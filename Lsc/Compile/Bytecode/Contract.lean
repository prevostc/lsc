import Lsc.Lang.AST
import Lsc.Lang.Checks
import Lsc.Compile.Lower
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.Encode
import Lsc.Selectors
import Lsc.Compile.IR.Opt.Pipeline
import EvmYul.Operations

namespace Lsc.Compile

open Lsc.Compile.IR
open Lsc.Compile.Bytecode
open EvmYul Operation
open Instr

/-- Build compile `Config` from a contract schema (sequential storage slots). -/
def configFromContract (c : ContractDef) (topic0 : Ident → Option Nat) : Config :=
  { storage := StorageLayout.fromList (c.storage.mapIdx fun i (n, _, _) => (n, i))
  , events := { topic0 := topic0 } }

namespace Bytecode.Contract

private def dispatchRevert : List Instr :=
  [.push 0, .push 0, .op REVERT]

/-- Load ABI selector from calldata word 0 (top 4 bytes). Leaves selector on stack. -/
private def loadSelector : List Instr := [
  .push 0,
  .op CALLDATALOAD,
  .push 0xE0,
  .op SHR
]

private def selectorDispatch (fns : List FunctionDef) (ctx : Ctx) : List Instr × Ctx :=
  let dispatchCtx : Ctx := { ctx with labelPrefix := "dispatch." }
  let (revLbl, ctx1) := Ctx.freshLabel dispatchCtx "revert"
  let calldataCheck : List Instr := [
    .push 4,
    .op CALLDATASIZE,
    .op LT,
    .pushLabel revLbl,
    .op JUMPI
  ]
  let branches := fns.foldl (init := ([] : List Instr)) fun acc fn =>
    acc ++ [
      .op DUP1,
      .push (computeSelector fn |>.toNat),
      .op EQ,
      .pushLabel fn.name,
      .op JUMPI
    ]
  let instrs := calldataCheck ++ loadSelector ++ branches ++ [
    .op POP,
    .pushLabel revLbl,
    .op JUMP,
    .jumpDest revLbl
  ] ++ dispatchRevert
  (instrs, ctx1)

/-- Decode each of `fn`'s ABI parameters from calldata (one 32-byte-aligned word per parameter,
starting right after the 4-byte selector — `uint256`/`bool`/`address`/`wei`/`wad` are all a
single word wide, see `Ty.abiStr`) onto the stack, `bindLocal`-ing each one under its declared
parameter name exactly as `codegenStmt`'s `.letBind` case already does for `let`-locals — so the
function body's `Expr.var paramName` references (lowered to `IR.Expr.local paramName` by
`Lower.lean`, unchanged) resolve via the ordinary `Ctx.lookupDepth`/`DUP` mechanism with zero
further special-casing. -/
private partial def emitParamLoadsGo :
    List (Ident × Ty) → Nat → List Instr × Ctx → List Instr × Ctx
  | [], _, acc => acc
  | (name, _ty) :: rest, i, (instrs, c) =>
    let offset := 4 + 32 * i
    let c1 := { c with stackDepth := c.stackDepth + 1 }
    let c2 := c1.bindLocal name
    emitParamLoadsGo rest (i + 1) (instrs ++ [.push offset, .op CALLDATALOAD], c2)

private def emitParamLoads (ctx : Ctx) (params : List (Ident × Ty)) : List Instr × Ctx :=
  emitParamLoadsGo params 0 ([], ctx)

private def emitFunctionBodies (cfg : Config) (fns : List FunctionDef) (ctx : Ctx) :
    Except String (List Instr × Ctx) :=
  fns.foldlM (init := ([], ctx)) fun (acc, ctx) fn => do
    let ir ← Lower.stmt cfg fn.body
    let fnCtx := Ctx.forFunction ctx fn.name
    let (paramInstrs, fnCtx') := emitParamLoads fnCtx fn.params
    let (body, ctx') ← Codegen.stmt fnCtx' (IR.Opt.optimizeStmt ir)
    let ctxOut := Ctx.afterFunction ctx'
    -- A `.view` function's body always ends in a `return e;` (`Checks.checkViewReturns`,
    -- enforced by `Checks.validateAll` before this ever runs), which `Codegen.lean`'s `.ret`
    -- case already lowers to a real `RETURN` — that halts execution on its own, so appending a
    -- trailing `STOP` after it would be genuinely unreachable, dead bytecode (harmless, but
    -- pointless). An `.external`/`tx` body, by contrast, never contains `.ret` at all (see
    -- `Lang/AST.lean`'s `Stmt.ret` docstring) and always needs the explicit `STOP` to halt.
    let haltInstrs : List Instr := if fn.kind == .view then [] else [.op STOP]
    .ok (acc ++ [.jumpDest fn.name] ++ paramInstrs ++ body ++ haltInstrs, ctxOut)

/-- Functions reachable via the shared ABI selector-dispatch jump table: both `.external`
(state-mutating) and `.view` (read-only) — see `Checks.checkSelectorCollisions`'s docstring for
why both kinds share one selector namespace. -/
private def dispatchedFunctions (c : ContractDef) : List FunctionDef :=
  c.functions.filter fun fn => fn.kind == .external || fn.kind == .view

def contract (cfg : Config) (c : ContractDef) : Except String (List Instr) := do
  let fns := dispatchedFunctions c
  if fns.isEmpty then
    .error "contract has no external functions"
  else do
    let (dispatch, ctx1) := selectorDispatch fns {}
    let (bodies, _) ← emitFunctionBodies cfg fns ctx1
    .ok (dispatch ++ bodies)

/-- Lower and codegen a constructor `Stmt` to a flat list of `Instr`.
    The caller `CALLER` opcode is the deployer address during construction. -/
def constructorInstrs (cfg : Config) (s : Lsc.Stmt) : Except String (List Instr) := do
  let ir ← Lower.stmt cfg s
  let (instrs, _) ← Codegen.stmt {} (IR.Opt.optimizeStmt ir)
  .ok instrs

/-- Number of bytes occupied by a `Instr.push n` (PUSH0 = 1 byte, PUSHk = 1+k bytes). -/
private def pushByteSize (n : Nat) : Nat :=
  if n == 0 then 1
  else
    -- pushWidth n = floor(log2(n)/8) + 1; total = 1 + pushWidth
    1 + (Nat.div (Nat.log2 n) 8 + 1)

/-- Build deploy bytecode: constructor bytes ++ CODECOPY/RETURN preamble ++ runtime bytes.
    The preamble copies the runtime portion into memory at offset 0 and returns it,
    which is the EVM deploy transaction contract-creation convention. -/
def deployCode (ctorBytes runtimeBytes : ByteArray) : ByteArray :=
  -- preamble layout (7 instructions):
  --   push rSize        -- CODECOPY length
  --   push rOffset      -- CODECOPY source offset in deploy code
  --   push 0            -- CODECOPY dest in memory
  --   CODECOPY
  --   push rSize        -- RETURN length
  --   push 0            -- RETURN offset in memory
  --   RETURN
  -- preamble byte size = pushByteSize(rSize) + pushByteSize(rOffset) + 1 + 1
  --                    + pushByteSize(rSize) + 1 + 1
  --                    = 4 + 2*pushByteSize(rSize) + pushByteSize(rOffset)
  -- rOffset = ctorBytes.size + preamble byte size
  -- Solve with small fixpoint (converges in ≤ 2 steps for any realistic contract):
  let rSize := runtimeBytes.size
  let base := ctorBytes.size + 4 + 2 * pushByteSize rSize
  -- Try pushByteSize(rOffset) = 1 (covers rOffset ≤ 255):
  let cand1 := base + pushByteSize (base + 1)
  -- If the guess was consistent, use cand1, else fall back to cand2 (covers ≤ 65535):
  let rOffset :=
    if pushByteSize cand1 == pushByteSize (base + 1) then cand1
    else base + pushByteSize (base + pushByteSize (base + 2))
  -- Emit preamble as raw bytes using the same PUSH encoding as Encode.lean.
  -- We replicate emitPush inline to avoid a private-function dependency.
  let pushWidth : Nat → Nat := fun n =>
    if n == 0 then 0 else Nat.div (Nat.log2 n) 8 + 1
  let natToBytes : Nat → Nat → ByteArray := fun n w =>
    ByteArray.mk ((List.range w).map fun i =>
      UInt8.ofNat ((n / (2 ^ (8 * (w - 1 - i)))) % 256)).toArray
  let emitPushRaw : Nat → ByteArray := fun n =>
    let w := pushWidth n
    -- PUSH0 = 0x5f, PUSH1 = 0x60, ..., PUSHk = 0x5f + k
    let opByte : UInt8 := UInt8.ofNat (0x5f + w)
    ByteArray.mk #[opByte] ++ natToBytes n w
  let preamble :=
    emitPushRaw rSize ++
    emitPushRaw rOffset ++
    emitPushRaw 0 ++
    ByteArray.mk #[0x39] ++  -- CODECOPY opcode
    emitPushRaw rSize ++
    emitPushRaw 0 ++
    ByteArray.mk #[0xf3]     -- RETURN opcode
  ctorBytes ++ preamble ++ runtimeBytes

end Bytecode.Contract

def contractToBytecode (c : ContractDef) (topic0 : Ident → Option Nat) : Except String ByteArray := do
  let c ← Checks.validateAll c
  let cfg := configFromContract c topic0
  let instrs ← Bytecode.Contract.contract cfg c
  encode instrs

def contractToBytecodeHex (c : ContractDef) (topic0 : Ident → Option Nat) : Except String String :=
  contractToBytecode c topic0 |>.map Bytecode.toHex

/-- Produce a full EVM **deploy transaction** payload.
    When `c.constructor = none` this is identical to `contractToBytecode`.
    When `c.constructor = some stmt` the constructor body runs first (setting
    storage, e.g. `owner = CALLER`), then the runtime bytecode is returned via
    the standard CODECOPY + RETURN pattern. -/
def deployToBytecode (c : ContractDef) (topic0 : Ident → Option Nat) : Except String ByteArray := do
  let c ← Checks.validateAll c
  let cfg := configFromContract c topic0
  let runtimeInstrs ← Bytecode.Contract.contract cfg c
  let runtimeBytes ← encode runtimeInstrs
  match c.constructor with
  | none => .ok runtimeBytes
  | some ctorStmt =>
    let cInstrs ← Bytecode.Contract.constructorInstrs cfg ctorStmt
    let ctorBytes ← encode cInstrs
    .ok (Bytecode.Contract.deployCode ctorBytes runtimeBytes)

def deployToBytecodeHex (c : ContractDef) (topic0 : Ident → Option Nat) : Except String String :=
  deployToBytecode c topic0 |>.map Bytecode.toHex

end Lsc.Compile
