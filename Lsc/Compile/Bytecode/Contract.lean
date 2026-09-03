import Lsc.Lang.AST
import Lsc.Lang.Checks
import Lsc.Compile.Lower
import Lsc.Compile.Abi
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.Encode
import Lsc.Selectors
import Lsc.Compile.IR.Opt.Pipeline
import EvmYul.Operations

namespace Lsc.Compile

open Lsc.Compile.IR
open Lsc.Compile.Bytecode
open Lsc.Compile.Abi
open EvmYul Operation
open Instr

/-- Build compile `Config` from a contract schema (sequential storage slots). -/
def configFromContract (c : ContractDef) (topic0 : Ident → Option Nat) : Config :=
  let storage :=
    if !c.layoutScalars.isEmpty || !c.layoutMaps.isEmpty then
      { slots := c.layoutScalars, mapSlots := c.layoutMaps }
    else StorageLayout.fromList (c.storage.mapIdx fun i (n, _, _) => (n, i))
  let errorSelector name :=
    (c.errors.find? (·.1 == name)).map fun (n, ps) =>
      (computeErrorSelector n ps).toNat
  { storage := storage
  , events := { topic0 := topic0 }
  , errors := { errorSelector := errorSelector } }

namespace Bytecode.Contract

/- `.view` codegen intentionally consumes the exact lowered IR.  Besides keeping review output
faithful to lowering, this lets view-correctness proofs use the lowering/building invariants
directly, without transporting syntactic reload plans through the optimizer.  Transactional
functions retain the optimizer pipeline. -/
def codegenInput (fn : FunctionDef) (ir : IR.Stmt) : IR.Stmt :=
  if fn.kind == .view then ir else IR.Opt.optimizeStmt ir

def dispatchRevert (cfg : Config) : List Instr :=
  match cfg.errors.errorSelector "InvalidSelector" with
  | some sel =>
    [ .push (paddedSelector sel)
    , .push 0
    , .op MSTORE
    , .push 4
    , .push 0
    , .op REVERT ]
  | none => [.push 0, .push 0, .op REVERT]

/-- Load ABI selector from calldata word 0 (top 4 bytes). Leaves selector on stack. -/
def loadSelector : List Instr := [
  .push 0,
  .op CALLDATALOAD,
  .push 0xE0,
  .op SHR
]

def selectorRevertLabel (ctx : Ctx) : String :=
  (Ctx.freshLabel { ctx with labelPrefix := "dispatch." } "revert").1

/-- Generate independent selector tests. Each test reloads the selector, so both a failed test and
a successful jump leave the operand stack empty. -/
def selectorBranches : List FunctionDef → List Instr
  | [] => []
  | fn :: rest =>
      loadSelector ++ [
        .push (computeSelector fn |>.toNat),
        .op EQ,
        .pushLabel fn.name,
        .op JUMPI
      ] ++ selectorBranches rest

def selectorDispatch (cfg : Config) (fns : List FunctionDef) (ctx : Ctx) : List Instr × Ctx :=
  let dispatchCtx : Ctx := { ctx with labelPrefix := "dispatch." }
  let (revLbl, ctx1) := Ctx.freshLabel dispatchCtx "revert"
  let calldataCheck : List Instr := [
    .push 4,
    .op CALLDATASIZE,
    .op LT,
    .pushLabel revLbl,
    .op JUMPI
  ]
  let instrs := calldataCheck ++ selectorBranches fns ++ [
    .pushLabel revLbl,
    .op JUMP,
    .jumpDest revLbl
  ] ++ dispatchRevert cfg
  (instrs, ctx1)

def emitFunctionBody (cfg : Config) (accCtx : List Instr × Ctx) (fn : FunctionDef) :
    Except String (List Instr × Ctx) := do
    let (acc, ctx) := accCtx
    let ir ← Lower.function cfg fn
    let fnCtx := Ctx.forFunction ctx fn.name
    let (body, ctx') ← Codegen.stmt fnCtx (codegenInput fn ir)
    let ctxOut := Ctx.afterFunction ctx'
    -- A `.view` function's body always ends in a `return e;` (`Checks.checkViewReturns`,
    -- enforced by `Checks.validateAll` before this ever runs), which `Codegen.lean`'s `.ret`
    -- case already lowers to a real `RETURN` — that halts execution on its own, so appending a
    -- trailing `STOP` after it would be genuinely unreachable, dead bytecode (harmless, but
    -- pointless). An `.external`/`tx` body, by contrast, never contains `.ret` at all (see
    -- `Lang/AST.lean`'s `Stmt.ret` docstring) and always needs the explicit `STOP` to halt.
    let haltInstrs : List Instr := if fn.kind == .view then [] else [.op STOP]
    .ok (acc ++ [.jumpDest fn.name] ++ body ++ haltInstrs, ctxOut)

def emitFunctionBodies (cfg : Config) (fns : List FunctionDef) (ctx : Ctx) :
    Except String (List Instr × Ctx) :=
  fns.foldlM (init := ([], ctx)) (emitFunctionBody cfg)

/-- Lower and codegen a single function body (including ABI parameter `letBind`s). -/
def functionInstrs (cfg : Config) (fn : FunctionDef) (baseOffset : Nat := 4) :
    Except String (List Instr) := do
  let ir ← Lower.function cfg fn baseOffset
  let fnCtx := Ctx.forFunction {} fn.name
  let (body, _) ← Codegen.stmt fnCtx (codegenInput fn ir)
  .ok body

/-- Functions reachable via the shared ABI selector-dispatch jump table: both `.external`
(state-mutating) and `.view` (read-only) — see `Checks.checkSelectorCollisions`'s docstring for
why both kinds share one selector namespace. -/
def dispatchedFunctions (c : ContractDef) : List FunctionDef :=
  c.functions.filter fun fn => fn.kind == .external || fn.kind == .view

def contract (cfg : Config) (c : ContractDef) : Except String (List Instr) := do
  let fns := dispatchedFunctions c
  if fns.isEmpty then
    .error "contract has no external functions"
  else do
    let (dispatch, ctx1) := selectorDispatch cfg fns {}
    let (bodies, _) ← emitFunctionBodies cfg fns ctx1
    .ok (dispatch ++ bodies)

/-- Lower and codegen a constructor `FunctionDef` to a flat list of `Instr`.
    Deploy calldata params are loaded from word offset 0 (no selector). The `CALLER` opcode
    is the deployer address during construction. -/
def constructorInstrs (cfg : Config) (fn : FunctionDef) : Except String (List Instr) := do
  functionInstrs cfg fn 0

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
    When `c.deployFn = none` this is identical to `contractToBytecode`.
    When `c.deployFn = some fn` the deploy initializer runs first (setting storage from deploy
    calldata and/or `CALLER`), then the runtime bytecode is returned via CODECOPY + RETURN. -/
def deployToBytecode (c : ContractDef) (topic0 : Ident → Option Nat) : Except String ByteArray := do
  let c ← Checks.validateAll c
  let cfg := configFromContract c topic0
  let runtimeInstrs ← Bytecode.Contract.contract cfg c
  let runtimeBytes ← encode runtimeInstrs
  match c.deployFn with
  | none => .ok runtimeBytes
  | some ctorFn =>
    let cInstrs ← Bytecode.Contract.constructorInstrs cfg ctorFn
    let ctorBytes ← encode cInstrs
    .ok (Bytecode.Contract.deployCode ctorBytes runtimeBytes)

def deployToBytecodeHex (c : ContractDef) (topic0 : Ident → Option Nat) : Except String String :=
  deployToBytecode c topic0 |>.map Bytecode.toHex

end Lsc.Compile
