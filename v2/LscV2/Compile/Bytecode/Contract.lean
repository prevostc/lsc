import LscV2.Lang.AST
import LscV2.Compile.Lower
import LscV2.Compile.Bytecode.Codegen
import LscV2.Compile.Bytecode.Encode
import LscV2.Selectors
import LscV2.Compile.IR.Opt.Pipeline
import EvmYul.Operations

namespace LscV2.Compile

open LscV2.Compile.IR
open LscV2.Compile.Bytecode
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

private def emitFunctionBodies (cfg : Config) (fns : List FunctionDef) (ctx : Ctx) :
    Except String (List Instr × Ctx) :=
  fns.foldlM (init := ([], ctx)) fun (acc, ctx) fn => do
    let ir ← Lower.stmt cfg fn.body
    let fnCtx := Ctx.forFunction ctx fn.name
    let (body, ctx') ← Codegen.stmt fnCtx (IR.Opt.optimizeStmt ir)
    let ctxOut := Ctx.afterFunction ctx'
    .ok (acc ++ [.jumpDest fn.name] ++ body ++ [.op STOP], ctxOut)

private def externalFunctions (c : ContractDef) : List FunctionDef :=
  c.functions.filter fun fn => fn.kind == .external

def contract (cfg : Config) (c : ContractDef) : Except String (List Instr) := do
  let fns := externalFunctions c
  if fns.isEmpty then
    .error "contract has no external functions"
  else do
    let (dispatch, ctx1) := selectorDispatch fns {}
    let (bodies, _) ← emitFunctionBodies cfg fns ctx1
    .ok (dispatch ++ bodies)

/-- Lower and codegen a constructor `Stmt` to a flat list of `Instr`.
    The caller `CALLER` opcode is the deployer address during construction. -/
def constructorInstrs (cfg : Config) (s : LscV2.Stmt) : Except String (List Instr) := do
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

end LscV2.Compile
