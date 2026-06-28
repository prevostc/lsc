import LscV2.Lang.AST
import LscV2.Compile.Lower
import LscV2.Compile.Bytecode.Codegen
import LscV2.Compile.Bytecode.Encode
import LscV2.Selectors
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
    let (body, ctx') ← Codegen.stmt fnCtx ir
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

end Bytecode.Contract

def contractToBytecode (c : ContractDef) (topic0 : Ident → Option Nat) : Except String ByteArray := do
  let cfg := configFromContract c topic0
  let instrs ← Bytecode.Contract.contract cfg c
  encode instrs

def contractToBytecodeHex (c : ContractDef) (topic0 : Ident → Option Nat) : Except String String :=
  contractToBytecode c topic0 |>.map Bytecode.toHex

end LscV2.Compile
