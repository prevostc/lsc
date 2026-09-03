import Lsc3.Contract
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode

/-!
# LSC v3 — contract bytecode assembly (dispatcher + function bodies)
-/

namespace Lsc3.Compile

open Lsc3.EVM (Opcode)
open Codegen

def loadSelector : List Asm :=
  [Asm.push 0, Asm.op .CALLDATALOAD, Asm.push 0xE0, Asm.op .SHR]

def selectorBranch (fn : FnDef) : List Asm :=
  loadSelector ++ [Asm.push (FnDef.selector fn), Asm.op .EQ, Asm.jumpi fn.name]

def selectorBranches : List FnDef → List Asm
  | [] => []
  | fn :: rest => selectorBranch fn ++ selectorBranches rest

def dispatchRevert (sel : Nat) : List Asm :=
  emitRevert sel

def selectorDispatch (c : ContractDef) (ctx : Ctx) : Except String (List Asm × Ctx) := do
  let fns := c.functions
  if fns.isEmpty then
    throw "contract has no functions"
  let (revLbl, ctx1) := Ctx.freshLabel ctx "dispR"
  let calldataCheck : List Asm := [Asm.push 4, Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl]
  let branches := selectorBranches fns
  let tail : List Asm := [Asm.jump revLbl, Asm.jumpDest revLbl] ++ dispatchRevert (selectorOf "InvalidSelector" [])
  pure (calldataCheck ++ branches ++ tail, ctx1)

def emitFunction (c : ContractDef) (acc : List Asm × Ctx) (fn : FnDef) :
    Except String (List Asm × Ctx) := do
  let (accInstr, ctx) := acc
  let (body, ctx') ← genFunction c fn ctx
  pure (accInstr ++ [Asm.jumpDest fn.name] ++ body, ctx')

def contractInstrs (c : ContractDef) : Except String (List Asm) := do
  let (dispatch, ctx1) ← selectorDispatch c {}
  let (bodies, _) ← c.functions.foldlM (emitFunction c) (dispatch, ctx1)
  pure bodies

def compileContract (c : ContractDef) : Except String (List UInt8) := do
  let instrs ← contractInstrs c
  encode instrs

end Lsc3.Compile
