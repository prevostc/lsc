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
  loadSelector ++ [Asm.push4 (FnDef.selector fn), Asm.op .EQ, Asm.jumpi fn.name]

def selectorBranches : List FnDef → List Asm
  | [] => []
  | fn :: rest => selectorBranch fn ++ selectorBranches rest

def dispatchRevert (sel : Nat) : List Asm :=
  emitRevert sel

def selectorDispatch (c : ContractDef) (ctx : Ctx) : Except String (List Asm × Ctx) :=
  let fns := c.functions
  match fns with
  | [] => .error "contract has no functions"
  | _ =>
    let (revLbl, ctx1) := Ctx.freshLabel ctx "dispR"
    let calldataCheck : List Asm :=
      [Asm.push 4, Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl]
    let branches := selectorBranches fns
    let tail : List Asm :=
      [Asm.jump revLbl, Asm.jumpDest revLbl] ++
        dispatchRevert (selectorOf "InvalidSelector" [])
    .ok (calldataCheck ++ branches ++ tail, ctx1)

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

def compileDeploy (c : ContractDef) : Except String (List UInt8) := do
  let runtime ← compileContract c
  pure (deployCode runtime)

/-! ## Dispatcher byte sizes

Selector immediates are always `PUSH4` and the invalid-selector revert is always `PUSH32`,
so these sizes do not depend on Keccak. The first function `JUMPDEST` is at
`dispatchByteSize n`. -/

def calldataCheckByteSize : Nat := 8
def selectorBranchByteSize : Nat := 15
def dispatchTailByteSize : Nat := 44
def dispatchByteSize (nFns : Nat) : Nat :=
  calldataCheckByteSize + selectorBranchByteSize * nFns + dispatchTailByteSize

theorem dispatchByteSize_one : dispatchByteSize 1 = 67 := rfl
theorem dispatchByteSize_two : dispatchByteSize 2 = 82 := rfl
theorem dispatchByteSize_four : dispatchByteSize 4 = 112 := rfl

theorem asmListSize_loadSelector : asmListSize loadSelector = 5 := rfl

theorem asmListSize_selectorBranch (fn : FnDef) :
    asmListSize (selectorBranch fn) = selectorBranchByteSize := rfl

theorem asmListSize_selectorBranches (fns : List FnDef) :
    asmListSize (selectorBranches fns) = selectorBranchByteSize * fns.length := by
  induction fns with
  | nil =>
    rfl
  | cons fn rest ih =>
    rw [selectorBranches, asmListSize_append, asmListSize_selectorBranch, ih, List.length_cons]
    simp [selectorBranchByteSize]
    omega

theorem asmListSize_calldataCheck (revLbl : String) :
    asmListSize [Asm.push 4, Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl] =
      calldataCheckByteSize :=
  rfl

theorem asmListSize_dispatchRevert (sel : Nat) :
    asmListSize (dispatchRevert sel) = 39 := rfl

theorem asmListSize_emitRevert (sel : Nat) :
    asmListSize (emitRevert sel) = 39 :=
  asmListSize_dispatchRevert sel

theorem asmListSize_dispatchTail (revLbl : String) (sel : Nat) :
    asmListSize ([Asm.jump revLbl, Asm.jumpDest revLbl] ++ dispatchRevert sel) =
      dispatchTailByteSize :=
  rfl

theorem selectorDispatch_size {c : ContractDef} {ctx : Ctx} (hne : c.functions ≠ []) :
    match selectorDispatch c ctx with
    | .ok (instrs, _) => asmListSize instrs = dispatchByteSize c.functions.length
    | .error _ => False := by
  unfold selectorDispatch
  match hfn : c.functions with
  | [] => exact (hne hfn).elim
  | _fn :: _rest =>
    simp [Ctx.freshLabel, asmListSize_append, asmListSize_selectorBranches,
      asmListSize_dispatchRevert, dispatchByteSize, calldataCheckByteSize, dispatchTailByteSize]
    omega

end Lsc3.Compile
