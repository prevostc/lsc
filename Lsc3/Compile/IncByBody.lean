import Lsc3.Examples.Counter
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode
import Lsc3.Compile.Contract

/-!
# Codegen of `incrementBy` (calldata argument + require + checked add)

`loadParams 1`, `require n ≠ 0` (Error.Zero), load slot 0, checked-add `n`,
store, emit `Incremented(n)`, STOP. Jump labels are those of
`Ctx.forFunction {} "incrementBy" 1`.
-/

namespace Lsc3.Compile.IncByBody

open Lsc3 Lsc3.Compile Lsc3.Compile.Codegen Counter

def incByFn : FnDef where
  name := "incrementBy"
  decl := .anonymous
  kind := .tx
  params := [{ name := "n", ty := .uint256 }]
  ret := .unit
  core := .seq (.require (.ne (.var 0) (.lit 0)) 0 [])
    (.letOp (.load 0)
      (.letOp (.addChecked (.var 0) (.var 1))
        (.seq (.store 0 (.var 0))
          (.stmtTail (.emit 0 [.var 2])))))

theorem incByFn_core :
    incByFn.core =
      Core.seq (.require (.ne (.var 0) (.lit 0)) 0 [])
        (Core.letOp (.load 0)
          (Core.letOp (.addChecked (.var 0) (.var 1))
            (Core.seq (.store 0 (.var 0))
              (Core.stmtTail (.emit 0 [.var 2]))))) :=
  rfl

def reqR : String := "incrementBy.reqR0"
def reqO : String := "incrementBy.reqO1"
def addR : String := "incrementBy.addR2"
def addO : String := "incrementBy.addO3"

def zeroSel : Nat :=
  if h : 0 < contract.errors.length then ErrorDef.selector contract.errors[0] else 0

def incTopic : Nat :=
  if h : 0 < contract.events.length then EventDef.topic0 contract.events[0] else 0

def loadParamInstrs : List Asm :=
  [Asm.push 4, Asm.op .CALLDATALOAD, Asm.push localBase, Asm.op .MSTORE]

def requireInstrs : List Asm :=
  [Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .EQ, Asm.op .ISZERO,
   Asm.op .ISZERO, Asm.jumpi reqR, Asm.jump reqO, Asm.jumpDest reqR] ++
  emitRevert zeroSel ++
  [Asm.jumpDest reqO]

def prefixInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD]

def checkedAddInstrs : List Asm :=
  [dup2, Asm.op .ADD, dup1, swap2, Asm.op .GT,
   Asm.jumpi addR, Asm.jump addO, Asm.jumpDest addR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest addO]

def tailInstrs : List Asm :=
  [Asm.push (localBase + 64), Asm.op .MSTORE,
   Asm.push (localBase + 64), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

def incByInstrs : List Asm :=
  loadParamInstrs ++ requireInstrs ++ prefixInstrs ++ checkedAddInstrs ++ tailInstrs

set_option maxRecDepth 20000 in
theorem incrementBy_genFunction :
    genFunction contract incByFn {} =
      .ok (incByInstrs, { depth := 0, labelCounter := 4, labelPrefix := "" }) :=
  rfl

def reqRPc : Nat := 21
def reqOPc : Nat := 61
def addRPc : Nat := 86
def addOPc : Nat := 131

set_option maxRecDepth 20000 in
theorem labels_incBy :
    layoutLabels incByInstrs =
      [(addO, addOPc), (addR, addRPc), (reqO, reqOPc), (reqR, reqRPc)] :=
  rfl

end Lsc3.Compile.IncByBody
