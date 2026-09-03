import Lsc.Lib.Wei.Syntax
import Lsc.Lib.Fixed.Optimize

namespace Lsc.Wei

open Lsc.Compile.IR (Expr Stmt)

def lowerExpr (fieldSlot : Ident → Option Nat) (e : Expr) : Except String Compile.IR.Expr :=
  Fixed.lowerExpr fieldSlot (fun _ => none) e

def lowerAddCheckedNatStorage := Fixed.lowerAddCheckedNatStorage
def lowerAddCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot : Ident → Option Nat)
    (overflowSelector : Nat) : Except String Stmt :=
  Fixed.lowerAddCheckedStorage slot rhs fieldSlot (fun _ => none) overflowSelector

def lowerSubCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot : Ident → Option Nat)
    (underflowSelector : Nat) : Except String Stmt :=
  Fixed.lowerSubCheckedStorage slot rhs fieldSlot (fun _ => none) underflowSelector

def lowerLetBind (fieldSlot : Ident → Option Nat) (name : Ident) (e : Expr)
    (overflowSelector : Nat) : Except String Compile.IR.Stmt :=
  Fixed.lowerLetBind fieldSlot (fun _ => none) name e overflowSelector

def incrementLetIR (overflowSelector : Nat) : Stmt :=
  let old := "lsc_n_old"
  .seq
    (.letBind old (.sload 0))
    (.seq
      (.letBind "n" (.add (.local old) (.lit 1)))
      (.seq
        (.ifRevertSelector (.lt (.local "n") (.local old)) overflowSelector)
        .skip))

private def counterNumberSlot (field : Ident) : Option Nat :=
  if field == "number" then some 0 else none

theorem lower_addCheckedNatStorage_shape (overflowSelector : Nat) :
    lowerLetBind counterNumberSlot "n" (addCheckedNatStorage "number" 1) overflowSelector =
      .ok (incrementLetIR overflowSelector) := rfl

end Lsc.Wei
