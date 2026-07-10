import Lsc.Lib.Wei.Syntax
import Lsc.Compile.IR

namespace Lsc.Wei

open Lsc.Compile.IR (Expr Stmt)

partial def lowerExpr (fieldSlot : Ident → Option Nat) (e : Expr) : Except String Compile.IR.Expr :=
  match e with
  | .lit n => .ok (Compile.IR.Expr.lit n)
  | .var name => .ok (Compile.IR.Expr.local name)
  | .storageGet field =>
    match fieldSlot field with
    | some s => .ok (Compile.IR.Expr.sload s)
    | none => .error s!"unknown storage field {field}"
  | .addChecked a b => do
    let a' ← lowerExpr fieldSlot a
    let b' ← lowerExpr fieldSlot b
    .ok (Compile.IR.Expr.add a' b')
  | .addCheckedNat e n => do
    let e' ← lowerExpr fieldSlot e
    .ok (Compile.IR.Expr.add e' (Compile.IR.Expr.lit n))
  | .subChecked a b => do
    let a' ← lowerExpr fieldSlot a
    let b' ← lowerExpr fieldSlot b
    .ok (Compile.IR.Expr.sub a' b')

def lowerAddCheckedNatStorage (slot : Nat) (n : Nat) (bind : Ident) (overflowSelector : Nat)
    (rest : Stmt) : Stmt :=
  let old := s!"lsc_{bind}_old"
  .seq
    (.letBind old (.sload slot))
    (.seq
      (.letBind bind (.add (.local old) (.lit n)))
      (.seq
        (.ifRevertSelector (.lt (.local bind) (.local old)) overflowSelector)
        rest))

def lowerAddCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot : Ident → Option Nat)
    (overflowSelector : Nat) : Except String Stmt := do
  let rhsIr ← lowerExpr fieldSlot rhs
  let old := "lsc_add_old"
  let new := "lsc_add_new"
  .ok <|
    .seq
      (.letBind old (.sload slot))
      (.seq
        (.letBind new (.add (.local old) rhsIr))
        (.seq
          (.ifRevertSelector (.lt (.local new) (.local old)) overflowSelector)
          (.sstore slot (.local new))))

def lowerSubCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot : Ident → Option Nat)
    (underflowSelector : Nat) : Except String Stmt := do
  let rhsIr ← lowerExpr fieldSlot rhs
  let old := "lsc_sub_old"
  .ok <|
    .seq
      (.letBind old (.sload slot))
      (.seq
        (.ifRevertSelector (.lt (.local old) rhsIr) underflowSelector)
        (.sstore slot (.sub (.local old) rhsIr)))

def lowerLetBind (fieldSlot : Ident → Option Nat) (name : Ident) (e : Expr)
    (overflowSelector : Nat) : Except String Compile.IR.Stmt :=
  match e with
  | .addCheckedNat (.storageGet field) n =>
    match fieldSlot field with
    | some slot =>
      .ok (lowerAddCheckedNatStorage slot n name overflowSelector Compile.IR.Stmt.skip)
    | none => .error s!"unknown storage field {field}"
  | e' => do
    let ir ← lowerExpr fieldSlot e'
    .ok (Compile.IR.Stmt.letBind name ir)

/-- Expected IR for `let n ← $.number +? 1` at slot 0 (overflow selector placeholder `0`). -/
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
