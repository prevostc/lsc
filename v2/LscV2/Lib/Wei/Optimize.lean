import LscV2.Lib.Wei.Syntax
import LscV2.Compile.IR

namespace LscV2.Wei

open LscV2.Compile.IR (Expr Stmt)

def lowerAddCheckedNatStorage (slot : Nat) (n : Nat) (bind : Ident) (rest : Stmt) : Stmt :=
  let old := s!"lsc_{bind}_old"
  .seq
    (.letBind old (.sload slot))
    (.seq
      (.letBind bind (.add (.local old) (.lit n)))
      (.seq
        (.ifRevert (.lt (.local bind) (.local old)))
        rest))

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
    .ok (Compile.IR.Expr.lt a' b')

def lowerLetBind (fieldSlot : Ident → Option Nat) (name : Ident) (e : Expr) : Except String Compile.IR.Stmt :=
  match e with
  | .addCheckedNat (.storageGet field) n =>
    match fieldSlot field with
    | some slot =>
      .ok (lowerAddCheckedNatStorage slot n name Compile.IR.Stmt.skip)
    | none => .error s!"unknown storage field {field}"
  | e' => do
    let ir ← lowerExpr fieldSlot e'
    .ok (Compile.IR.Stmt.letBind name ir)

/-- Expected IR for `let n ← $.number +? 1` at slot 0. -/
def incrementLetIR : Stmt :=
  let old := "lsc_n_old"
  .seq
    (.letBind old (.sload 0))
    (.seq
      (.letBind "n" (.add (.local old) (.lit 1)))
      (.seq
        (.ifRevert (.lt (.local "n") (.local old)))
        .skip))

private def counterNumberSlot (field : Ident) : Option Nat :=
  if field == "number" then some 0 else none

theorem lower_addCheckedNatStorage_shape :
    lowerLetBind counterNumberSlot "n" (addCheckedNatStorage "number" 1) =
      .ok incrementLetIR := rfl

end LscV2.Wei
