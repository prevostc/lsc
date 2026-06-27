import LscV2.Lib.Wei.Expr
import LscV2.Compile.IR

namespace LscV2.Wei.Lower

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

partial def lowerExpr (fieldSlot : Ident → Option Nat) (e : Wei.Expr) : Except String Compile.IR.Expr :=
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

def lowerLetBind (fieldSlot : Ident → Option Nat) (name : Ident) (e : Wei.Expr) : Except String Compile.IR.Stmt :=
  match e with
  | .addCheckedNat (.storageGet field) n =>
    match fieldSlot field with
    | some slot =>
      .ok (lowerAddCheckedNatStorage slot n name Compile.IR.Stmt.skip)
    | none => .error s!"unknown storage field {field}"
  | e' => do
    let ir ← lowerExpr fieldSlot e'
    .ok (Compile.IR.Stmt.letBind name ir)

end LscV2.Wei.Lower
