import Lsc.Lib.Wad.Syntax
import Lsc.Compile.IR

namespace Lsc.Wad

open Lsc.Compile.IR (Expr Stmt)

partial def lowerExpr (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr) : Except String Compile.IR.Expr :=
  match e with
  | .lit n => .ok (Compile.IR.Expr.lit n)
  | .var name => .ok (Compile.IR.Expr.local name)
  | .storageGet field =>
    match fieldSlot field with
    | some s => .ok (Compile.IR.Expr.sload s)
    | none => .error s!"unknown storage field {field}"
  | .mapGet field key => do
    match mapFieldSlot field with
    | none => .error s!"unknown mapping field {field}"
    | some base =>
      let keyIr ← match key with
        | .caller => .ok (Compile.IR.Expr.local "caller")
        | .var name => .ok (Compile.IR.Expr.local name)
      .ok (Compile.IR.Expr.dynSload (Compile.IR.Expr.mapSlot base keyIr))
  | .addChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    .ok (Compile.IR.Expr.add a' b')
  | .addCheckedNat e n => do
    let e' ← lowerExpr fieldSlot mapFieldSlot e
    .ok (Compile.IR.Expr.add e' (Compile.IR.Expr.lit n))
  | .subChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    .ok (Compile.IR.Expr.sub a' b')
  | .mulHalfUpChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let product := Compile.IR.Expr.mul a' b'
    let rounded := Compile.IR.Expr.add product (Compile.IR.Expr.lit (WAD / 2))
    .ok (Compile.IR.Expr.div rounded (Compile.IR.Expr.lit WAD))
  | .divDownChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let scaledNumer := Compile.IR.Expr.mul a' (Compile.IR.Expr.lit WAD)
    .ok (Compile.IR.Expr.div scaledNumer b')

/-- Lower `σ.field +=? n` (literal increment) with an on-chain overflow guard. -/
def lowerAddCheckedNatStorage (slot : Nat) (n : Nat) (overflowSelector : Nat) : Stmt :=
  let old := "lsc_add_old"
  let new := "lsc_add_new"
  .seq
    (.letBind old (.sload slot))
    (.seq
      (.letBind new (.add (.local old) (.lit n)))
      (.seq
        (.ifRevertSelector (.lt (.local new) (.local old)) overflowSelector)
        (.sstore slot (.local new))))

/-- Lower `σ.field +=? rhs` with an on-chain overflow guard. -/
def lowerAddCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot mapFieldSlot : Ident → Option Nat)
    (overflowSelector : Nat) : Except String Stmt := do
  let rhsIr ← lowerExpr fieldSlot mapFieldSlot rhs
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

/-- Lower `σ.field -=? rhs` with an on-chain underflow guard. -/
def lowerSubCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot mapFieldSlot : Ident → Option Nat)
    (underflowSelector : Nat) : Except String Stmt := do
  let rhsIr ← lowerExpr fieldSlot mapFieldSlot rhs
  let old := "lsc_sub_old"
  .ok <|
    .seq
      (.letBind old (.sload slot))
      (.seq
        (.ifRevertSelector (.lt (.local old) rhsIr) underflowSelector)
        (.sstore slot (.sub (.local old) rhsIr)))

end Lsc.Wad
