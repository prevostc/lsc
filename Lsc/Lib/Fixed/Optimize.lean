import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Fixed.IRExpand
import Lsc.Compile.IR

namespace Lsc.Fixed

open Lsc.Compile.IR (Expr Stmt)
open Lsc.Compile.IR.Builder

def scaleIr (mode : ScaleMode) : Compile.IR.Expr :=
  match mode with
  | .static d => Compile.IR.Expr.lit (10 ^ d)
  | .runtime factor => Compile.IR.Expr.lit factor

def lowerExpr (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr) :
    Except String Compile.IR.Expr :=
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
  | .mapGet2 field key1 key2 => do
    match mapFieldSlot field with
    | none => .error s!"unknown mapping field {field}"
    | some base =>
      let key1Ir ← match key1 with
        | .caller => .ok (Compile.IR.Expr.local "caller")
        | .var name => .ok (Compile.IR.Expr.local name)
      let key2Ir ← match key2 with
        | .caller => .ok (Compile.IR.Expr.local "caller")
        | .var name => .ok (Compile.IR.Expr.local name)
      .ok (Compile.IR.Expr.dynSload (Compile.IR.Expr.mapSlot2 base key1Ir key2Ir))
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
  | .mulHalfUpChecked scale a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let s := scaleIr scale
    let product := Compile.IR.Expr.mul a' b'
    let half := Compile.IR.Expr.div s (Compile.IR.Expr.lit 2)
    let rounded := Compile.IR.Expr.add product half
    .ok (Compile.IR.Expr.div rounded s)
  | .divDownChecked scale a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let s := scaleIr scale
    let scaledNumer := Compile.IR.Expr.mul a' s
    .ok (Compile.IR.Expr.div scaledNumer b')
  | .sqrtDownChecked scale a => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    .ok (IRExpand.expandSqrtDown scale.scaleNat a')
  | .min a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    .ok (IRExpand.expandMin a' b')

/-- Whether an expression needs statement-level sharing during lowering. -/
def containsSqrtDown : Expr → Bool
  | .sqrtDownChecked _ _ => true
  | .addChecked a b
  | .subChecked a b
  | .mulHalfUpChecked _ a b
  | .divDownChecked _ a b
  | .min a b => containsSqrtDown a || containsSqrtDown b
  | .addCheckedNat e _ => containsSqrtDown e
  | .lit _ | .var _ | .storageGet _ | .mapGet _ _ | .mapGet2 _ _ _ => false

/-- User locals read by a fixed expression. Generated sqrt names are chosen outside this set,
    so they cannot shadow parameters or prior user bindings that affect the return value. -/
def localNames : Expr → List Ident
  | .var name => [name]
  | .mapGet _ .caller => ["caller"]
  | .mapGet _ (.var name) => [name]
  | .mapGet2 _ key1 key2 =>
      let ofKey : MapKey → List Ident
        | .caller => ["caller"]
        | .var name => [name]
      ofKey key1 ++ ofKey key2
  | .addChecked a b
  | .subChecked a b
  | .mulHalfUpChecked _ a b
  | .divDownChecked _ a b
  | .min a b => localNames a ++ localNames b
  | .addCheckedNat e _ | .sqrtDownChecked _ e => localNames e
  | .lit _ | .storageGet _ => []

/-- Lower an expression while introducing bindings only along sqrt-containing paths. This keeps
    ordinary arithmetic and branchless `min` shallow, while every magnitude/Newton intermediate
    is shared exactly once. -/
def lowerExprLinear (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr)
    (build : Build) : Except String (Build × Compile.IR.Expr) := do
  if !containsSqrtDown e then
    return (build, ← lowerExpr fieldSlot mapFieldSlot e)
  match e with
  | .addChecked a b =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let (build, b') ← lowerExprLinear fieldSlot mapFieldSlot b build
      return (build, .add a' b')
  | .addCheckedNat e n =>
      let (build, e') ← lowerExprLinear fieldSlot mapFieldSlot e build
      return (build, .add e' (.lit n))
  | .subChecked a b =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let (build, b') ← lowerExprLinear fieldSlot mapFieldSlot b build
      return (build, .sub a' b')
  | .mulHalfUpChecked scale a b =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let (build, b') ← lowerExprLinear fieldSlot mapFieldSlot b build
      let s := scaleIr scale
      return (build, .div (.add (.mul a' b') (.div s (.lit 2))) s)
  | .divDownChecked scale a b =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let (build, b') ← lowerExprLinear fieldSlot mapFieldSlot b build
      return (build, .div (.mul a' (scaleIr scale)) b')
  | .sqrtDownChecked scale a =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let scaled := if scale.scaleNat == 1 then a' else .mul a' (.lit scale.scaleNat)
      return IRExpand.sqrtBinds scaled build
  | .min a b =>
      let (build, a') ← lowerExprLinear fieldSlot mapFieldSlot a build
      let (build, b') ← lowerExprLinear fieldSlot mapFieldSlot b build
      return (build, IRExpand.expandMin a' b')
  | _ =>
      return (build, ← lowerExpr fieldSlot mapFieldSlot e)

/-- Lower a Wad/Wei return expression, using a linear let-chain exactly when it contains sqrt. -/
def lowerRetStmt (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr) :
    Except String Compile.IR.Stmt := do
  if containsSqrtDown e then
    let fresh : Fresh := { used := localNames e }
    let (build, result) ← lowerExprLinear fieldSlot mapFieldSlot e { fresh }
    .ok (build.finish (.ret result))
  else
    .ok (.ret (← lowerExpr fieldSlot mapFieldSlot e))

/-- Constructor-level equation for the production WAD `sqrtProduct` shape.  Deliberately stops at
`IRExpand.sqrtBinds`, so transparent lowering proofs never reduce the shared sqrt program. -/
theorem lowerRetStmt_sqrtProduct (fieldSlot mapFieldSlot : Ident → Option Nat) (a b : Ident) :
    lowerRetStmt fieldSlot mapFieldSlot
        (.sqrtDownChecked (.static 18)
          (.mulHalfUpChecked (.static 18) (.var a) (.var b))) =
      let scale : Nat := 10 ^ 18
      let rounded : Compile.IR.Expr :=
        .div (.add (.mul (.local a) (.local b)) (.div (.lit scale) (.lit 2))) (.lit scale)
      let widened := .mul rounded (.lit scale)
      let result := IRExpand.sqrtBinds widened
        ({ fresh := { used := [a, b] } } : Build)
      .ok (result.1.finish (.ret result.2)) := by
  simp only [lowerRetStmt, containsSqrtDown, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, localNames, lowerExprLinear, scaleIr, ScaleMode.scaleNat]
  simp [lowerExpr, scaleIr, Bind.bind, Except.bind]
  rfl

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

def lowerLetBind (fieldSlot mapFieldSlot : Ident → Option Nat) (name : Ident) (e : Expr)
    (overflowSelector : Nat) : Except String Compile.IR.Stmt :=
  match e with
  | .addCheckedNat (.storageGet field) n =>
    match fieldSlot field with
    | some slot =>
      .ok (lowerAddCheckedNatStorage slot n name overflowSelector Compile.IR.Stmt.skip)
    | none => .error s!"unknown storage field {field}"
  | e' => do
    let ir ← lowerExpr fieldSlot mapFieldSlot e'
    .ok (Compile.IR.Stmt.letBind name ir)

end Lsc.Fixed
