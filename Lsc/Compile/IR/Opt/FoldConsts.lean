import Lsc.Compile.IR.Eval

namespace Lsc.Compile.IR.Opt

open Lsc.Compile.IR

def foldConsts : Expr → Expr
  | .lit n => .lit n
  | .local name => .local name
  | .sload slot => .sload slot
  | .mapSlot base key => .mapSlot base (foldConsts key)
  | .dynSload slot => .dynSload (foldConsts slot)
  | .add a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => .lit (i + j)
    | a', b' => .add a' b'
  | .sub a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => .lit (i - j)
    | a', b' => .sub a' b'
  | .mul a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => .lit (i * j)
    | a', b' => .mul a' b'
  | .div a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => .lit (i / j)
    | a', b' => .div a' b'
  | .lt a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => if i < j then .lit 1 else .lit 0
    | a', b' => .lt a' b'
  | .eq a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => if i == j then .lit 1 else .lit 0
    | a', b' => .eq a' b'
  | .isZero a =>
    match foldConsts a with
    | .lit i => if i == 0 then .lit 1 else .lit 0
    | a' => .isZero a'

def foldConstsStmt : Stmt → Stmt
  | .skip => .skip
  | .seq s1 s2 => .seq (foldConstsStmt s1) (foldConstsStmt s2)
  | .letBind name e => .letBind name (foldConsts e)
  | .sstore slot e => .sstore slot (foldConsts e)
  | .sstoreDyn slot val => .sstoreDyn (foldConsts slot) (foldConsts val)
  | .ifRevert cond => .ifRevert (foldConsts cond)
  | .log0 topic => .log0 topic
  | .log1 topic data => .log1 topic (foldConsts data)
  | .revert0 => .revert0
  | .ret e => .ret (foldConsts e)
  | .checkReentrancyLock => .checkReentrancyLock
  | .setReentrancyLock held => .setReentrancyLock held
  | .externalCall addr selector args checkBoolReturn =>
    .externalCall (foldConsts addr) selector (args.map foldConsts) checkBoolReturn
  | .externalCallBind addr selector args bindName =>
    .externalCallBind (foldConsts addr) selector (args.map foldConsts) bindName
  | .staticCall addr selector args retWords =>
    .staticCall (foldConsts addr) selector (args.map foldConsts) retWords
  | .staticCallBind addr selector args bindName =>
    .staticCallBind (foldConsts addr) selector (args.map foldConsts) bindName

namespace FoldConsts

theorem foldConsts_correct (st : IRState) (e : Expr) :
    evalExpr st (foldConsts e) = evalExpr st e := by
  induction e with
  | lit n => rfl
  | «local» name => rfl
  | sload slot => rfl
  | mapSlot _ key ih =>
    simp only [foldConsts]
    simp [evalExpr, ih]
  | dynSload slot ih =>
    simp only [foldConsts]
    simp [evalExpr, ih]
  | add a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
  | sub a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
  | mul a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
  | div a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
  | lt a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
      split <;> rfl
  | eq a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
      split <;> rfl
  | isZero a ih =>
    simp only [foldConsts]
    cases ha : foldConsts a
    all_goals
      simp only [ha, evalExpr] at ih
      simp only [evalExpr]
      rw [← ih]
      split <;> rfl

theorem foldConstsStmt_correct (st : IRState) (s : Stmt) :
    evalStmt st (foldConstsStmt s) = evalStmt st s := by
  match s with
  | .skip => rfl
  | .seq s1 s2 =>
    simp only [foldConstsStmt, evalStmt]
    rw [foldConstsStmt_correct (evalStmt st (foldConstsStmt s1)) s2,
      foldConstsStmt_correct st s1]
  | .letBind name e =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st e]
  | .sstore slot e =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st e]
  | .sstoreDyn slot val =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st slot, foldConsts_correct st val]
  | .ifRevert cond =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st cond]
  | .log0 topic => rfl
  | .log1 topic data =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st data]
  | .revert0 => rfl
  | .ret _ => rfl
  | .checkReentrancyLock => rfl
  | .setReentrancyLock _ => rfl
  | .externalCall .. => rfl
  | .externalCallBind .. => rfl
  | .staticCall .. => rfl
  | .staticCallBind .. => rfl

end FoldConsts

end Lsc.Compile.IR.Opt
