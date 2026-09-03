import Lsc.Compile.IR.Eval

set_option maxHeartbeats 400000

namespace Lsc.Compile.IR.Opt

open Lsc.Compile.IR

def foldConsts : Expr → Expr
  | .lit n => .lit n
  | .local name => .local name
  | .sload slot => .sload slot
  | .mapSlot base key => .mapSlot base (foldConsts key)
  | .mapSlot2 base key1 key2 => .mapSlot2 base (foldConsts key1) (foldConsts key2)
  | .dynSload slot => .dynSload (foldConsts slot)
  | .calldataWord offset => .calldataWord offset
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
  | .gt a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => if i > j then .lit 1 else .lit 0
    | a', b' => .gt a' b'
  | .shr amount val =>
    match foldConsts amount, foldConsts val with
    | .lit k, .lit v => .lit (v / 2 ^ k)
    | amount', val' => .shr amount' val'
  | .xor a b =>
    match foldConsts a, foldConsts b with
    | .lit i, .lit j => .lit (i ^^^ j)
    | a', b' => .xor a' b'

def foldConstsStmt : Stmt → Stmt
  | .skip => .skip
  | .seq s1 s2 => .seq (foldConstsStmt s1) (foldConstsStmt s2)
  | .letBind name e => .letBind name (foldConsts e)
  | .sstore slot e => .sstore slot (foldConsts e)
  | .sstoreDyn slot val => .sstoreDyn (foldConsts slot) (foldConsts val)
  | .ifRevertSelector cond sel => .ifRevertSelector (foldConsts cond) sel
  | .log topic datas => .log topic (datas.map foldConsts)
  | .revertSelector sel => .revertSelector sel
  | .ret e => .ret (foldConsts e)
  | .checkReentrancyLock sel => .checkReentrancyLock sel
  | .setReentrancyLock held => .setReentrancyLock held
  | .externalCall addr selector args checkBoolReturn failSel =>
    .externalCall (foldConsts addr) selector (args.map foldConsts) checkBoolReturn failSel
  | .externalCallBind addr selector args bindName failSel =>
    .externalCallBind (foldConsts addr) selector (args.map foldConsts) bindName failSel
  | .staticCall addr selector args retWords failSel =>
    .staticCall (foldConsts addr) selector (args.map foldConsts) retWords failSel
  | .staticCallBind addr selector args bindName failSel =>
    .staticCallBind (foldConsts addr) selector (args.map foldConsts) bindName failSel

namespace FoldConsts

theorem foldConsts_correct (st : IRState) (e : Expr) :
    evalExpr st (foldConsts e) = evalExpr st e := by
  induction e with
  | lit n => rfl
  | «local» name => rfl
  | sload slot => rfl
  | mapSlot _ key ih =>
    simp only [foldConsts]
    simp [evalExpr]
  | mapSlot2 _ key1 key2 ih1 ih2 =>
    simp only [foldConsts]
    simp [evalExpr]
  | dynSload slot ih =>
    simp only [foldConsts]
    simp [evalExpr, ih]
  | calldataWord offset => rfl
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
  | gt a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
      split <;> rfl
  | shr amount val ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts amount <;> cases hb : foldConsts val
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]
  | xor a b ih_a ih_b =>
    simp only [foldConsts]
    cases ha : foldConsts a <;> cases hb : foldConsts b
    all_goals
      simp only [ha, hb, evalExpr] at ih_a ih_b
      simp only [evalExpr]
      rw [← ih_a, ← ih_b]

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
  | .ifRevertSelector cond sel =>
    simp only [foldConstsStmt, evalStmt, foldConsts_correct st cond]
  | .log topic datas =>
    have hdatas : datas.map (evalExpr st ∘ foldConsts) = datas.map (evalExpr st) := by
      induction datas with
      | nil => rfl
      | cons d ds ih =>
        simp [List.map, foldConsts_correct st d, ih]
    have hcomp : (datas.map foldConsts).map (evalExpr st) = datas.map (evalExpr st) := by
      simpa [Function.comp, List.map_map] using hdatas
    simp only [foldConstsStmt, evalStmt_log, hcomp]
  | .revertSelector _ => rfl
  | .ret _ => rfl
  | .checkReentrancyLock _ => rfl
  | .setReentrancyLock _ => rfl
  | .externalCall .. => rfl
  | .externalCallBind .. => rfl
  | .staticCall .. => rfl
  | .staticCallBind .. => rfl

end FoldConsts

end Lsc.Compile.IR.Opt
