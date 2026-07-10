import Lsc.Compile.IR.Eval
import Lsc.Compile.IR.EvalLemmas
import Lsc.Compile.IR.FreeVars

namespace Lsc.Compile.IR.Opt

open Lsc.Compile.IR

/-- Eliminate `letBind name e` when `name` is absent from the free variables of the continuation.
    For `seq s1 s2` where `s1` is not a `letBind`, recurse only into `s2`. -/
def elimUnusedLocals : Stmt → Stmt
  | .seq (.letBind name e) rest =>
    let rest' := elimUnusedLocals rest
    if name ∈ freeVarsStmt rest' then .seq (.letBind name e) rest'
    else rest'
  | .seq s1 s2 => .seq s1 (elimUnusedLocals s2)
  | s => s

namespace ElimUnusedLocals

theorem elimUnusedLocals_correct (st : IRState) (s : Stmt) :
    observablyEqual (evalStmt st s) (evalStmt st (elimUnusedLocals s)) := by
  induction s generalizing st with
  | seq s1 s2 ih1 ih2 =>
    cases s1 with
    | letBind name e =>
      by_cases h : name ∈ freeVarsStmt (elimUnusedLocals s2)
      · simp only [elimUnusedLocals, if_pos h, evalStmt_seq, evalStmt_letBind]
        exact ih2 _
      · simp only [elimUnusedLocals, if_neg h, evalStmt_seq, evalStmt_letBind]
        exact observablyEqual_trans (ih2 _)
          (evalStmt_setLocal_unused_obs st name (evalExpr st e) (elimUnusedLocals s2) h)
    | skip =>
      simp only [show elimUnusedLocals (.seq .skip s2) = .seq .skip (elimUnusedLocals s2) from rfl,
                 evalStmt_seq, evalStmt_skip]
      exact ih2 st
    | seq s1a s1b =>
      simp only [show elimUnusedLocals (.seq (.seq s1a s1b) s2) =
                      .seq (.seq s1a s1b) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | sstore slot e =>
      simp only [show elimUnusedLocals (.seq (.sstore slot e) s2) =
                      .seq (.sstore slot e) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | sstoreDyn slot val =>
      simp only [show elimUnusedLocals (.seq (.sstoreDyn slot val) s2) =
                      .seq (.sstoreDyn slot val) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | ifRevertSelector cond sel =>
      simp only [evalStmt_seq]
      exact ih2 _
    | log0 topic =>
      simp only [show elimUnusedLocals (.seq (.log0 topic) s2) =
                      .seq (.log0 topic) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | log1 topic data =>
      simp only [show elimUnusedLocals (.seq (.log1 topic data) s2) =
                      .seq (.log1 topic data) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | revertSelector sel =>
      simp only [evalStmt_seq]
      exact ih2 _
    | ret e =>
      simp only [show elimUnusedLocals (.seq (.ret e) s2) =
                      .seq (.ret e) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | externalCall addr selector args checkBoolReturn failSel =>
      simp only [show elimUnusedLocals (.seq (.externalCall addr selector args checkBoolReturn failSel) s2) =
                      .seq (.externalCall addr selector args checkBoolReturn failSel) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | externalCallBind addr selector args bindName failSel =>
      simp only [show elimUnusedLocals (.seq (.externalCallBind addr selector args bindName failSel) s2) =
                      .seq (.externalCallBind addr selector args bindName failSel) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | staticCall addr selector args retWords failSel =>
      simp only [show elimUnusedLocals (.seq (.staticCall addr selector args retWords failSel) s2) =
                      .seq (.staticCall addr selector args retWords failSel) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | staticCallBind addr selector args bindName failSel =>
      simp only [show elimUnusedLocals (.seq (.staticCallBind addr selector args bindName failSel) s2) =
                      .seq (.staticCallBind addr selector args bindName failSel) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
    | checkReentrancyLock sel =>
      simp only [show elimUnusedLocals (.seq (.checkReentrancyLock sel) s2) =
                      .seq (.checkReentrancyLock sel) (elimUnusedLocals s2) from rfl, evalStmt_seq]
      exact ih2 _
    | setReentrancyLock held =>
      simp only [show elimUnusedLocals (.seq (.setReentrancyLock held) s2) =
                      .seq (.setReentrancyLock held) (elimUnusedLocals s2) from rfl, evalStmt_seq]
      exact ih2 _
  | skip => exact observablyEqual_refl _
  | letBind name e => exact observablyEqual_refl _
  | sstore slot e => exact observablyEqual_refl _
  | sstoreDyn _ _ => exact observablyEqual_refl _
  | ifRevertSelector cond _ => exact observablyEqual_refl _
  | log0 topic => exact observablyEqual_refl _
  | log1 topic data => exact observablyEqual_refl _
  | revertSelector _ => exact observablyEqual_refl _
  | ret e => exact observablyEqual_refl _
  | checkReentrancyLock _ => exact observablyEqual_refl _
  | setReentrancyLock held => exact observablyEqual_refl _
  | externalCall addr selector args checkBoolReturn failSel => exact observablyEqual_refl _
  | externalCallBind addr selector args bindName failSel => exact observablyEqual_refl _
  | staticCall addr selector args retWords failSel => exact observablyEqual_refl _
  | staticCallBind addr selector args bindName failSel => exact observablyEqual_refl _

end ElimUnusedLocals

end Lsc.Compile.IR.Opt
