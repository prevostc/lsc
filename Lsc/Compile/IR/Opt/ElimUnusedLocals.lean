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
    | ifRevert cond =>
      simp only [show elimUnusedLocals (.seq (.ifRevert cond) s2) =
                      .seq (.ifRevert cond) (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
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
    | revert0 =>
      simp only [show elimUnusedLocals (.seq .revert0 s2) =
                      .seq .revert0 (elimUnusedLocals s2) from rfl,
                 evalStmt_seq]
      exact ih2 _
  | skip => exact observablyEqual_refl _
  | letBind name e => exact observablyEqual_refl _
  | sstore slot e => exact observablyEqual_refl _
  | ifRevert cond => exact observablyEqual_refl _
  | log0 topic => exact observablyEqual_refl _
  | log1 topic data => exact observablyEqual_refl _
  | revert0 => exact observablyEqual_refl _

end ElimUnusedLocals

end Lsc.Compile.IR.Opt
