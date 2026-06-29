import LscV2.Compile.IR.Opt.FoldConsts
import LscV2.Compile.IR.Opt.ElimUnusedLocals

namespace LscV2.Compile.IR.Opt

open LscV2.Compile.IR
open FoldConsts (foldConstsStmt_correct)
open ElimUnusedLocals (elimUnusedLocals_correct)

/-- Run IR optimization passes in order (fold constants, then drop unused locals). -/
def optimizeStmt (s : Stmt) : Stmt :=
  elimUnusedLocals (foldConstsStmt s)

theorem optimizeStmt_correct (st : IRState) (s : Stmt) :
    observablyEqual (evalStmt st s) (evalStmt st (optimizeStmt s)) := by
  unfold optimizeStmt
  rw [← foldConstsStmt_correct st s]
  exact elimUnusedLocals_correct st (foldConstsStmt s)

end LscV2.Compile.IR.Opt
