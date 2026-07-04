import Lsc.Compile.IR.Opt.FoldConsts
import Lsc.Compile.IR.Opt.ElimUnusedLocals
import Lsc.Compile.IR.Opt.Pipeline
import Lsc.Lib.Wei.Optimize

namespace Lsc.Compile.IR.Opt

open Lsc.Compile.IR

theorem foldConsts_add_example :
    foldConsts (.add (.lit 2) (.lit 3)) = .lit 5 := rfl

def deadBind : Stmt :=
  .seq (.letBind "dead" (.lit 42)) (.sstore 0 (.lit 1))

theorem elimUnusedLocals_deadBind :
    elimUnusedLocals deadBind = .sstore 0 (.lit 1) := rfl

theorem optimizeStmt_deadBind :
    optimizeStmt deadBind = .sstore 0 (.lit 1) := rfl

theorem incrementLetIR_elimUnusedLocals_id :
    elimUnusedLocals Wei.incrementLetIR = Wei.incrementLetIR := rfl

end Lsc.Compile.IR.Opt
