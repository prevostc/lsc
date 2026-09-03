import Lsc.Lib.Math.Bounds
import Lsc.Lib.Math.Stmt
import Lsc.Lib.Wad.Eval

namespace Lsc.Math.ExprProofs

open Lsc
open Lsc.Fixed
open Lsc.Math

theorem eval_sqrtProductExpr
    {S E Err : Type} [ContractErrors Err] [ContractDSL S E Err]
    (a b : Fixed.Expr) (env : LocalEnv) :
    (Wad.eval (Stmt.sqrtProductExpr a b) env : ContractM S E Err Wad) =
      Wad.eval
        (.sqrtDownChecked (.static 18) (.mulHalfUpChecked (.static 18) a b))
        env := by
  rfl

end Lsc.Math.ExprProofs
