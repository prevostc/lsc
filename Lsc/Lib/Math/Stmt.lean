import Lsc.Lib.Fixed.ScaleMode
import Lsc.Lib.Fixed.Syntax

/-!
# Math library — `Fixed.Expr` builders for `library_view`

Contract views that call sqrt/min are authored with `library_view` (see `Lsc.Lib.Math.Inline`)
using these helpers instead of extending `lscExpr` grammar. -/

namespace Lsc.Math.Stmt

open Lsc.Fixed

def wadScale : ScaleMode := .static 18

def varWad (name : String) : Fixed.Expr := .var name

def mulHalfUpWad (a b : Fixed.Expr) : Fixed.Expr :=
  .mulHalfUpChecked wadScale a b

def sqrtDownWad (x : Fixed.Expr) : Fixed.Expr :=
  .sqrtDownChecked wadScale x

def minWad (a b : Fixed.Expr) : Fixed.Expr :=
  .min a b

/-- `floor(sqrt(a * b))` at WAD scale (Solady `sqrtWad` on the product). -/
def sqrtProductExpr (a b : Fixed.Expr) : Fixed.Expr :=
  sqrtDownWad (mulHalfUpWad a b)

def minOfExpr (a b : Fixed.Expr) : Fixed.Expr :=
  minWad a b

end Lsc.Math.Stmt
