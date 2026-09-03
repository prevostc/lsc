import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Math.SqrtAlgo

namespace Lsc.Fixed

/-- Integer floor square root used by both source evaluation and primitive IR lowering. -/
def isqrtFloor (n : Nat) : Nat :=
  Lsc.Math.SqrtAlgo.sqrtNat n

end Lsc.Fixed
