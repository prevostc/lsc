import Lsc.Lib.Fixed.ScaleMode
import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Math.Isqrt

namespace Lsc.Fixed

def min {d : Nat} {tag : Type} (a b : Fixed d tag) : Fixed d tag :=
  if a.n ≤ b.n then a else b

/-- Fixed-point floor sqrt: `floor(sqrt(x * scale))` in raw units at scale `scaleMode`. -/
def sqrtDown (scaleMode : ScaleMode) {d : Nat} {tag : Type} (x : Fixed d tag) :
    Except ArithError (Fixed d tag) :=
  let s := scaleMode.scaleNat
  if s == 1 then
    .ok (mkNat (isqrtFloor x.n))
  else
    let widened := x.n * s
    if x.n != 0 && widened / x.n != s then
      .error .Overflow
    else if widened ≥ 2 ^ 256 then
      .error .Overflow
    else
      .ok (mkNat (isqrtFloor widened))

end Lsc.Fixed

namespace Lsc.Math

export Fixed (isqrtFloor sqrtDown min)

end Lsc.Math
