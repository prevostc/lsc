import Lsc.Lib.Math
import Lsc.Lib.Wad.Eval

namespace Lsc.Lib.Math.Test

open Lsc.Fixed Lsc.Wad

example : Wad.min (Wad.mkNat 3) (Wad.mkNat 5) = Wad.mkNat 3 := rfl

example : isqrtFloor 10 = 3 := by native_decide

example : isqrtFloor 100 = 10 := by native_decide

end Lsc.Lib.Math.Test
