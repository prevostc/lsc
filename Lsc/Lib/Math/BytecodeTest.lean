import Lsc.Lib.Math.Proofs
import Mathlib.Data.Nat.Sqrt

namespace Lsc.Lib.Math.BytecodeTest

open Lsc.Fixed
open Lsc.Math.Proofs

example : isqrtFloor 0 = 0 := by native_decide
example : isqrtFloor 10 = Nat.sqrt 10 := isqrtFloor_eq_natSqrt 10 (by decide)
example : isqrtFloor 65535 = Nat.sqrt 65535 := isqrtFloor_eq_natSqrt 65535 (by decide)
example : isqrtFloor (2 ^ 256 - 1) = Nat.sqrt (2 ^ 256 - 1) :=
  isqrtFloor_eq_natSqrt _ (by omega)

example : 3 ^^^ Nat.mul (5 ^^^ 3) (if 5 < 3 then 1 else 0) = Nat.min 3 5 := branchlessMin 3 5
example : 5 ^^^ Nat.mul (3 ^^^ 5) (if 3 < 5 then 1 else 0) = Nat.min 5 3 := branchlessMin 5 3
example : 4 ^^^ Nat.mul (4 ^^^ 4) (if 4 < 4 then 1 else 0) = Nat.min 4 4 := branchlessMin 4 4
example : Nat.min 3 5 = 3 := by decide
example : Nat.min 5 3 = 3 := by decide
example : Nat.min 4 4 = 4 := by decide

theorem sqrt_grid (n : Nat) (h : n ≤ 255) : isqrtFloor n = Nat.sqrt n :=
  isqrtFloor_eq_natSqrt n (lt_of_le_of_lt h (by decide))

end Lsc.Lib.Math.BytecodeTest
