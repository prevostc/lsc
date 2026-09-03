import Init.Data.Nat.Bitwise.Lemmas
import Lsc.Lib.Fixed.ScaleMode
import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Math.Isqrt
import Lsc.Lib.Math.Sqrt
import Lsc.Lib.Math.SqrtCorrect
import Mathlib.Data.Nat.Sqrt

namespace Lsc.Math.Proofs

open Lsc.Fixed

/-! ## `min` -/

/-- Solady branchless `min` on raw words. -/
theorem branchlessMin (a b : Nat) :
    a ^^^ Nat.mul (b ^^^ a) (if b < a then 1 else 0) = Nat.min a b := by
  by_cases h : b < a
  · simp [h, Nat.min, ↓reduceIte, Nat.mul_one, Nat.min_eq_right (Nat.le_of_lt h)]
    rw [Nat.xor_comm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp [h, Nat.min, ↓reduceIte, Nat.mul_zero, Nat.xor_zero, Nat.min_eq_left (Nat.le_of_not_lt h)]

theorem isqrtFloor_eq_natSqrt (n : Nat) (h : n < 2 ^ 256) :
    isqrtFloor n = Nat.sqrt n := by
  exact SqrtCorrect.sqrtNat_eq_natSqrt_u256 n h

theorem isqrtFloor_le (n : Nat) (h : n < 2 ^ 256) :
    isqrtFloor n * isqrtFloor n ≤ n := by
  rw [isqrtFloor_eq_natSqrt n h]
  exact Nat.sqrt_le n

end Lsc.Math.Proofs
