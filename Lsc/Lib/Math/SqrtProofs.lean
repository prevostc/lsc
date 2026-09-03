import Lsc.Lib.Math.Bounds
import Lsc.Lib.Math.SqrtCorrect
import Mathlib.Data.Nat.Sqrt

namespace Lsc.Math.SqrtProofs

open Lsc.Fixed
open Lsc.Math.Bounds

private theorem widen_div (x s : Nat) (hx : x ≠ 0) : x * s / x = s := by
  rw [Nat.mul_comm, Nat.mul_div_left _ (Nat.pos_of_ne_zero hx)]

theorem sqrtDown_eq_ok_of (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (x : Fixed d tag) (h : canSqrtDown scaleMode x) :
    sqrtDown scaleMode x =
      .ok (mkNat (Lsc.Math.SqrtAlgo.sqrtNat (sqrtArg scaleMode.scaleNat x.n))) := by
  unfold canSqrtDown sqrtArg at h
  simp only [sqrtDown]
  by_cases hs : scaleMode.scaleNat = 1
  · simp [hs, isqrtFloor, sqrtArg]
  · simp only [hs, beq_iff_eq, ↓reduceIte]
    have hw : x.n * scaleMode.scaleNat < 2 ^ 256 := by
      simpa [hs, u256Bound] using h
    have hwLit :
        x.n * scaleMode.scaleNat <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      simpa using hw
    have hguard : ¬(x.n != 0 && x.n * scaleMode.scaleNat / x.n != scaleMode.scaleNat) := by
      by_cases hx : x.n = 0
      · simp [hx]
      · simp [hx, widen_div x.n scaleMode.scaleNat hx]
    simp [hguard, Nat.not_le.mpr hwLit, isqrtFloor, sqrtArg, hs]

theorem sqrtDown_eq_error_of (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (x : Fixed d tag) (h : ¬canSqrtDown scaleMode x) :
    sqrtDown scaleMode x = .error .Overflow := by
  unfold canSqrtDown sqrtArg at h
  simp only [sqrtDown]
  by_cases hs : scaleMode.scaleNat = 1
  · have hx : x.n < 2 ^ 256 := x.raw.isLt
    have hf : False := by
      simp [hs, u256Bound] at h
      omega
    exact hf.elim
  · simp only [hs, beq_iff_eq, ↓reduceIte]
    have hw : 2 ^ 256 ≤ x.n * scaleMode.scaleNat := by
      simpa [hs, Nat.not_lt, u256Bound] using h
    have hwLit :
        115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
          x.n * scaleMode.scaleNat := by
      simpa using hw
    by_cases hx : x.n = 0
    · simp [hx] at hw
    · simp [hx, widen_div x.n scaleMode.scaleNat hx, hwLit]

theorem sqrtDown_result_spec (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (x r : Fixed d tag) (h : sqrtDown scaleMode x = .ok r) :
    let widened := sqrtArg scaleMode.scaleNat x.n
    r.n * r.n ≤ widened ∧ widened < (r.n + 1) * (r.n + 1) := by
  intro widened
  have hw : canSqrtDown scaleMode x := by
    by_contra hn
    have herr := sqrtDown_eq_error_of scaleMode x hn
    rw [h] at herr
    cases herr
  have hw' : widened < 2 ^ 256 := by
    simpa [canSqrtDown, widened] using hw
  have hok := sqrtDown_eq_ok_of scaleMode x hw
  have heq : r = mkNat (Lsc.Math.SqrtAlgo.sqrtNat widened) := by
    apply Except.ok.inj
    exact h.symm.trans (by simpa [widened] using hok)
  have hsqrt := Lsc.Math.SqrtCorrect.sqrtNat_eq_natSqrt_u256 widened hw'
  have hslt : Lsc.Math.SqrtAlgo.sqrtNat widened < 2 ^ 256 := by
    rw [hsqrt]
    exact lt_of_le_of_lt (Nat.sqrt_le_self widened) hw'
  have hslt' :
      Lsc.Math.SqrtAlgo.sqrtNat widened <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa using hslt
  have hr : r.n = Lsc.Math.SqrtAlgo.sqrtNat widened := by
    rw [heq]
    simp [Fixed.n, mkNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslt']
  rw [hr, hsqrt]
  exact ⟨Nat.sqrt_le widened, Nat.lt_succ_sqrt widened⟩

end Lsc.Math.SqrtProofs
