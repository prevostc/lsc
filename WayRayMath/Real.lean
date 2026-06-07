import Mathlib
import WayRayMath.Nat

/-!
# WayRayMath.Real

Codec (`decode`, `toReal`) and bridge lemmas pushing `Nat` distance bounds to `ℝ`.
-/

namespace WayRayMath.Real

noncomputable section

open Real

/-- Decode a RAY-encoded natural number to a real. -/
def decode (n : ℕ) : ℝ := (n : ℝ) / Nat.RAY

/-- `RAY^k` as a real scalar. -/
def RAY_pow (k : ℕ) : ℝ := (Nat.RAY ^ k : ℝ)

/-- Decode a value at scale `k` (numerator `n` represents `n / RAY^k`). -/
def toReal (k : ℕ) (n : ℕ) : ℝ := (n : ℝ) / RAY_pow k

private lemma RAY_pos : (0 : ℝ) < Nat.RAY := Nat.cast_pos.mpr Nat.RAY_pos

private lemma RAY_pow_pos (k : ℕ) : 0 < RAY_pow k := by
  unfold RAY_pow
  exact pow_pos RAY_pos k

private lemma nat_dist_eq_abs (x y : ℕ) :
    |(x : ℝ) - (y : ℝ)| = (Nat.rayDist x y : ℝ) := by
  unfold Nat.rayDist
  split_ifs with hx
  · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hx))]
    simp only [Nat.cast_sub hx]
  · have hy : x < y := Nat.lt_of_not_ge hx
    have hxy : x ≤ y := Nat.le_of_lt hy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_lt hy)))]
    simp only [Nat.cast_sub hxy]

/-- Maximum decoded error budget per `rayMulHalfUp` (`10⁻²⁷`). -/
def rayMulHalfUpMaxError : ℝ := (10 : ℝ) ^ (-27 : ℤ)

lemma rayMulHalfUpMaxError_eq_inv : rayMulHalfUpMaxError = (1 : ℝ) / Nat.RAY := by
  unfold rayMulHalfUpMaxError Nat.RAY
  norm_num

lemma rayMulHalfUpMaxError_nonneg : 0 ≤ rayMulHalfUpMaxError := by
  unfold rayMulHalfUpMaxError
  norm_num

private lemma half_ray_inv :
    (Nat.HALF_RAY : ℝ) / (Nat.RAY ^ 2) = rayMulHalfUpMaxError / 2 := by
  rw [rayMulHalfUpMaxError_eq_inv]
  unfold Nat.HALF_RAY Nat.RAY
  norm_num

private lemma half_le_maxError : rayMulHalfUpMaxError / 2 ≤ rayMulHalfUpMaxError := by
  unfold rayMulHalfUpMaxError
  norm_num

private lemma rayMulHalfUp_tight_error (a b : ℕ) :
    |decode a * decode b - decode (Nat.rayMulHalfUp a b)| ≤ rayMulHalfUpMaxError / 2 := by
  set c := Nat.rayMulHalfUp a b
  have hdist := Nat.rayMulHalfUp_error a b
  have hRAY2 : (0 : ℝ) < Nat.RAY ^ 2 := pow_pos RAY_pos 2
  have hstep :
      decode a * decode b - decode c = ((a * b : ℝ) - (c * Nat.RAY : ℝ)) / (Nat.RAY ^ 2) := by
    unfold decode
    field_simp [pow_two]
  rw [hstep, abs_div]
  rw [← Nat.cast_mul, ← Nat.cast_mul, nat_dist_eq_abs, abs_of_pos hRAY2]
  calc
    (Nat.rayDist (a * b) (c * Nat.RAY) : ℝ) / (Nat.RAY ^ 2)
        ≤ (Nat.HALF_RAY : ℝ) / (Nat.RAY ^ 2) :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hdist) (le_of_lt hRAY2)
    _ = rayMulHalfUpMaxError / 2 := half_ray_inv

/-- Push a `Nat.rayDist` bound at scale `k` to a real distance. -/
theorem dist_of_nat_dist (k target computed ε : ℕ)
    (h : Nat.rayDist target computed ≤ ε) :
    |toReal k target - toReal k computed| ≤ (ε : ℝ) / RAY_pow k := by
  dsimp [toReal]
  have hpos := RAY_pow_pos k
  rw [← sub_div, abs_div, nat_dist_eq_abs, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
  gcongr

/-- Single half-up multiply is within `rayMulHalfUpMaxError` in decoded space. -/
theorem rayMulHalfUp_error (a b : ℕ) :
    |decode a * decode b - decode (Nat.rayMulHalfUp a b)| ≤ rayMulHalfUpMaxError := by
  exact le_trans (rayMulHalfUp_tight_error a b) half_le_maxError

/-- Double `rayMulHalfUp` slack at scale 2, in real units. -/
theorem double_rayMulHalfUp_error (sd a b : ℕ) :
    |toReal 2 (Nat.rayMulHalfUp sd (Nat.rayMulHalfUp a b) * Nat.RAY * Nat.RAY) -
        toReal 2 (sd * (a * b))| ≤
      ((sd * Nat.RAY + Nat.RAY * Nat.RAY) : ℝ) / RAY_pow 2 := by
  simpa [RAY_pow] using
    dist_of_nat_dist 2
      (Nat.rayMulHalfUp sd (Nat.rayMulHalfUp a b) * Nat.RAY * Nat.RAY) (sd * (a * b))
      (sd * Nat.RAY + Nat.RAY * Nat.RAY) (Nat.double_rayMulHalfUp_scaled_error sd a b)

/-- Double `rayMulHalfUp` is within `(1 + decode sd) · rayMulHalfUpMaxError / 2`. -/
theorem double_rayMulHalfUp_decode_error (sd a b : ℕ) :
    |decode (Nat.rayMulHalfUp sd (Nat.rayMulHalfUp a b)) - decode sd * decode a * decode b| ≤
      (1 + decode sd) * rayMulHalfUpMaxError / 2 := by
  set p := Nat.rayMulHalfUp a b
  set c := Nat.rayMulHalfUp sd p
  have hinner := rayMulHalfUp_tight_error a b
  have houter := rayMulHalfUp_tight_error sd p
  have h₁ : |decode c - decode sd * decode p| ≤ rayMulHalfUpMaxError / 2 := by
    rw [abs_sub_comm]; exact houter
  have h₂ : |decode p - decode a * decode b| ≤ rayMulHalfUpMaxError / 2 := by
    rw [abs_sub_comm]; exact hinner
  have hmul :
      |decode sd * decode p - decode sd * decode a * decode b| =
        |decode sd| * |decode p - decode a * decode b| := by
    rw [show decode sd * decode p - decode sd * decode a * decode b =
        decode sd * (decode p - decode a * decode b) from by ring, abs_mul]
  have hdecode_abs : |decode sd| = decode sd :=
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt RAY_pos))
  have hdecode_nonneg : 0 ≤ decode sd :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt RAY_pos)
  calc
    |decode c - decode sd * decode a * decode b|
        ≤ |decode c - decode sd * decode p| +
            |decode sd * decode p - decode sd * decode a * decode b| :=
        abs_sub_le _ _ _
    _ = |decode c - decode sd * decode p| +
          |decode sd| * |decode p - decode a * decode b| := by rw [hmul]
    _ ≤ rayMulHalfUpMaxError / 2 + decode sd * (rayMulHalfUpMaxError / 2) := by
          rw [hdecode_abs]
          exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hdecode_nonneg)
    _ = (1 + decode sd) * rayMulHalfUpMaxError / 2 := by ring

end

end WayRayMath.Real
