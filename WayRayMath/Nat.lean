import Mathlib

/-!
# WayRayMath.Nat

RAY fixed-point arithmetic on `ℕ`, mirroring Aave's `WadRayMath`
([source](https://github.com/aave/aave-v4/blob/main/src/libraries/math/WadRayMath.sol)).

Includes definitions, helper lemmas, single-op rounding bounds, monotonicity,
and compositional error certificates.

Overflow and division-by-zero are ignored here; see `WayRayMath.Evm` for
EVM-faithful `Except` wrappers.
-/

namespace WayRayMath.Nat

/-! ## Constants -/

/-- `1e27` -/
def RAY : ℕ := 10^27

/-- `RAY / 2`, used by half-up rounding. -/
def HALF_RAY : ℕ := RAY / 2

/-! ## Operations -/

/-- Multiplies two RAY numbers, rounding down. -/
def rayMulDown (a b : ℕ) : ℕ :=
  (a * b) / RAY

/-- Multiplies two RAY numbers, rounding up. -/
def rayMulUp (a b : ℕ) : ℕ :=
  let prod := a * b
  prod / RAY + if prod % RAY > 0 then 1 else 0

/-- Multiplies two RAY numbers, rounding half up (Aave's default `rayMul`). -/
def rayMulHalfUp (a b : ℕ) : ℕ :=
  (a * b + HALF_RAY) / RAY

/-- Divides two RAY numbers, rounding down. -/
def rayDivDown (a b : ℕ) : ℕ :=
  (a * RAY) / b

/-- Divides two RAY numbers, rounding up. -/
def rayDivUp (a b : ℕ) : ℕ :=
  let prod := a * RAY
  prod / b + if prod % b > 0 then 1 else 0

/-- Divides two RAY numbers, rounding half up. -/
def rayDivHalfUp (a b : ℕ) : ℕ :=
  (a * RAY + b / 2) / b

/-- Absolute difference on `ℕ`. -/
def rayDist (x y : ℕ) : ℕ :=
  if x ≥ y then x - y else y - x

/-- Remainder after half-up ray multiply. -/
def rayRemHalfUp (a b : ℕ) : ℕ :=
  (a * b + HALF_RAY) % RAY

/-! ## Basic lemmas -/

lemma RAY_pos : 0 < RAY := by unfold RAY; native_decide

lemma two_half_eq_ray : 2 * HALF_RAY = RAY := by
  unfold HALF_RAY RAY
  native_decide

lemma two_half_le_ray : 2 * HALF_RAY ≤ RAY := by
  unfold HALF_RAY RAY
  native_decide

lemma half_add_half_eq_ray : HALF_RAY + HALF_RAY = RAY := by
  rw [← Nat.two_mul, two_half_eq_ray]

lemma div_mul_add_mod (n k : ℕ) : n / k * k + n % k = n := by
  simpa [mul_comm] using Nat.div_add_mod n k

lemma rayRemHalfUp_lt (a b : ℕ) : rayRemHalfUp a b < RAY := by
  dsimp [rayRemHalfUp]
  exact Nat.mod_lt _ RAY_pos

lemma rayMulHalfUp_add_mod (a b : ℕ) :
    rayMulHalfUp a b * RAY + rayRemHalfUp a b = a * b + HALF_RAY := by
  dsimp [rayMulHalfUp, rayRemHalfUp]
  exact div_mul_add_mod (a * b + HALF_RAY) RAY

lemma rayMulDown_mul_le (a b : ℕ) :
    rayMulDown a b * RAY ≤ a * b :=
  Nat.div_mul_le_self _ _

lemma rayMulHalfUp_mul_le (a b : ℕ) :
    rayMulHalfUp a b * RAY ≤ a * b + HALF_RAY :=
  Nat.div_mul_le_self _ _

lemma rayDivDown_mul_le (a b : ℕ) (_hb : 0 < b) :
    rayDivDown a b * b ≤ a * RAY :=
  Nat.div_mul_le_self _ _

lemma rayDiv_mul_le (a b : ℕ) (_hb : 0 < b) :
    rayDivHalfUp a b * b ≤ a * RAY + b / 2 :=
  Nat.div_mul_le_self _ _

/-! ## Monotonicity -/

lemma rayMulDown_le_rayMulUp (a b : ℕ) :
    rayMulDown a b ≤ rayMulUp a b := by
  unfold rayMulDown rayMulUp
  by_cases h : (a * b) % RAY > 0
  · simp [h]
  · simp [h]

lemma rayMulHalfUp_mono_left (a b c : ℕ) (h : a ≤ b) :
    rayMulHalfUp a c ≤ rayMulHalfUp b c := by
  unfold rayMulHalfUp
  apply Nat.div_le_div_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _

lemma rayMulHalfUp_mono_right (a b c : ℕ) (h : a ≤ b) :
    rayMulHalfUp c a ≤ rayMulHalfUp c b := by
  unfold rayMulHalfUp
  apply Nat.div_le_div_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

lemma rayMulHalfUp_mono (s₀ s₁ u₀ u₁ : ℕ)
    (h_smono : s₀ ≤ s₁) (h_umono : u₀ ≤ u₁) :
    rayMulHalfUp s₀ u₀ ≤ rayMulHalfUp s₁ u₁ :=
  le_trans (rayMulHalfUp_mono_right _ _ _ h_umono) (rayMulHalfUp_mono_left _ _ _ h_smono)

/-! ## Single-op bounds -/

theorem rayMulHalfUp_exact_ge (a b : ℕ) :
    rayMulHalfUp a b * RAY ≤ a * b + HALF_RAY :=
  rayMulHalfUp_mul_le a b

theorem rayMulHalfUp_exact_le (a b : ℕ) :
    a * b ≤ rayMulHalfUp a b * RAY + HALF_RAY := by
  have hr := rayRemHalfUp_lt a b
  have hmod := rayMulHalfUp_add_mod a b
  have hdouble := half_add_half_eq_ray
  omega

theorem rayMulHalfUp_error (a b : ℕ) :
    rayDist (a * b) (rayMulHalfUp a b * RAY) ≤ HALF_RAY := by
  have hge := rayMulHalfUp_exact_ge a b
  have hle := rayMulHalfUp_exact_le a b
  unfold rayDist
  split_ifs <;> omega

theorem rayMulDown_exact_le (a b : ℕ) :
    rayMulDown a b * RAY ≤ a * b :=
  rayMulDown_mul_le a b

theorem rayDivDown_exact_le (a b : ℕ) (_hb : 0 < b) :
    rayDivDown a b * b ≤ a * RAY :=
  rayDivDown_mul_le a b _hb

/-! ## Composition -/

lemma rayDist_comm (x y : ℕ) : rayDist x y = rayDist y x := by
  unfold rayDist
  split_ifs <;> omega

lemma rayDist_triangle (x y z : ℕ) : rayDist x z ≤ rayDist x y + rayDist y z := by
  dsimp [rayDist]
  split_ifs with h1 h2 <;> omega

private lemma mul_sub_distrib (k a b : ℕ) (h : a ≤ b) :
    k * b - k * a = k * (b - a) := by
  apply Nat.sub_eq_of_eq_add
  rw [← Nat.mul_add, Nat.sub_add_cancel h]

lemma rayDist_mul_left (k x y : ℕ) :
    rayDist (k * x) (k * y) = k * rayDist x y := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [rayDist]
  · rcases le_total x y with hxy | hxy
    · rcases eq_or_lt_of_le hxy with hx | hlt
      · subst hx
        simp [rayDist]
      · have hklt : k * x < k * y := Nat.mul_lt_mul_of_pos_left hlt hk
        dsimp [rayDist]
        simp [Nat.not_le.mpr hlt, Nat.not_le.mpr hklt, mul_sub_distrib k x y (le_of_lt hlt)]
    · rcases eq_or_lt_of_le hxy with hy | hlt
      · subst hy
        simp [rayDist]
      · have hklt : k * y < k * x := Nat.mul_lt_mul_of_pos_left hlt hk
        dsimp [rayDist]
        have hkx : k * x ≥ k * y := le_of_lt hklt
        simp [hkx, hxy, Nat.mul_sub_left_distrib]

lemma rayDist_mul_right (k x y : ℕ) :
    rayDist (x * k) (y * k) = rayDist x y * k := by
  rw [Nat.mul_comm x k, Nat.mul_comm y k, rayDist_mul_left, Nat.mul_comm]

/-- Double `rayMulHalfUp` slack to the exact product, in `RAY²`-scaled space. -/
theorem double_rayMulHalfUp_scaled_error (sd a b : ℕ) :
    rayDist (rayMulHalfUp sd (rayMulHalfUp a b) * RAY * RAY) (sd * (a * b)) ≤
      sd * RAY + RAY * RAY := by
  set p := rayMulHalfUp a b
  set c := rayMulHalfUp sd p
  have he₁ : rayDist (a * b) (p * RAY) ≤ RAY :=
    le_trans (rayMulHalfUp_error a b) (by unfold HALF_RAY RAY; decide)
  have he₂ : rayDist (sd * p) (c * RAY) ≤ RAY :=
    le_trans (rayMulHalfUp_error sd p) (by unfold HALF_RAY RAY; decide)
  have htri :=
    rayDist_triangle (c * RAY * RAY) (sd * p * RAY) (sd * (a * b))
  have h₁ := rayDist_mul_right RAY (c * RAY) (sd * p)
  have h₂ : rayDist (sd * p * RAY) (sd * (a * b)) = sd * rayDist (p * RAY) (a * b) := by
    have hstep : sd * p * RAY = sd * (p * RAY) := by rw [← Nat.mul_assoc]
    calc
      rayDist (sd * p * RAY) (sd * (a * b))
          = rayDist (sd * (p * RAY)) (sd * (a * b)) := by rw [hstep]
      _ = sd * rayDist (p * RAY) (a * b) := rayDist_mul_left sd (p * RAY) (a * b)
  have he₁' : rayDist (p * RAY) (a * b) ≤ RAY := by
    rw [rayDist_comm]
    exact he₁
  have he₂' : rayDist (c * RAY) (sd * p) ≤ RAY := by
    rw [rayDist_comm]
    exact he₂
  calc
    rayDist (c * RAY * RAY) (sd * (a * b))
        ≤ rayDist (c * RAY * RAY) (sd * p * RAY) + rayDist (sd * p * RAY) (sd * (a * b)) := htri
    _ = RAY * rayDist (c * RAY) (sd * p) + sd * rayDist (p * RAY) (a * b) := by
        rw [h₁, h₂, Nat.mul_comm (rayDist (c * RAY) (sd * p)) RAY]
    _ ≤ RAY * RAY + sd * RAY := by gcongr
    _ = sd * RAY + RAY * RAY := by ring

end WayRayMath.Nat
