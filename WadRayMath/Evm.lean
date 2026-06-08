import WadRayMath.Nat
import WadRayMath.Real

/-!
# WadRayMath.Evm

EVM-faithful `Except` wrappers with `uint256` overflow and revert guards,
matching on-chain `WadRayMath` behavior.
-/

namespace WadRayMath.Evm

open WadRayMath.Nat

/-- `type(uint256).max` -/
def UINT256_MAX : ℕ := 2^256 - 1

inductive Error
  | overflow
  | divByZero
  deriving DecidableEq, Repr

/-- `rayMulDown` / `rayMulUp` revert unless `b = 0` or `a ≤ UINT256_MAX / b`. -/
def rayMulReverts (a b : ℕ) : Prop :=
  b ≠ 0 ∧ a > UINT256_MAX / b

/-- `rayDivDown` / `rayDivUp` revert when `b = 0` or `a > UINT256_MAX / RAY`. -/
def rayDivReverts (a b : ℕ) : Prop :=
  b = 0 ∨ a > UINT256_MAX / RAY

/-- `rayMulHalfUp` reverts unless `b = 0` or `a ≤ (UINT256_MAX - HALF_RAY) / b`. -/
def rayMulHalfUpReverts (a b : ℕ) : Prop :=
  b ≠ 0 ∧ a > (UINT256_MAX - HALF_RAY) / b

/-- `rayDivHalfUp` reverts when `b = 0` or `a > (UINT256_MAX - b / 2) / RAY`. -/
def rayDivHalfUpReverts (a b : ℕ) : Prop :=
  b = 0 ∨ a > (UINT256_MAX - b / 2) / RAY

instance (a b : ℕ) : Decidable (rayMulReverts a b) :=
  inferInstanceAs (Decidable (b ≠ 0 ∧ a > UINT256_MAX / b))

instance (a b : ℕ) : Decidable (rayDivReverts a b) :=
  inferInstanceAs (Decidable (b = 0 ∨ a > UINT256_MAX / RAY))

instance (a b : ℕ) : Decidable (rayMulHalfUpReverts a b) :=
  inferInstanceAs (Decidable (b ≠ 0 ∧ a > (UINT256_MAX - HALF_RAY) / b))

instance (a b : ℕ) : Decidable (rayDivHalfUpReverts a b) :=
  inferInstanceAs (Decidable (b = 0 ∨ a > (UINT256_MAX - b / 2) / RAY))

/-- Multiplies two RAY numbers, rounding down. -/
def rayMulDown (a b : ℕ) : Except Error ℕ :=
  if rayMulReverts a b then
    .error .overflow
  else
    .ok (Nat.rayMulDown a b)

/-- Multiplies two RAY numbers, rounding up. -/
def rayMulUp (a b : ℕ) : Except Error ℕ :=
  if rayMulReverts a b then
    .error .overflow
  else
    .ok (Nat.rayMulUp a b)

/-- Divides two RAY numbers, rounding down. -/
def rayDivDown (a b : ℕ) : Except Error ℕ :=
  if rayDivReverts a b then
    if b = 0 then .error .divByZero else .error .overflow
  else
    .ok (Nat.rayDivDown a b)

/-- Divides two RAY numbers, rounding up. -/
def rayDivUp (a b : ℕ) : Except Error ℕ :=
  if rayDivReverts a b then
    if b = 0 then .error .divByZero else .error .overflow
  else
    .ok (Nat.rayDivUp a b)

/-- Multiplies two RAY numbers, rounding half up. -/
def rayMulHalfUp (a b : ℕ) : Except Error ℕ :=
  if rayMulHalfUpReverts a b then
    .error .overflow
  else
    .ok (Nat.rayMulHalfUp a b)

/-- Divides two RAY numbers, rounding half up. -/
def rayDivHalfUp (a b : ℕ) : Except Error ℕ :=
  if rayDivHalfUpReverts a b then
    if b = 0 then .error .divByZero else .error .overflow
  else
    .ok (Nat.rayDivHalfUp a b)

/-! ## EVM simulation -/

theorem rayMulHalfUp_eq_ok (a b : ℕ) (h : ¬ rayMulHalfUpReverts a b) :
    rayMulHalfUp a b = .ok (Nat.rayMulHalfUp a b) := by
  unfold rayMulHalfUp
  rw [if_neg h]

theorem rayMulHalfUp_eq_err (a b : ℕ) (h : rayMulHalfUpReverts a b) :
    rayMulHalfUp a b = .error .overflow := by
  unfold rayMulHalfUp
  rw [if_pos h]

theorem rayMulDown_eq_ok (a b : ℕ) (h : ¬ rayMulReverts a b) :
    rayMulDown a b = .ok (Nat.rayMulDown a b) := by
  unfold rayMulDown
  rw [if_neg h]

theorem rayMulDown_eq_err (a b : ℕ) (h : rayMulReverts a b) :
    rayMulDown a b = .error .overflow := by
  unfold rayMulDown
  rw [if_pos h]

theorem rayMulHalfUp_error_ok (a b : ℕ) (h : ¬ rayMulHalfUpReverts a b) :
    ∀ c, rayMulHalfUp a b = .ok c → rayDist (a * b) (c * RAY) ≤ HALF_RAY := by
  intro c hok
  rcases rayMulHalfUp_eq_ok a b h ▸ hok
  exact rayMulHalfUp_error a b

theorem rayMulHalfUp_exact_le_ok (a b : ℕ) (h : ¬ rayMulHalfUpReverts a b) :
    ∀ c, rayMulHalfUp a b = .ok c → a * b ≤ c * RAY + HALF_RAY := by
  intro c hok
  rcases rayMulHalfUp_eq_ok a b h ▸ hok
  exact rayMulHalfUp_exact_le a b

theorem rayMulHalfUp_exact_ge_ok (a b : ℕ) (h : ¬ rayMulHalfUpReverts a b) :
    ∀ c, rayMulHalfUp a b = .ok c → c * RAY ≤ a * b + HALF_RAY := by
  intro c hok
  rcases rayMulHalfUp_eq_ok a b h ▸ hok
  exact rayMulHalfUp_exact_ge a b

theorem rayMulDown_exact_le_ok (a b : ℕ) (h : ¬ rayMulReverts a b) :
    ∀ c, rayMulDown a b = .ok c → c * RAY ≤ a * b := by
  intro c hok
  rcases rayMulDown_eq_ok a b h ▸ hok
  exact rayMulDown_exact_le a b

theorem rayDivDown_eq_ok (a b : ℕ) (hb : b ≠ 0) (ha : a ≤ UINT256_MAX / RAY) :
    rayDivDown a b = .ok (Nat.rayDivDown a b) := by
  unfold rayDivDown
  have h : ¬ rayDivReverts a b := by
    dsimp [rayDivReverts]
    refine not_or_intro hb ?_
    exact Nat.not_lt.mpr ha
  rw [if_neg h]

theorem rayDivDown_exact_le_ok (a b : ℕ) (hb : b ≠ 0) (ha : a ≤ UINT256_MAX / RAY) :
    ∀ c, rayDivDown a b = .ok c → c * b ≤ a * RAY := by
  intro c hok
  rcases rayDivDown_eq_ok a b hb ha ▸ hok
  exact Nat.div_mul_le_self _ _

/-- On a successful EVM call, the result is within `1/(2·RAY)` of `decode a * decode b`. -/
theorem rayMulHalfUp_error_real_ok (a b : ℕ) (h : ¬ rayMulHalfUpReverts a b) :
    ∀ c, rayMulHalfUp a b = .ok c →
      |Real.decode a * Real.decode b - Real.decode c| ≤ (1 : ℝ) / (2 * Nat.RAY) := by
  intro c hok
  rcases rayMulHalfUp_eq_ok a b h ▸ hok
  exact Real.rayMulHalfUp_error a b

end WadRayMath.Evm
