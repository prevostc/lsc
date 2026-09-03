import Lsc.Lib.Math.Bounds
import Lsc.Lib.Math.SqrtAlgo
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace Lsc.Math.SqrtCorrect

open Lsc.Math.SqrtAlgo

def step (n x : Nat) : Nat := (x + n / x) / 2

def InScaleInterval (n aa p : Nat) : Prop :=
  aa * (p * p) ≤ n ∧ n < (aa + 1) * (p * p)

theorem inScaleInterval_initial (n : Nat) : InScaleInterval n n 1 := by
  simp [InScaleInterval]

theorem inScaleInterval_scale (n aa p k q : Nat)
    (h : InScaleInterval n aa p) (hq : q * q = 2 ^ k) :
    InScaleInterval n (aa / 2 ^ k) (p * q) := by
  have hd : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hloDiv : aa / 2 ^ k * 2 ^ k ≤ aa := Nat.div_mul_le_self aa (2 ^ k)
  have hiDiv : aa < (aa / 2 ^ k + 1) * 2 ^ k :=
    (Nat.div_lt_iff_lt_mul hd).1 (by omega)
  have hscale : (p * q) * (p * q) = 2 ^ k * (p * p) := by
    calc
      (p * q) * (p * q) = (q * q) * (p * p) := by ac_rfl
      _ = 2 ^ k * (p * p) := by rw [hq]
  constructor
  · rw [InScaleInterval] at h
    rw [hscale, ← Nat.mul_assoc]
    exact le_trans (Nat.mul_le_mul_right (p * p) hloDiv) h.1
  · rw [InScaleInterval] at h
    rw [hscale, ← Nat.mul_assoc]
    have hiDiv' : aa + 1 ≤ (aa / 2 ^ k + 1) * 2 ^ k := by omega
    exact lt_of_lt_of_le h.2 (Nat.mul_le_mul_right (p * p) hiDiv')

theorem inScaleInterval_magnitudeStep (n aa p k q : Nat)
    (h : InScaleInterval n aa p) (hq : q * q = 2 ^ k) :
    InScaleInterval n
      (magnitudeStep natOps (2 ^ k) k q (aa, p)).1
      (magnitudeStep natOps (2 ^ k) k q (aa, p)).2 := by
  by_cases htake : 2 ^ k ≤ aa
  · have hd : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hqpos : 0 < q := by
      by_contra hz
      have : q = 0 := by omega
      simp [this] at hq
      exact (Nat.ne_of_gt hd) hq.symm
    have hgt : aa > 2 ^ k - 1 := by omega
    have hfac : 1 + (q - 1) = q := by omega
    simpa [magnitudeStep, natOps, hgt, hfac] using
      inScaleInterval_scale n aa p k q h hq
  · have hgt : ¬aa > 2 ^ k - 1 := by
      have hd : 0 < 2 ^ k := Nat.pow_pos (by decide)
      omega
    simpa [magnitudeStep, natOps, hgt] using h

theorem magnitudeStep_fst_lt (aa p k q : Nat)
    (hbound : aa < (2 ^ k) * (2 ^ k)) :
    (magnitudeStep natOps (2 ^ k) k q (aa, p)).1 < 2 ^ k := by
  have hd : 0 < 2 ^ k := Nat.pow_pos (by decide)
  by_cases htake : 2 ^ k ≤ aa
  · have hgt : aa > 2 ^ k - 1 := by omega
    simp only [magnitudeStep, natOps, hgt, ↓reduceIte, id_eq]
    have hk : Nat.mul 1 k = k := Nat.one_mul k
    rw [hk]
    exact (Nat.div_lt_iff_lt_mul hd).2 hbound
  · have hgt : ¬aa > 2 ^ k - 1 := by omega
    simp only [magnitudeStep, natOps, hgt, ↓reduceIte, id_eq]
    have hk : Nat.mul 0 k = 0 := Nat.zero_mul k
    rw [hk, Nat.pow_zero, Nat.div_one]
    omega

theorem magnitudeStep_fst_pos (aa p k q : Nat) (haa : 0 < aa) :
    0 < (magnitudeStep natOps (2 ^ k) k q (aa, p)).1 := by
  have hd : 0 < 2 ^ k := Nat.pow_pos (by decide)
  by_cases htake : 2 ^ k ≤ aa
  · have hgt : aa > 2 ^ k - 1 := by omega
    simp only [magnitudeStep, natOps, hgt, ↓reduceIte, id_eq]
    have hk : Nat.mul 1 k = k := Nat.one_mul k
    rw [hk]
    exact Nat.div_pos htake hd
  · have hgt : ¬aa > 2 ^ k - 1 := by omega
    simpa [magnitudeStep, natOps, hgt] using haa

private theorem cross_le_square (s x : Nat) (hxs : x ≤ 2 * s) :
    (2 * s - x) * x ≤ s * s := by
  by_cases hsx : s ≤ x
  · let d := x - s
    have hd : d ≤ s := by omega
    have hx : x = s + d := by omega
    have hsub : 2 * s - x = s - d := by omega
    rw [hsub, hx, Nat.mul_add]
    calc
      (s - d) * s + (s - d) * d ≤ (s - d) * s + s * d := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.sub_le s d)) _
      _ = s * s := by
        rw [Nat.mul_comm (s - d) s, ← Nat.mul_add, Nat.sub_add_cancel hd]
  · have hxs' : x ≤ s := by omega
    let d := s - x
    have hd : d ≤ s := Nat.sub_le s x
    have hx : s = x + d := by omega
    have hx' : x = s - d := by omega
    have hsub : 2 * s - x = s + d := by omega
    rw [hsub, hx', Nat.add_mul]
    calc
      s * (s - d) + d * (s - d) ≤ s * (s - d) + d * s := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left d (Nat.sub_le s d)) _
      _ = s * s := by
        rw [Nat.mul_comm d s, ← Nat.mul_add, Nat.sub_add_cancel hd]

def dist (s x : Nat) : Nat := (x - s) + (s - x)

private theorem dist_sq_identity (s x : Nat) :
    dist s x * dist s x + 2 * x * s = x * x + s * s := by
  by_cases hsx : s ≤ x
  · simp only [dist, Nat.sub_eq_zero_of_le hsx, Nat.add_zero]
    let d := x - s
    have hx : x = s + d := by omega
    rw [hx, Nat.add_sub_cancel_left]
    simp only [Nat.succ_mul, Nat.add_mul, Nat.mul_add]
    rw [Nat.mul_comm d s]
    omega
  · have hxs : x ≤ s := by omega
    simp only [dist, Nat.sub_eq_zero_of_le hxs, Nat.zero_add]
    let d := s - x
    have hx : s = x + d := by omega
    rw [hx, Nat.add_sub_cancel_left]
    simp only [Nat.succ_mul, Nat.add_mul, Nat.mul_add]
    rw [Nat.mul_comm d x]
    omega

theorem step_bounds (n s x : Nat)
    (hsq : s * s ≤ n) (hlt : n < (s + 1) * (s + 1))
    (hx : 0 < x) :
    s ≤ step n x ∧ 2 * x * (step n x - s) ≤ dist s x * dist s x + 2 * s := by
  have hn : n ≤ s * s + 2 * s := by grind
  have hdivmul : n / x * x ≤ n := Nat.div_mul_le_self n x
  have htwostep : 2 * step n x ≤ x + n / x := by
    simpa [step, Nat.mul_comm] using Nat.div_mul_le_self (x + n / x) 2
  have hlower : 2 * s ≤ x + n / x := by
    by_cases h2 : 2 * s ≤ x
    · exact le_trans h2 (Nat.le_add_right x (n / x))
    · have hm : (2 * s - x) * x ≤ n :=
        le_trans (cross_le_square s x (Nat.le_of_not_ge h2)) hsq
      have hd : 2 * s - x ≤ n / x := (Nat.le_div_iff_mul_le hx).2 hm
      omega
  have hstep : s ≤ step n x := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    simpa [Nat.mul_comm] using hlower
  constructor
  · exact hstep
  · have hm := Nat.mul_le_mul_right x htwostep
    have hraw : 2 * x * step n x ≤ x * x + s * s + 2 * s := by
      calc
        2 * x * step n x = (2 * step n x) * x := by
          simp only [Nat.mul_assoc, Nat.mul_comm]
        _ ≤ (x + n / x) * x := hm
        _ = x * x + (n / x) * x := by rw [Nat.add_mul]
        _ ≤ x * x + n := Nat.add_le_add_left hdivmul _
        _ ≤ x * x + (s * s + 2 * s) := Nat.add_le_add_left hn _
        _ = x * x + s * s + 2 * s := by omega
    apply Nat.le_of_add_le_add_right
    calc
      2 * x * (step n x - s) + 2 * x * s = 2 * x * step n x := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hstep]
      _ ≤ x * x + s * s + 2 * s := hraw
      _ = dist s x * dist s x + 2 * s + 2 * x * s := by
        symm
        calc
          dist s x * dist s x + 2 * s + 2 * x * s =
              (dist s x * dist s x + 2 * x * s) + 2 * s := by omega
          _ = x * x + s * s + 2 * s := by rw [dist_sq_identity]

theorem magnitudeInit_band (n : Nat) (hn : 0 < n) (hu : n < 2 ^ 256) :
    let state := magnitudeInit natOps n
    state.2 * state.2 ≤ n ∧
      n < (2 * state.2) * (2 * state.2) ∧
      0 < state.1 ∧ state.1 < 16 := by
  let s₀ : Nat × Nat := (n, 1)
  let s₁ := magnitudeStep natOps (2 ^ 128) 128 (2 ^ 64) s₀
  let s₂ := magnitudeStep natOps (2 ^ 64) 64 (2 ^ 32) s₁
  let s₃ := magnitudeStep natOps (2 ^ 32) 32 (2 ^ 16) s₂
  let s₄ := magnitudeStep natOps (2 ^ 16) 16 (2 ^ 8) s₃
  let s₅ := magnitudeStep natOps (2 ^ 8) 8 (2 ^ 4) s₄
  let s₆ := magnitudeStep natOps (2 ^ 4) 4 (2 ^ 2) s₅
  have hI₀ : InScaleInterval n s₀.1 s₀.2 := by
    simpa [s₀] using inScaleInterval_initial n
  have hI₁ : InScaleInterval n s₁.1 s₁.2 := by
    exact inScaleInterval_magnitudeStep n s₀.1 s₀.2 128 (2 ^ 64) hI₀ (by decide)
  have hB₁ : s₁.1 < 2 ^ 128 := by
    apply magnitudeStep_fst_lt s₀.1 s₀.2 128 (2 ^ 64)
    simpa [s₀, ← Nat.pow_add] using hu
  have hP₁ : 0 < s₁.1 :=
    magnitudeStep_fst_pos s₀.1 s₀.2 128 (2 ^ 64) (by simpa [s₀] using hn)
  have hI₂ : InScaleInterval n s₂.1 s₂.2 :=
    inScaleInterval_magnitudeStep n s₁.1 s₁.2 64 (2 ^ 32) hI₁ (by decide)
  have hB₂ : s₂.1 < 2 ^ 64 :=
    magnitudeStep_fst_lt s₁.1 s₁.2 64 (2 ^ 32) (by
      simpa [← Nat.pow_add] using hB₁)
  have hP₂ : 0 < s₂.1 := magnitudeStep_fst_pos s₁.1 s₁.2 64 (2 ^ 32) hP₁
  have hI₃ : InScaleInterval n s₃.1 s₃.2 :=
    inScaleInterval_magnitudeStep n s₂.1 s₂.2 32 (2 ^ 16) hI₂ (by decide)
  have hB₃ : s₃.1 < 2 ^ 32 :=
    magnitudeStep_fst_lt s₂.1 s₂.2 32 (2 ^ 16) (by
      simpa [← Nat.pow_add] using hB₂)
  have hP₃ : 0 < s₃.1 := magnitudeStep_fst_pos s₂.1 s₂.2 32 (2 ^ 16) hP₂
  have hI₄ : InScaleInterval n s₄.1 s₄.2 :=
    inScaleInterval_magnitudeStep n s₃.1 s₃.2 16 (2 ^ 8) hI₃ (by decide)
  have hB₄ : s₄.1 < 2 ^ 16 :=
    magnitudeStep_fst_lt s₃.1 s₃.2 16 (2 ^ 8) (by
      simpa [← Nat.pow_add] using hB₃)
  have hP₄ : 0 < s₄.1 := magnitudeStep_fst_pos s₃.1 s₃.2 16 (2 ^ 8) hP₃
  have hI₅ : InScaleInterval n s₅.1 s₅.2 :=
    inScaleInterval_magnitudeStep n s₄.1 s₄.2 8 (2 ^ 4) hI₄ (by decide)
  have hB₅ : s₅.1 < 2 ^ 8 :=
    magnitudeStep_fst_lt s₄.1 s₄.2 8 (2 ^ 4) (by
      simpa [← Nat.pow_add] using hB₄)
  have hP₅ : 0 < s₅.1 := magnitudeStep_fst_pos s₄.1 s₄.2 8 (2 ^ 4) hP₄
  have hI₆ : InScaleInterval n s₆.1 s₆.2 :=
    inScaleInterval_magnitudeStep n s₅.1 s₅.2 4 (2 ^ 2) hI₅ (by decide)
  have hB₆ : s₆.1 < 16 := by
    simpa using magnitudeStep_fst_lt s₅.1 s₅.2 4 (2 ^ 2) (by
      simpa [← Nat.pow_add] using hB₅)
  have hP₆ : 0 < s₆.1 := magnitudeStep_fst_pos s₅.1 s₅.2 4 (2 ^ 2) hP₅
  change
    let state := magnitudeStep natOps (2 ^ 2) 0 2 s₆
    state.2 * state.2 ≤ n ∧
      n < (2 * state.2) * (2 * state.2) ∧
      0 < state.1 ∧ state.1 < 16
  dsimp only
  rw [InScaleInterval] at hI₆
  by_cases htake : 4 ≤ s₆.1
  · have hgt : s₆.1 > 2 ^ 2 - 1 := by omega
    have hzero : Nat.mul 1 0 = 0 := Nat.mul_zero 1
    have hfac : Nat.add 1 (Nat.mul 1 (2 - 1)) = 2 := by decide
    simp only [magnitudeStep, natOps, hgt, ↓reduceIte, id_eq, hzero, hfac,
      Nat.pow_zero, Nat.div_one]
    have hsq : (s₆.2 * 2) * (s₆.2 * 2) = 4 * (s₆.2 * s₆.2) := by
      have h4 : (4 : Nat) = 2 * 2 := rfl
      rw [h4]
      ac_rfl
    have hupper :
        (2 * (s₆.2 * 2)) * (2 * (s₆.2 * 2)) = 16 * (s₆.2 * s₆.2) := by
      have h16 : (16 : Nat) = (2 * 2) * (2 * 2) := rfl
      rw [h16]
      ac_rfl
    constructor
    · change (s₆.2 * 2) * (s₆.2 * 2) ≤ n
      rw [hsq]
      exact le_trans (Nat.mul_le_mul_right (s₆.2 * s₆.2) htake) hI₆.1
    constructor
    · change n < (2 * (s₆.2 * 2)) * (2 * (s₆.2 * 2))
      rw [hupper]
      have : s₆.1 + 1 ≤ 16 := by omega
      exact lt_of_lt_of_le hI₆.2 (Nat.mul_le_mul_right _ this)
    · exact ⟨hP₆, hB₆⟩
  · have hgt : ¬s₆.1 > 2 ^ 2 - 1 := by omega
    have hzero : Nat.mul 0 0 = 0 := Nat.mul_zero 0
    have hfac : Nat.add 1 (Nat.mul 0 (2 - 1)) = 1 := by decide
    simp only [magnitudeStep, natOps, hgt, ↓reduceIte, id_eq, hzero, hfac,
      Nat.pow_zero, Nat.div_one]
    have hp1 : Nat.mul s₆.2 1 = s₆.2 := Nat.mul_one s₆.2
    rw [hp1]
    have hupper :
        (2 * s₆.2) * (2 * s₆.2) = 4 * (s₆.2 * s₆.2) := by
      have h4 : (4 : Nat) = 2 * 2 := rfl
      rw [h4]
      ac_rfl
    constructor
    · change s₆.2 * s₆.2 ≤ n
      have hlo := Nat.mul_le_mul_right (s₆.2 * s₆.2) (by omega : 1 ≤ s₆.1)
      exact le_trans (by simpa using hlo) hI₆.1
    constructor
    · change n < (2 * s₆.2) * (2 * s₆.2)
      rw [hupper]
      have : s₆.1 + 1 ≤ 4 := by omega
      exact lt_of_lt_of_le hI₆.2 (Nat.mul_le_mul_right _ this)
    · exact ⟨hP₆, hB₆⟩

theorem refined_init_error_of_band (n p : Nat)
    (hp : 0 < p) (hlo : p * p ≤ n) (hi : n < (2 * p) * (2 * p)) :
    let x₀ := 3 * p / 2
    p ≤ Nat.sqrt n ∧ Nat.sqrt n < 2 * p ∧
      0 < x₀ ∧ dist (Nat.sqrt n) x₀ ≤ (p + 1) / 2 := by
  dsimp
  have hslo : p ≤ Nat.sqrt n := Nat.le_sqrt.mpr hlo
  have hshi : Nat.sqrt n < 2 * p := Nat.sqrt_lt.mpr hi
  have hxlo : p ≤ 3 * p / 2 := by omega
  have hxhi : 3 * p / 2 ≤ p + p / 2 := by omega
  have hxp : 0 < 3 * p / 2 := lt_of_lt_of_le hp hxlo
  constructor
  · exact hslo
  constructor
  · exact hshi
  constructor
  · exact hxp
  · simp only [dist]
    omega

private theorem initFromMagnitude_natOps (state : Nat × Nat) :
    initFromMagnitude natOps state = 3 * state.2 / 2 := by
  rfl

theorem init_natOps_eq_refined_scale (n : Nat) :
    init natOps n = 3 * (magnitudeInit natOps n).2 / 2 :=
  initFromMagnitude_natOps (magnitudeInit natOps n)

theorem sixSteps_natOps_eq_steps (n x₀ : Nat) :
    sixSteps natOps n x₀ =
      step n (step n (step n (step n (step n (step n x₀))))) := by
  rfl

theorem magnitudeInit_error (n : Nat) (hn : 0 < n) (hu : n < 2 ^ 256) :
    let state := magnitudeInit natOps n
    let p := state.2
    p ≤ Nat.sqrt n ∧ Nat.sqrt n < 2 * p ∧
      0 < init natOps n ∧
      dist (Nat.sqrt n) (init natOps n) ≤ (p + 1) / 2 := by
  dsimp
  have hb := magnitudeInit_band n hn hu
  have hi := refined_init_error_of_band n (magnitudeInit natOps n).2
    (by
      by_contra hp
      have hp0 : (magnitudeInit natOps n).2 = 0 := by omega
      have hbUpper :
          n < (2 * (magnitudeInit natOps n).2) *
            (2 * (magnitudeInit natOps n).2) := by
        simpa only using hb.2.1
      rw [hp0] at hbUpper
      simp at hbUpper)
    hb.1 hb.2.1
  rw [init_natOps_eq_refined_scale]
  exact hi

private theorem floorDiv_add_two_bounds (n d : Nat) (hd : 0 < d) :
    n + d + 1 ≤ d * (n / d + 2) ∧ d * (n / d + 2) ≤ n + 2 * d := by
  have hlo : n < d * (n / d + 1) := by
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (n / d))
  have hhi : d * (n / d) ≤ n := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n d
  constructor
  · calc
      n + d + 1 = (n + 1) + d := by omega
      _ ≤ d * (n / d + 1) + d :=
        Nat.add_le_add_right (Nat.succ_le_of_lt hlo) d
      _ = d * (n / d + 2) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  · calc
      d * (n / d + 2) = d * (n / d) + 2 * d := by
        simp only [Nat.mul_add]
        omega
      _ ≤ n + 2 * d := Nat.add_le_add_right hhi (2 * d)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Integer-aware error budgets. The additive two units absorb the truncation in every
    division while the denominators retain enough quadratic-convergence margin for u256. -/
theorem u256_newton_budgets (p s x₀ : Nat)
    (hp : 4 ≤ p) (hpMax : p < 2 ^ 128)
    (hps : p ≤ s) (hsp : s < 2 * p)
    (hx₀ : x₀ = 3 * p / 2) :
    let D₀ := (p + 1) / 2
    let D₁ := p / 11 + 2
    let D₂ := p / 240 + 2
    let D₃ := p / 100000 + 2
    let D₄ := p / 15000000000 + 2
    let D₅ := p / 400000000000000000000 + 2
    D₀ * D₀ + 2 * s < 2 * x₀ * (D₁ + 1) ∧
      D₁ * D₁ < 2 * s * D₂ ∧
      D₂ * D₂ < 2 * s * D₃ ∧
      D₃ * D₃ < 2 * s * D₄ ∧
      D₄ * D₄ < 2 * s * D₅ ∧
      D₅ * D₅ < 2 * s := by
  dsimp
  have hD₀ : 2 * ((p + 1) / 2) ≤ p + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (p + 1) 2
  have hD₀sq := Nat.mul_le_mul hD₀ hD₀
  have hx₀lo : 3 * p - 1 ≤ 2 * x₀ := by
    subst x₀
    omega
  have hD₁lo : p + 23 ≤ 11 * (p / 11 + 2 + 1) := by
    have h := (floorDiv_add_two_bounds p 11 (by decide)).1
    calc
      p + 23 = (p + 11 + 1) + 11 := by omega
      _ ≤ 11 * (p / 11 + 2) + 11 := Nat.add_le_add_right h 11
      _ = 11 * (p / 11 + 2 + 1) := by omega
  have hfirstProduct := Nat.mul_le_mul hx₀lo hD₁lo
  constructor
  · have hleft :
        44 * (((p + 1) / 2) * ((p + 1) / 2) + 2 * s) <
          11 * ((p + 1) * (p + 1)) + 176 * p := by
      nlinarith
    have hmiddle :
        11 * ((p + 1) * (p + 1)) + 176 * p <
          4 * ((3 * p - 1) * (p + 23)) := by
      have hsubeq : 3 * p - 1 + 1 = 3 * p :=
        Nat.sub_add_cancel (by omega)
      nlinarith
    have hright := Nat.mul_le_mul_left 4 hfirstProduct
    nlinarith
  have h11 : 11 * (p / 11 + 2) ≤ p + 22 :=
    (floorDiv_add_two_bounds p 11 (by decide)).2
  have h11sq := Nat.mul_le_mul h11 h11
  have h240 : p + 241 ≤ 240 * (p / 240 + 2) :=
    (floorDiv_add_two_bounds p 240 (by decide)).1
  have hp240 := Nat.mul_le_mul hps h240
  constructor
  · nlinarith
  have h240up : 240 * (p / 240 + 2) ≤ p + 480 :=
    (floorDiv_add_two_bounds p 240 (by decide)).2
  have h240sq := Nat.mul_le_mul h240up h240up
  have h100k : p + 100001 ≤ 100000 * (p / 100000 + 2) :=
    (floorDiv_add_two_bounds p 100000 (by decide)).1
  have hp100k := Nat.mul_le_mul hps h100k
  constructor
  · nlinarith
  have h100kup : 100000 * (p / 100000 + 2) ≤ p + 200000 :=
    (floorDiv_add_two_bounds p 100000 (by decide)).2
  have h100ksq := Nat.mul_le_mul h100kup h100kup
  have h15b : p + 15000000001 ≤ 15000000000 * (p / 15000000000 + 2) :=
    (floorDiv_add_two_bounds p 15000000000 (by decide)).1
  have hp15b := Nat.mul_le_mul hps h15b
  constructor
  · nlinarith
  have h15bup : 15000000000 * (p / 15000000000 + 2) ≤ p + 30000000000 :=
    (floorDiv_add_two_bounds p 15000000000 (by decide)).2
  have h15bsq := Nat.mul_le_mul h15bup h15bup
  have h400e : p + 400000000000000000001 ≤
      400000000000000000000 * (p / 400000000000000000000 + 2) :=
    (floorDiv_add_two_bounds p 400000000000000000000 (by decide)).1
  have hp400e := Nat.mul_le_mul hps h400e
  constructor
  · nlinarith
  have h400eup : 400000000000000000000 *
      (p / 400000000000000000000 + 2) ≤ p + 800000000000000000000 :=
    (floorDiv_add_two_bounds p 400000000000000000000 (by decide)).2
  have h400esq := Nat.mul_le_mul h400eup h400eup
  have hpSq : p * p < (2 ^ 128) * p :=
    Nat.mul_lt_mul_of_pos_right hpMax (by omega)
  have hconst :
      2 ^ 128 + 4 * 400000000000000000000 +
          400000000000000000000 * 400000000000000000000 <
        2 * (400000000000000000000 * 400000000000000000000) := by
    norm_num
  · nlinarith

theorem step_error_le_of_budget (n s x D K : Nat)
    (hsq : s * s ≤ n) (hlt : n < (s + 1) * (s + 1))
    (hx : 0 < x) (hD : dist s x ≤ D)
    (hbudget : D * D + 2 * s < 2 * x * (K + 1)) :
    s ≤ step n x ∧ step n x - s ≤ K := by
  have hb := step_bounds n s x hsq hlt hx
  have hdist : dist s x * dist s x ≤ D * D :=
    Nat.mul_le_mul hD hD
  have herr : 2 * x * (step n x - s) < 2 * x * (K + 1) :=
    lt_of_le_of_lt hb.2 (lt_of_le_of_lt (Nat.add_le_add_right hdist (2 * s)) hbudget)
  have hpos : 0 < 2 * x := Nat.mul_pos (by decide) hx
  have hlt' : step n x - s < K + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2 * x)
    simpa only [← Nat.mul_assoc] using herr
  exact ⟨hb.1, by omega⟩

theorem step_error_le_of_square (n s x D K : Nat)
    (hsq : s * s ≤ n) (hlt : n < (s + 1) * (s + 1))
    (hs : 0 < s) (hsx : s ≤ x) (hD : x - s ≤ D)
    (hsquare : D * D < 2 * s * K) :
    s ≤ step n x ∧ step n x - s ≤ K := by
  have hx : 0 < x := lt_of_lt_of_le hs hsx
  apply step_error_le_of_budget n s x D K hsq hlt hx
  · simp [dist, Nat.sub_eq_zero_of_le hsx, hD]
  · calc
      D * D + 2 * s < 2 * s * K + 2 * s :=
        Nat.add_lt_add_right hsquare (2 * s)
      _ = 2 * s * (K + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ 2 * x * (K + 1) := by
        exact Nat.mul_le_mul_right (K + 1) (Nat.mul_le_mul_left 2 hsx)

/-- Six rounded Newton steps turn an explicit analytic error chain into a one-unit estimate. -/
theorem six_steps_error_le_one (n s x₀ D₀ D₁ D₂ D₃ D₄ D₅ : Nat)
    (hsq : s * s ≤ n) (hlt : n < (s + 1) * (s + 1))
    (hs : 0 < s) (hx₀ : 0 < x₀) (hD₀ : dist s x₀ ≤ D₀)
    (hfirst : D₀ * D₀ + 2 * s < 2 * x₀ * (D₁ + 1))
    (h12 : D₁ * D₁ < 2 * s * D₂)
    (h23 : D₂ * D₂ < 2 * s * D₃)
    (h34 : D₃ * D₃ < 2 * s * D₄)
    (h45 : D₄ * D₄ < 2 * s * D₅)
    (h5 : D₅ * D₅ < 2 * s) :
    let x₁ := step n x₀
    let x₂ := step n x₁
    let x₃ := step n x₂
    let x₄ := step n x₃
    let x₅ := step n x₄
    let x₆ := step n x₅
    s ≤ x₆ ∧ x₆ ≤ s + 1 := by
  dsimp
  have h1 := step_error_le_of_budget n s x₀ D₀ D₁ hsq hlt hx₀ hD₀ hfirst
  have h2 := step_error_le_of_square n s (step n x₀) D₁ D₂ hsq hlt hs h1.1 h1.2 h12
  have h3 := step_error_le_of_square n s (step n (step n x₀)) D₂ D₃
    hsq hlt hs h2.1 h2.2 h23
  have h4 := step_error_le_of_square n s (step n (step n (step n x₀))) D₃ D₄
    hsq hlt hs h3.1 h3.2 h34
  have h5' := step_error_le_of_square n s (step n (step n (step n (step n x₀)))) D₄ D₅
    hsq hlt hs h4.1 h4.2 h45
  have h6 := step_error_le_of_square n s
    (step n (step n (step n (step n (step n x₀))))) D₅ 1
    hsq hlt hs h5'.1 h5'.2 (by simpa using h5)
  exact ⟨h6.1, by omega⟩

theorem floor_correction_eq (n s x : Nat)
    (hsq : s * s ≤ n) (hlt : n < (s + 1) * (s + 1))
    (hs : 0 < s) (hlo : s ≤ x) (hi : x ≤ s + 1) :
    x - (if x > n / x then 1 else 0) = s := by
  have hx : x = s ∨ x = s + 1 := by omega
  rcases hx with hx | hx
  · rw [hx]
    have hdiv : s ≤ n / s := (Nat.le_div_iff_mul_le hs).2 hsq
    simp [Nat.not_lt.mpr hdiv]
  · rw [hx]
    have hs1 : 0 < s + 1 := by omega
    have hdiv : n / (s + 1) < s + 1 :=
      (Nat.div_lt_iff_lt_mul hs1).2 hlt
    simp [hdiv]

/-- Once the six-step pre-fixpoint is within one of floor sqrt, the algorithm's final
    correction returns exactly `Nat.sqrt`. -/
theorem sqrtNat_eq_natSqrt_of_preFix_bounds (n : Nat)
    (hlo : Nat.sqrt n ≤ preFix natOps n)
    (hi : preFix natOps n ≤ Nat.sqrt n + 1) :
    sqrtNat n = Nat.sqrt n := by
  by_cases hn : n = 0
  · subst n
    native_decide
  · have hs : 0 < Nat.sqrt n := (Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hn)
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    rw [sqrtNat, sqrt_eq_floorFix, floorFix]
    change
      preFix natOps n - (if preFix natOps n > n / preFix natOps n then 1 else 0) =
        Nat.sqrt n
    exact floor_correction_eq n (Nat.sqrt n) (preFix natOps n) hsq hlt hs hlo hi

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Analytic correctness on the nontrivial initializer bands. -/
private theorem sqrtNat_eq_natSqrt_of_scale_ge_four (n : Nat)
    (hu : n < 2 ^ 256) (hn : 0 < n)
    (hp4 : 4 ≤ (magnitudeInit natOps n).2) :
    sqrtNat n = Nat.sqrt n := by
  let p := (magnitudeInit natOps n).2
  have hb := magnitudeInit_band n hn hu
  have hm := magnitudeInit_error n hn hu
  dsimp only at hb hm
  change p * p ≤ n ∧ n < (2 * p) * (2 * p) ∧
    0 < (magnitudeInit natOps n).1 ∧ (magnitudeInit natOps n).1 < 16 at hb
  change p ≤ Nat.sqrt n ∧ Nat.sqrt n < 2 * p ∧
    0 < init natOps n ∧ dist (Nat.sqrt n) (init natOps n) ≤ (p + 1) / 2 at hm
  have hp : 0 < p := by
    by_contra hp0
    have : p = 0 := by omega
    rw [this] at hb
    simp at hb
  have hsMax : Nat.sqrt n < 2 ^ 128 := by
    apply Nat.sqrt_lt.mpr
    simpa [← Nat.pow_add] using hu
  have hpMax : p < 2 ^ 128 := lt_of_le_of_lt hm.1 hsMax
  have hinit : init natOps n = 3 * p / 2 := by
    simpa [p] using init_natOps_eq_refined_scale n
  have hbud := u256_newton_budgets p (Nat.sqrt n) (init natOps n)
    (by simpa [p] using hp4) hpMax hm.1 hm.2.1 hinit
  dsimp only at hbud
  have hconv := six_steps_error_le_one n (Nat.sqrt n) (init natOps n)
    ((p + 1) / 2)
    (p / 11 + 2)
    (p / 240 + 2)
    (p / 100000 + 2)
    (p / 15000000000 + 2)
    (p / 400000000000000000000 + 2)
    (Nat.sqrt_le n) (Nat.lt_succ_sqrt n)
    ((Nat.sqrt_pos).2 hn) hm.2.2.1 hm.2.2.2
    hbud.1 hbud.2.1 hbud.2.2.1 hbud.2.2.2.1 hbud.2.2.2.2.1 hbud.2.2.2.2.2
  have hpre :
      Nat.sqrt n ≤ preFix natOps n ∧ preFix natOps n ≤ Nat.sqrt n + 1 := by
    rw [preFix, sixSteps_natOps_eq_steps]
    exact hconv
  apply sqrtNat_eq_natSqrt_of_preFix_bounds
  · exact hpre.1
  · exact hpre.2

set_option maxRecDepth 10000 in
private theorem sqrtNat_eq_natSqrt_lt36 (n : Nat) (hn : n < 36) :
    sqrtNat n = Nat.sqrt n := by
  interval_cases n <;> native_decide

/-- The shared six-step implementation computes floor square root for every u256 input. -/
theorem sqrtNat_eq_natSqrt_u256 (n : Nat) (hu : n < 2 ^ 256) :
    sqrtNat n = Nat.sqrt n := by
  by_cases hn0 : n = 0
  · exact sqrtNat_eq_natSqrt_lt36 n (by omega)
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hp4 : 4 ≤ (magnitudeInit natOps n).2
  · exact sqrtNat_eq_natSqrt_of_scale_ge_four n hu hn hp4
  · have hb := magnitudeInit_band n hn hu
    dsimp only at hb
    have hpSmall : (magnitudeInit natOps n).2 ≤ 3 := by omega
    have hnSmall : n < 36 := by
      calc
        n < (2 * (magnitudeInit natOps n).2) *
            (2 * (magnitudeInit natOps n).2) := hb.2.1
        _ ≤ 6 * 6 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpSmall)
          (Nat.mul_le_mul_left 2 hpSmall)
        _ = 36 := by decide
    exact sqrtNat_eq_natSqrt_lt36 n hnSmall

end Lsc.Math.SqrtCorrect
