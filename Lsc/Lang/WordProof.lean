import Lsc.Lang.Word

/-!
Proofs of the checked-word theorems. Statements live in `WordTheorems.lean`.
-/

namespace Lsc.Proof

variable {S X E ε : Type}

theorem addChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.addChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a + b ∧ a + b < wordBound ∧ w' = w := by
  simp [Tx.run_addChecked] at h
  by_cases hfit : a + b < wordBound
  · simp [hfit] at h
    exact ⟨h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem subChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.subChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a - b ∧ b ≤ a ∧ w' = w := by
  simp [Tx.run_subChecked] at h
  by_cases hle : b ≤ a
  · simp [hle] at h
    exact ⟨h.1.symm, hle, h.2.symm⟩
  · simp [hle] at h

theorem mulChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a * b ∧ a * b < wordBound ∧ w' = w := by
  simp [Tx.run_mulChecked] at h
  by_cases hfit : a * b < wordBound
  · simp [hfit] at h
    exact ⟨h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem divChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.divChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a / b ∧ b ≠ 0 ∧ w' = w := by
  simp [Tx.run_divChecked] at h
  by_cases hb : b = 0
  · simp [hb] at h
  · simp [hb] at h
    exact ⟨h.1.symm, hb, h.2.symm⟩

theorem mulDivDown_ok {a b c : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      .ok (q, w')) :
    c ≠ 0 ∧ a * b < wordBound ∧ q = a * b / c ∧ q * c ≤ a * b ∧
      a * b - q * c < c ∧ w' = w := by
  simp [Tx.run_mulDivDown] at h
  by_cases hc0 : c = 0
  · simp [hc0] at h
  · by_cases hfit : a * b < wordBound
    · simp [hc0, hfit] at h
      have hc : 0 < c := Nat.pos_of_ne_zero hc0
      have hq : q = a * b / c := h.1.symm
      have hw : w' = w := h.2.symm
      refine ⟨hc0, hfit, hq, ?_, ?_, hw⟩
      · simpa [hq, Nat.mul_comm] using Nat.mul_div_le (a * b) c
      · have : a * b % c = a * b - (a * b / c) * c := by
          have hdecomp := Nat.div_add_mod (a * b) c
          have : (a * b / c) * c = c * (a * b / c) := Nat.mul_comm _ _
          omega
        simpa [hq, this] using Nat.mod_lt (a * b) hc
    · simp [hc0, hfit] at h

theorem mulDivUp_ok {a b c : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      .ok (q, w')) :
    c ≠ 0 ∧ a * b < wordBound ∧
      q = a * b / c + (if a * b % c = 0 then 0 else 1) ∧ a * b ≤ q * c ∧ w' = w := by
  simp [Tx.run_mulDivUp] at h
  by_cases hc0 : c = 0
  · simp [hc0] at h
  · by_cases hfit : a * b < wordBound
    · simp [hc0, hfit] at h
      have hq : q = a * b / c + (if a * b % c = 0 then 0 else 1) := h.1.symm
      have hw : w' = w := h.2.symm
      refine ⟨hc0, hfit, hq, ?_, hw⟩
      by_cases hmod : a * b % c = 0
      · have hdecomp := Nat.div_add_mod (a * b) c
        simp [hmod] at hdecomp
        have hcomm : (a * b / c) * c = c * (a * b / c) := Nat.mul_comm _ _
        have : q * c = a * b := by
          simp [hq, hmod, hcomm, hdecomp]
        exact Nat.le_of_eq this.symm
      · have hpos : 0 < c := Nat.pos_of_ne_zero hc0
        have hmodlt : a * b % c < c := Nat.mod_lt _ hpos
        have hdecomp : a * b = c * (a * b / c) + a * b % c :=
          (Nat.div_add_mod (a * b) c).symm
        have hcomm : (a * b / c) * c = c * (a * b / c) := Nat.mul_comm _ _
        have hq' : q * c = (a * b / c + 1) * c := by simp [hq, hmod]
        rw [hq', Nat.add_mul, Nat.one_mul, hcomm]
        exact Nat.le_trans (Nat.le_of_eq hdecomp)
          (Nat.add_le_add_left (Nat.le_of_lt hmodlt) _)
    · simp [hc0, hfit] at h

theorem pow10_ok {d : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.pow10 (S := S) (X := X) (E := E) (ε := ε) d) ctx w = .ok (q, w')) :
    d ≤ Tx.pow10Max ∧ q = 10 ^ d ∧ w' = w := by
  simp [Tx.run_pow10] at h
  by_cases hbig : d > Tx.pow10Max
  · simp [hbig] at h
  · simp [hbig] at h
    exact ⟨Nat.le_of_not_gt hbig, h.1.symm, h.2.symm⟩

theorem rescale_id {d : Nat} {r : Rounding} {a : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.rescale (S := S) (X := X) (E := E) (ε := ε) d d r a) ctx w =
      .ok (q, w')) :
    q = a ∧ w' = w := by
  unfold Tx.rescale at h
  simp at h
  exact ⟨h.1.symm, h.2.symm⟩

end Lsc.Proof
