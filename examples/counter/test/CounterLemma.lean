import Counter
import Lsc.Prelude

open Lsc

-- ─── State-shaped proofs ──────────────────────────────────────────────────────

theorem pause_sets_paused
    (s s' : Counter.State)
    (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number := by
  simp [runS, pause] at h
  subst h; exact ⟨rfl, rfl⟩

theorem unpause_clears_paused
    (s s' : Counter.State)
    (h : runS unpause s = .ok ((), s')) :
    s'.paused = false ∧ s'.number = s.number := by
  simp [runS, unpause] at h
  subst h; exact ⟨rfl, rfl⟩

theorem increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, UInt256.addCheckedNat, hp, dif_pos hlt] at h
    subst h
    exact ⟨rfl, by simp [hp]⟩
  · exfalso
    simp [runS, increment, UInt256.addCheckedNat, hp, dif_neg hlt, ContractM.arithFail] at h

theorem increment_preserves_number_when_paused
    (s s' : Counter.State) (hp : s.paused)
    (h : runS increment s = .ok ((), s')) :
    s' = s := by
  simp [runS, increment, hp] at h
  cases s; simp_all

theorem increment_no_overflow_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s.number.val + 1 < 2 ^ 256 := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · exact hlt
  · exfalso
    simp [runS, increment, UInt256.addCheckedNat, hp, dif_neg hlt, ContractM.arithFail] at h

-- ─── World-shaped proofs ──────────────────────────────────────────────────────

theorem pause_sets_paused_world
    (w w' : World)
    (h : pause w = .ok ((), w')) :
    (Counter.view w').paused = true ∧
    (Counter.view w').number = (Counter.view w).number := by
  simp only [pause, ContractM.set, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp [Counter.view]

theorem unpause_clears_paused_world
    (w w' : World)
    (h : unpause w = .ok ((), w')) :
    (Counter.view w').paused = false ∧
    (Counter.view w').number = (Counter.view w).number := by
  simp only [unpause, ContractM.set, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp [Counter.view]
