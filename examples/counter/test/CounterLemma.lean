import Counter
import Lsc.Prelude

open Lsc

namespace CounterLemma

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

theorem increment_run_no_overflow_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s.number.val + 1 < 2 ^ 256 := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · exact hlt
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h

theorem increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt] at h
    subst h
    exact ⟨rfl, (Bool.not_iff_eq_false).mp hp |>.symm⟩
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h

theorem increment_errors_when_paused
    (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) := by
  have hpt : s.paused = true := hp
  simp [runS, increment, failWhen, hpt, ContractM.revert, ContractM.revertFail]

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

-- Overflow is impossible when increment succeeds; proved before the
-- number lemma so it can be referenced there.
theorem increment_run_no_overflow_world_when_unpaused
    (w w' : World) (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w).number.val + 1 < 2 ^ 256 := by
  by_cases hlt : (Counter.view w).number.val + 1 < 2 ^ 256
  · exact hlt
  · exfalso
    have hlt' : ¬(FromWord.fromWord (w.getStorage defaultSelf 0) : UInt256).val + 1 < 2 ^ 256 :=
      fun hlt0 => hlt (by simp [Counter.view]; exact hlt0)
    simp [Counter.view] at hp
    simp [increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt',
          ContractM.arithFail] at h

theorem increment_increases_number_world_when_unpaused
    (w w' : World) (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 ∧
    (Counter.view w').paused = (Counter.view w).paused := by
  have hlt := increment_run_no_overflow_world_when_unpaused w w' hp h
  have hlt' : (FromWord.fromWord (w.getStorage defaultSelf 0) : UInt256).val + 1 < 2 ^ 256 := by
    simp [Counter.view] at hlt; exact hlt
  simp [Counter.view] at hp
  simp [increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt'] at h
  subst h
  refine ⟨?_, ?_⟩
  · simp [Counter.view, fromWord_toWord_UInt256]
    exact rfl
  · simp [Counter.view, show (0 : Nat) ≠ 1 from by decide]

end CounterLemma
