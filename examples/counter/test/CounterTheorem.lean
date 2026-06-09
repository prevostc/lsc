import Counter
import CounterLemma
import Lsc.Prelude

/-- On success, pause sets `paused` to `true` and leaves `number` unchanged. -/
theorem pause_sets_paused (s s' : Counter.State) (h : (pause .run s) = .ok s') :
    s'.paused = true ∧ s'.number = s.number :=
  CounterLemma.pause_sets_paused s s' h

/-- On success, unpause clears `paused` and leaves `number` unchanged. -/
theorem unpause_clears_paused (s s' : Counter.State) (h : (unpause .run s) = .ok s') :
    s'.paused = false ∧ s'.number = s.number :=
  CounterLemma.unpause_clears_paused s s' h

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : (increment .run s) = .ok s') :
    s'.number = UInt256.addNat s.number 1 (CounterLemma.increment_run_no_overflow_when_unpaused s s' hp h) ∧
    s'.paused = s.paused := by
  have ⟨hn, hp'⟩ := CounterLemma.increment_increases_number_when_unpaused s s' hp h
  exact ⟨UInt256.eq_iff.mpr hn, hp'⟩

/-- When paused, increment is a no-op on state. -/
theorem increment_noop_when_paused (s s' : Counter.State) (hp : s.paused)
    (h : (increment .run s) = .ok s') :
    s' = s :=
  CounterLemma.increment_preserves_number_when_paused s s' hp h

/-- When unpaused, increment increases `number` by exactly 1 (full world). -/
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : (increment .run w) = Except.ok ((), w')) :
    Counter.view w' |>.number = UInt256.addNat (Counter.view w).number 1
      (CounterLemma.increment_run_no_overflow_world_when_unpaused w w' hp h) ∧
    Counter.view w' |>.paused = Counter.view w |>.paused := by
  have ⟨hn, hp'⟩ := CounterLemma.increment_increases_number_world_when_unpaused w w' hp h
  exact ⟨UInt256.eq_iff.mpr hn, hp'⟩
