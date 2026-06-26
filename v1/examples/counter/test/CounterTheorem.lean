import Counter
import CounterProofs
import LscV1.Prelude

open LscV1

/-- On success, pause sets `paused` to `true` and leaves `number` unchanged. -/
theorem pause_sets_paused (s s' : Counter.State) (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number :=
  CounterProofs.pause_sets_paused s s' h

/-- On success, unpause clears `paused` and leaves `number` unchanged. -/
theorem unpause_clears_paused (s s' : Counter.State) (h : runS unpause s = .ok ((), s')) :
    s'.paused = false ∧ s'.number = s.number :=
  CounterProofs.unpause_clears_paused s s' h

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterProofs.increment_increases_number_when_unpaused s s' hp h

/-- When paused, increment reverts with `.IsPausedError`. -/
theorem increment_reverts_when_paused (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) :=
  CounterProofs.increment_errors_when_paused s hp

/-- When unpaused, increment increases `number` by exactly 1 (full world). -/
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : increment w = Except.ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 ∧
    (Counter.view w').paused = (Counter.view w).paused :=
  CounterProofs.increment_increases_number_world_when_unpaused w w' hp h
