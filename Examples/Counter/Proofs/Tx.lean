import Mathlib.Tactic.SplitIfs
import Examples.Counter.Contract

/-!
Counter `Tx.run` deltas.
-/

set_option linter.unusedSimpArgs false

open Lsc Counter

namespace Counter

variable (ctx : Ctx) (w : World)

namespace Proof

theorem increment_adds {w' : World}
    (h : Tx.run increment ctx w = .ok ((), w')) :
    w'.self.count = w.self.count + 1 := by
  simp [increment, Tx.HAddChecked.hAdd, Tx.run_addChecked] at h
  split_ifs at h
  cases h
  rfl

theorem incrementBy_adds (n : Nat) {w' : World}
    (h : Tx.run (incrementBy n) ctx w = .ok ((), w')) :
    w'.self.count = w.self.count + n := by
  simp [incrementBy, Tx.HAddChecked.hAdd, Tx.run_addChecked, Tx.run_require] at h
  split_ifs at h
  simp at h
  split_ifs at h
  cases h
  rfl

theorem decrement_saturates {w' : World}
    (h : Tx.run decrement ctx w = .ok ((), w')) :
    w'.self.count = if w.self.count = 0 then 0 else w.self.count - 1 := by
  simp [decrement, Tx.HSubChecked.hSub, Tx.run_subChecked] at h
  by_cases hz : w.self.count = 0
  · simp [hz] at h ⊢
    cases h
    rfl
  · simp [hz] at h ⊢
    split_ifs at h
    cases h
    rfl

theorem get_returns {n : Nat} {w' : World}
    (h : Tx.run Counter.get ctx w = .ok (n, w')) :
    n = w.self.count ∧ w' = w := by
  have hget : Tx.run Counter.get ctx w = .ok (w.self.count, w) := by
    simp [Counter.get]
  rw [hget] at h
  cases h
  exact ⟨rfl, rfl⟩

end Proof

end Counter
