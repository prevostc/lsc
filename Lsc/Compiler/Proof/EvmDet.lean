import EvmSemantics.EVM.BigStep
import EvmSemantics.EVM.StepDeterminism

/-!
Halted EVM traces are unique: `Steps` is the RTC of a deterministic `Step`,
and a done frame (`halt ≠ .Running`, empty call stack) has no successor
(`Step.not_from_done`). Out-of-gas is a halt kind, so this lemma still
applies; it does not by itself say the program ran to a Yul-predicted halt.
-/

namespace Lsc.Compiler

open EvmSemantics.EVM

/-- Top-level execution is finished: the active frame halted and no caller
remains to resume. Same stuckness condition as `State.isDone` / `Eval`. -/
def Halted (s : State) : Prop :=
  s.halt ≠ .Running ∧ s.callStack = []

theorem halted_no_step {s s' : State} (h : Step s s') (H : Halted s) : False :=
  Step.not_from_done h H.1 H.2

theorem steps_from_halted {s s' : State} (h : Steps s s') (H : Halted s) :
    s' = s := by
  induction h with
  | refl => rfl
  | trans st _ _ => exact (halted_no_step st H).elim

theorem steps_halted_unique {s0 s1 s2 : State}
    (h1 : Steps s0 s1) (h2 : Steps s0 s2)
    (H1 : Halted s1) (H2 : Halted s2) : s1 = s2 := by
  induction h1 generalizing s2 with
  | refl =>
    exact (steps_from_halted h2 H1).symm
  | trans st rest ih =>
    cases h2 with
    | refl =>
      exact (halted_no_step st H2).elim
    | trans st' rest' =>
      exact ih (step_deterministic st st' ▸ rest') H1 H2

end Lsc.Compiler
