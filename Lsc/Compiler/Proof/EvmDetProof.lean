import EvmSemantics.EVM.StepDeterminism
import Lsc.Compiler.EvmDetDefs

/-!
Proofs of EVM halted-trace uniqueness. Statements live in `EvmDetTheorems`.
-/

namespace Lsc.Compiler.Proof

open EvmSemantics.EVM
open Lsc.Compiler

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

end Lsc.Compiler.Proof
