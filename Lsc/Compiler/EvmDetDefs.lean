import EvmSemantics.EVM.BigStep

/-!
Halted EVM frames: the stuckness condition used by uniqueness and by the
end-to-end glue (`EvmCallRun`).
-/

namespace Lsc.Compiler

open EvmSemantics.EVM

/-- Top-level execution is finished: the active frame halted and no caller
remains to resume. Same stuckness condition as `State.isDone` / `Eval`. -/
def Halted (s : State) : Prop :=
  s.halt ≠ .Running ∧ s.callStack = []

end Lsc.Compiler
