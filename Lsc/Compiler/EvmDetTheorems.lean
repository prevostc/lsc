import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.Proof.EvmDetProof

/-!
Determinism of halted EVM traces. The bytecode glue uses this so a security
conclusion about "the" post-storage applies to every matching `Steps` run,
not only the witness produced by powdr `compile_correct`.
-/

namespace Lsc.Compiler

open EvmSemantics.EVM

/-- Two halted EVM executions from the same start state end in the same
state. `Step` is deterministic, and a done frame (`halt ≠ Running`, empty
call stack) has no successor. Out-of-gas is a halt kind, so the lemma still
applies; it does not by itself say the program reached the Yul-predicted
halt — that direction is `compile_correct` plus progress. -/
theorem steps_halted_unique {s0 s1 s2 : State}
    (h1 : Steps s0 s1) (h2 : Steps s0 s2)
    (H1 : Halted s1) (H2 : Halted s2) : s1 = s2 :=
  Proof.steps_halted_unique h1 h2 H1 H2

end Lsc.Compiler
