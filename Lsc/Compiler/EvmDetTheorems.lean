import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.Proof.EvmDetProof

/-!
Halted EVM traces are deterministic. Bytecode security talks about "the"
post-storage of a call; this theorem says every matching halted run
agrees, not only the witness the Yul-to-EVM compiler produces.

Out-of-gas is a halt, so the lemma still applies. It does not by itself
say the program reached the Yul-predicted halt.
-/

namespace Lsc.Compiler

open EvmSemantics.EVM

/-- Two halted EVM executions from the same start state end in the same
state. A done frame has no successor, so there is only one post-storage
to talk about. Out-of-gas counts as a halt. This does not say the
program reached the halt the high-level model predicted — that direction
is the compiler theorem plus progress. -/
theorem steps_halted_unique {s0 s1 s2 : State}
    (h1 : Steps s0 s1) (h2 : Steps s0 s2)
    (H1 : Halted s1) (H2 : Halted s2) : s1 = s2 :=
  Proof.steps_halted_unique h1 h2 H1 H2

end Lsc.Compiler
