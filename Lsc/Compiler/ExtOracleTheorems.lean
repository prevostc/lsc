import Lsc.Compiler.ExtOracle
import Lsc.Compiler.Proof.ExtOracleProof
import YulEvmCompiler.Optimizer.Spec.MemoryGuard

/-!
Memory-blind CALL oracle: wrapping `ExtOracle` as `ExternalCalls` answers
every CALL, ignores caller memory/`msize`, and supplies powdr's
scratch-insensitive spill hypothesis. Vault and AMM bytecode glue use
this instead of assuming totality.
-/

namespace Lsc.Compiler

open YulSemantics.EVM
open YulEvmCompiler.Optimizer

/-- Wrapping a memory-blind `ExtOracle` as `ExternalCalls` answers every CALL
with some bytes. Totality is by construction: the oracle is a function, so
there is always a response. S2 bytecode glue uses this so "every matching
EVM run" is not vacuous. -/
theorem toCalls_total (o : ExtOracle) : CallsTotal (toCalls o) :=
  Proof.toCalls_total o

/-- Responses of `toCalls o` depend only on the callee-visible view, not on
caller memory or `msize`. Two Yul states that agree on every other field
therefore get the same CALL result. -/
theorem toCalls_memoryBlind (o : ExtOracle) : CallsMemoryBlind (toCalls o) :=
  Proof.toCalls_memoryBlind o

/-- Any memory-blind `ExternalCalls` relation is scratch-insensitive for
every reservation interval. Powdr's spill theorem asks for this on the
scratch window; memory-blindness is stronger and implies it. -/
theorem CallsScratchInsensitive_of_memoryBlind {calls : ExternalCalls}
    (h : CallsMemoryBlind calls) (base reserved : Nat) :
    CallsScratchInsensitive calls base reserved :=
  Proof.CallsScratchInsensitive_of_memoryBlind h base reserved

/-- `toCalls o` is scratch-insensitive for every reservation interval.
Instance of `CallsScratchInsensitive_of_memoryBlind` at the memory-blind
oracle. -/
theorem toCalls_scratchInsensitive (o : ExtOracle) (base reserved : Nat) :
    CallsScratchInsensitive (toCalls o) base reserved :=
  Proof.toCalls_scratchInsensitive o base reserved

/-- `toCalls o` with no CREATE is a `GuardedExternals` package at any
reservation window. That is the spill-theorem hypothesis; S2 compile
through powdr spill gets it from the memory-blind oracle rather than as
an extra assumption. -/
theorem guardedExternals_oracle (o : ExtOracle) (base reserved : Nat) :
    GuardedExternals (toCalls o) ExternalCreates.none base reserved :=
  Proof.guardedExternals_oracle o base reserved

end Lsc.Compiler
