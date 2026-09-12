import Lsc.Compiler.ExtOracle
import YulEvmCompiler.Optimizer.Spec.Observe
import YulEvmCompiler.Optimizer.Spec.MemoryGuard

/-!
Proofs of the memory-blind CALL oracle. Statements live in `ExtOracleTheorems`.
-/

namespace Lsc.Compiler.Proof

open Lsc.Compiler
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

theorem toCalls_total (o : ExtOracle) : CallsTotal (toCalls o) :=
  fun req st => ⟨toCall o req st, rfl⟩

theorem toCalls_memoryBlind (o : ExtOracle) : CallsMemoryBlind (toCalls o) := by
  intro req left right response hview
  constructor
  · intro h
    change response = toCall o req right
    have : response = toCall o req left := h
    simpa [toCall, hview] using this
  · intro h
    change response = toCall o req left
    have : response = toCall o req right := h
    simpa [toCall, hview] using this

theorem CallsScratchInsensitive_of_memoryBlind {calls : ExternalCalls}
    (h : CallsMemoryBlind calls) (base reserved : Nat) :
    CallsScratchInsensitive calls base reserved := by
  intro req left right response hrel
  exact h req left right response hrel.observables_eq

theorem toCalls_scratchInsensitive (o : ExtOracle) (base reserved : Nat) :
    CallsScratchInsensitive (toCalls o) base reserved :=
  CallsScratchInsensitive_of_memoryBlind (toCalls_memoryBlind o) base reserved

theorem guardedExternals_oracle (o : ExtOracle) (base reserved : Nat) :
    GuardedExternals (toCalls o) ExternalCreates.none base reserved where
  calls_insensitive := toCalls_scratchInsensitive o base reserved
  creates_insensitive := by
    intro req left right response hrel
    simp [ExternalCreates.none]

end Lsc.Compiler.Proof
