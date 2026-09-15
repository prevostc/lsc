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

open Lsc
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

/-- A CALL through `toCall` leaves this contract's storage and transient
storage as they were, and appends no log attributed to this contract.
ETH balances may still change: a callee can `SELFDESTRUCT` to this
address without running our code, and `balanceOf` of other accounts is
a real CALL effect. -/
theorem noInterfere_of_lock (o : ExtOracle) (req : CallRequest) (st : EvmState) :
    let resp := toCall o req st
    resp.world.storage = st.storage ∧
      resp.world.transient = st.transient ∧
      (∀ l ∈ resp.world.logs, l.address ≠ st.env.address) :=
  Proof.noInterfere_of_lock o req st

/-- Every memory-blind oracle, wrapped by `toCall`, satisfies `NoReentry`
at every address: the wrapper scrubs `self` on the way in and restores
storage / transient / self-logs on the way out. ETH balances are not
constrained (`SELFDESTRUCT` to this address, foreign `balanceOf`). -/
theorem ExtOracle.noReentry (o : ExtOracle) (self : Address) :
    ExtOracle.NoReentry o self :=
  Proof.ExtOracle.noReentry o self

end Lsc.Compiler
