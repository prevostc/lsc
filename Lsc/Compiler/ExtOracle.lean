import Lsc.Compiler.Externals
import YulEvmCompiler.Optimizer.Spec.Observe

/-!
# Memory-blind external-call oracle

An EVM callee never sees the caller's memory or `msize`. It sees the call
request (calldata, value, gas, target) and the world/account projection.
`ExtOracle` is that contract at the type level: the oracle is not given
`EvmState`, so it cannot peek at caller memory. Wrapping through
`toCalls` yields an `ExternalCalls` relation that is scratch-insensitive
for every reservation interval, which is what powdr's spill theorem needs.

A second, distinct modelling consequence: `ExtOracle` is a function of the
request and the observable world, so the oracle is deterministic.
Previously `ExternalCalls.Call` was an arbitrary relation, which allowed a
callee whose response depended on hidden state outside the caller's
observable world, or that answered differently on two calls with the same
request and the same observable world. The EVM is deterministic given the
world state and the block environment, and every callee's own storage,
balance, and code are already in `Obs`, so a real callee is a function of
exactly (request, world). What is excluded is an adversary with state
outside the modelled world — nothing a real deployment can exhibit.
Wrapping with `toCalls` discharges `CallsTotal` once (`toCalls_total`)
instead of assuming it.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

/-- Caller/transaction-observable projection: every `EvmState` field except
byte memory and `msize`. An external callee in the real EVM cannot see more
than this plus the explicit `CallRequest`. -/
abbrev ExtView := Obs

/-- Project an `EvmState` onto the view a callee can observe. -/
abbrev ExtView.ofState : EvmState → ExtView := observables

/-- External-call oracle that is memory-free by construction. -/
abbrev ExtOracle := CallRequest → ExtView → CallResponse

/-- Apply a memory-blind oracle to a full Yul state by dropping memory/`msize`. -/
def toCall (o : ExtOracle) (req : CallRequest) (st : EvmState) : CallResponse :=
  o req (ExtView.ofState st)

/-- `ExternalCalls` wrapper: the unique response is `toCall o req st`. -/
def toCalls (o : ExtOracle) : ExternalCalls where
  Call req st resp := resp = toCall o req st

/-- Agreement on every field except memory and `msize` (Yul `EvmState` has no
stack/pc). Stronger than `CallsScratchInsensitive`, which only needs this on
`ScratchRel` pairs. -/
def CallsMemoryBlind (calls : ExternalCalls) : Prop :=
  ∀ req left right response,
    ExtView.ofState left = ExtView.ofState right →
    (calls.Call req left response ↔ calls.Call req right response)

end Lsc.Compiler
