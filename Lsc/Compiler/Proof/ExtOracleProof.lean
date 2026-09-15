import Lsc.Compiler.ExtOracle
import YulEvmCompiler.Optimizer.Spec.Observe
import YulEvmCompiler.Optimizer.Spec.MemoryGuard

set_option linter.unusedVariables false

/-!
Proofs of the memory-blind CALL oracle. Statements live in `ExtOracleTheorems`.
-/

namespace Lsc.Compiler.Proof

open Lsc.Compiler
open Lsc
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

theorem toCalls_total (o : ExtOracle) : CallsTotal (toCalls o) :=
  fun req st => ⟨toCall o req st, rfl⟩

theorem toCalls_memoryBlind (o : ExtOracle) : CallsMemoryBlind (toCalls o) := by
  intro req left right response hview
  have hto : toCall o req left = toCall o req right := by
    simp only [toCall, callRaw, restoreCall]
    rw [hview]
  constructor
  · intro h
    change response = toCall o req right
    exact hto ▸ h
  · intro h
    change response = toCall o req left
    exact hto.symm ▸ h

theorem restoreSelfWorld_storage (x : ExtView) (w : CallWorld) :
    (restoreSelfWorld x w).storage = x.storage := rfl

theorem restoreSelfWorld_transient (x : ExtView) (w : CallWorld) :
    (restoreSelfWorld x w).transient = x.transient := rfl

theorem restoreSelfWorld_success (x : ExtView) (resp : CallResponse) :
    (restoreCall x resp).success = resp.success := rfl

theorem restoreSelfWorld_returndata (x : ExtView) (resp : CallResponse) :
    (restoreCall x resp).returndata = resp.returndata := rfl

theorem restoreSelfWorld_logs_not_self {x : ExtView} {w : CallWorld}
    {l : LogEntry} (hl : l ∈ (restoreSelfWorld x w).logs) :
    l.address ≠ x.env.address :=
  of_decide_eq_true (List.mem_filter.mp hl).2

/-- Yul CALL through `toCall` leaves this contract's storage and transient
storage unchanged and appends no self-addressed log. The ETH maps are
those of the raw oracle (a non-reentering callee may still move value). -/
theorem noInterfere_of_lock (o : ExtOracle) (req : CallRequest) (st : EvmState) :
    let resp := toCall o req st
    resp.world.storage = st.storage ∧
      resp.world.transient = st.transient ∧
      (∀ l ∈ resp.world.logs, l.address ≠ st.env.address) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [toCall, restoreCall, restoreSelfWorld, ExtView.ofState, ExtState.ofState]
  · simp [toCall, restoreCall, restoreSelfWorld, ExtView.ofState, ExtState.ofState]
  · intro l hl
    have hl' : l ∈ (restoreSelfWorld (ExtView.ofState st)
        (callRaw o req (ExtView.ofState st)).world).logs := by
      simpa [toCall, restoreCall] using hl
    simpa [ExtView.ofState, ExtState.ofState] using
      restoreSelfWorld_logs_not_self hl'

theorem toCall_success (o : ExtOracle) (req : CallRequest) (st : EvmState) :
    (toCall o req st).success = (callRaw o req (ExtView.ofState st)).success :=
  rfl

theorem toCall_returndata (o : ExtOracle) (req : CallRequest) (st : EvmState) :
    (toCall o req st).returndata = (callRaw o req (ExtView.ofState st)).returndata :=
  rfl

theorem scrubSelf_word (self : Address) (x : Lsc.ExtState) :
    scrubSelf self x = scrubSelfWord (BitVec.ofNat 256 self) x := rfl

theorem scrubSelf_address (self : Address) (x : Lsc.ExtState) :
    (scrubSelf self x).env.address = x.env.address := rfl

theorem agreeExceptSelf_address {self : Address} {x y : Lsc.ExtState}
    (h : agreeExceptSelf self x y) : x.env.address = y.env.address :=
  (scrubSelf_address self x).symm.trans
    ((congrArg (fun z : Lsc.ExtState => z.env.address) h).trans
      (scrubSelf_address self y))

theorem callRaw_congr {o : ExtOracle} {req : CallRequest} {x : ExtView}
    {st : EvmState} {self : Address}
    (haddr : st.env.address = BitVec.ofNat 256 self)
    (hAgr : agreeExceptSelf self x (ExtView.ofState st)) :
    callRaw o req x = callRaw o req (ExtView.ofState st) := by
  have hx : x.env.address = st.env.address := by
    simpa [ExtView.ofState, ExtState.ofState] using agreeExceptSelf_address hAgr
  have hself : x.env.address = BitVec.ofNat 256 self := hx.trans haddr
  have hL : scrubSelfWord x.env.address x = scrubSelf self x := by
    simp only [scrubSelf, hself]
  have hR : scrubSelfWord (ExtView.ofState st).env.address (ExtView.ofState st) =
      scrubSelf self (ExtView.ofState st) := by
    simp [scrubSelf, ExtView.ofState, ExtState.ofState, haddr]
  unfold callRaw
  rw [hL, hR, hAgr]

/-- `NoReentry` of every memory-blind oracle: input scrub plus the lock
restore on `toCall`. ETH conjuncts are not claimed. -/
theorem ExtOracle.noReentry (o : ExtOracle) (self : Address) :
    ExtOracle.NoReentry o self where
  noInterfere := fun req st _haddr => noInterfere_of_lock o req st
  ignoresSelf := fun req x st haddr hAgr => callRaw_congr haddr hAgr

theorem CallsScratchInsensitive_of_memoryBlind {calls : ExternalCalls}
    (h : CallsMemoryBlind calls) (base reserved : Nat) :
    CallsScratchInsensitive calls base reserved := by
  intro req left right response hrel
  exact h req left right response (ExtView.ofState_congr hrel.observables_eq)

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
