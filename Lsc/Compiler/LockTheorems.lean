import Lsc.Compiler.LockDefs
import Lsc.Compiler.Proof.LockProof
import Lsc.Compiler.Proof.LockPrefixProof
import Lsc.Compiler.Proof.LockNestedProof
import Lsc.Compiler.Bytecode
import Lsc.Compiler.CorrectnessDefs
import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.EvmDetTheorems
import YulEvmCompiler.LowerDefs
import YulSemantics.Observation

set_option linter.unusedVariables false

/-!
Held reentrancy lock: the compiled runtime reverts at the prologue, at
Yul and at assembled bytecode. Every assembled runtime begins with a
fixed instruction prefix. A nested CALL/STATICCALL frame into that
runtime, with transient slot 0 set, reverts in that prefix against
evm-semantics `Step` (not via `compile_correct`). Slice 8C-2 derives the storage / transient / self-log conjuncts of
`ExtOracle.NoReentry` from `toCall`'s lock restore (`noInterfere_of_lock`,
`ExtOracle.noReentry`) and `nested_lock_reverts`. ETH balances are not
claimed.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer.MemorySpill
open EvmSemantics (AccountAddress)
open EvmSemantics.EVM (State Steps Step Frame)

/-- If transient slot 0 is set, a Yul run of the memoryguard-erased
compiled runtime exists and reverts with empty data. Persistent storage,
transient storage, and logs in the committed observation are those of
the start state. No call oracle is required: the prologue reverts before
any CALL. -/
theorem lock_held_reverts_yul {c : ContractDef} {rt : YBlock} {st0 : EvmState}
    (hrt : runtimeBlock c = some rt) (hLock : ¬ LockFree st0) :
    ∃ st', Run evm (eraseMemoryGuardStmts rt) st0 [] st' .halt ∧
      st'.halted = some (.revert, []) ∧
      st'.storage = st0.storage ∧
      st'.transient = st0.transient ∧
      st'.logs = st0.logs ∧
      (committedState st0 st').storage = st0.storage ∧
      (committedState st0 st').transient = st0.transient ∧
      (committedState st0 st').logs = st0.logs :=
  Proof.lock_held_reverts_yul hrt hLock

/-- Every Yul run of the memoryguard-erased compiled runtime, from a
start state where transient slot 0 is set, reverts with empty data and
leaves committed storage, transient storage, and logs unchanged. -/
theorem lock_held_reverts_yul_of_run {c : ContractDef} {rt : YBlock}
    {st0 st' : EvmState} {out : Outcome}
    (hrt : runtimeBlock c = some rt) (hLock : ¬ LockFree st0)
    (hrun : Run evm (eraseMemoryGuardStmts rt) st0 [] st' out) :
    out = .halt ∧
      st'.halted = some (.revert, []) ∧
      st'.storage = st0.storage ∧
      st'.transient = st0.transient ∧
      st'.logs = st0.logs ∧
      (committedState st0 st').storage = st0.storage ∧
      (committedState st0 st').transient = st0.transient ∧
      (committedState st0 st').logs = st0.logs :=
  Proof.lock_held_reverts_yul_of_run hrt hLock hrun

/-- Same prologue revert as `lock_held_reverts_yul`, in the S2 dialect
that may mention CALL ops later in the block. Those ops are not reached. -/
theorem lock_held_reverts_yul_open {calls : ExternalCalls} {c : ContractDef}
    {rt : YBlock} {st0 : EvmState}
    (hrt : runtimeBlock c = some rt) (hLock : ¬ LockFree st0) :
    ∃ st', Run (yulD calls) (eraseMemoryGuardStmts rt) st0 [] st' .halt ∧
      st'.halted = some (.revert, []) ∧
      st'.storage = st0.storage ∧
      st'.transient = st0.transient ∧
      st'.logs = st0.logs ∧
      (committedState st0 st').storage = st0.storage ∧
      (committedState st0 st').transient = st0.transient ∧
      (committedState st0 st').logs = st0.logs :=
  Proof.lock_held_reverts_yul_open (calls := calls) hrt hLock

/-- On the held-lock path, `lockCheckStmt` reverts with empty data. The
post-state is the start state after `touchMemory` of the probed range,
with that revert payload. -/
theorem exec_lockCheck_halt_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hLock : ¬ LockFree st)
    (h : ExecStmt (yulD calls) funs V st lockCheckStmt V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } :=
  Proof.exec_lockCheck_halt_inv hfuns hLock h

/-- If transient slot 0 is set, assembled runtime bytecode of `c` from a
matching start frame (the same `FrameOK` / `StateMatch` / `pc = 0` /
empty-stack hypotheses as `compile_correct`) reverts with empty data.
The executing account's storage and transient storage, and the log
series, agree with the Yul start state. Every halted `Steps` from that
start agrees. -/
theorem lock_held_reverts_evm {c : ContractDef} {rt : YBlock} {is : List Instr}
    {yst0 : EvmState}
    (hrt : runtimeBlock c = some rt) (hcomp : compileBlock rt = some is)
    (hLock : ¬ LockFree yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] →
      b ≤ s0.gasAvailable →
      (∃ s', Steps s0 s' ∧ Halted s' ∧
        s'.halt = .Reverted ∧ s'.hReturn.toList = [] ∧
        (∀ k, conv (yst0.storage k) =
          (s'.accountMap s'.executionEnv.address).storage.get (conv k)) ∧
        (∀ k, conv (yst0.transient k) =
          (s'.accountMap s'.executionEnv.address).tstorage.get (conv k)) ∧
        LogsMatch yst0.logs s'.substate.logSeries) ∧
      ∀ s', Steps s0 s' → Halted s' →
        s'.halt = .Reverted ∧ s'.hReturn.toList = [] ∧
        (∀ k, conv (yst0.storage k) =
          (s'.accountMap s'.executionEnv.address).storage.get (conv k)) ∧
        (∀ k, conv (yst0.transient k) =
          (s'.accountMap s'.executionEnv.address).tstorage.get (conv k)) ∧
        LogsMatch yst0.logs s'.substate.logSeries :=
  Proof.lock_held_reverts_evm hrt hcomp hLock himm0

/-- Assembled runtime bytecode of every contract begins with a fixed
instruction prefix: `PUSH{w} k`, `ISZERO`, `POP`, `PUSH0`, `TLOAD`,
`ISZERO`, `PUSH2 dest`, `JUMPI`, `PUSH0`, `PUSH0`, `REVERT`, `JUMPDEST`,
then the rest of the program. `k` is `256` on the memoryguard-erasure
path and the spill reservation on the spill path. The `PUSH2`
immediate is the byte offset of that `JUMPDEST` (`13 + w`). -/
theorem runtime_prefix {c : ContractDef} {rt : YBlock} {is : List Instr}
    (hrt : runtimeBlock c = some rt) (h : compileBlock rt = some is) :
    ∃ k w hi lo rest,
      w = Instr.byteWidth k ∧
      assembleBytes is =
        lockPrefixP1 k ++ [hi, lo] ++ lockPrefixP2 ++ rest ∧
      ofBytes2 hi lo = 13 + w ∧
      ((compileErased rt = some is ∧ k = memoryGuardK) ∨
        (compileErased rt = none ∧
          ∃ r, spillRuntime? rt = some r ∧ k = r.reserved)) :=
  Proof.runtime_prefix hrt h

/-- A CALL or STATICCALL frame executing this contract's assembled runtime
at `pc = 0` with an empty stack, with transient slot 0 set at `self`,
reverts in the runtime prefix (at most the gas in `lockPrefixGasBound`)
and resumes the caller by rolling the world back to the call-time
snapshot. Not routed through `compile_correct` (the call stack is
non-empty). Out-of-gas on a shorter budget is not claimed. -/
theorem nested_lock_reverts {c : ContractDef} {rt : YBlock} {is : List Instr}
    {self : AccountAddress} {s : State} {f : Frame} {rest : List Frame}
    (hrt : runtimeBlock c = some rt) (hcomp : compileBlock rt = some is)
    (hf : NestedFrame (assemble is) s)
    (hself : s.executionEnv.address = self)
    (hacc : (s.accountMap self).code = assemble is)
    (hpc : s.pc = EvmSemantics.UInt256.ofNat 0)
    (hstack : s.stack = [])
    (hlock : (s.accountMap self).tstorage ⟨0⟩ ≠ ⟨0⟩)
    (hcs : s.callStack = f :: rest)
    (hcreate : f.createAddr = none) :
    ∃ b, b ≤ lockPrefixGasBound ∧
      (b ≤ s.gasAvailable →
        ∃ sR sP, Steps s sR ∧ sR.halt = .Reverted ∧ sR.hReturn.toList = [] ∧
          sR.callStack = f :: rest ∧ Step sR sP ∧
          sP.accountMap = f.snapAccountMap ∧
          sP.substate = f.snapSubstate) :=
  Proof.nested_lock_reverts hrt hcomp hf hself hacc hpc hstack hlock hcs hcreate

/-- Isolation of a nested CALL/STATICCALL into this contract while the
transient lock is held: the child reverts in the runtime prefix and
the parent snapshot of `self`'s storage, transient storage, code, and
nonce is restored. Balance is not claimed — a callee can credit `self`
via `SELFDESTRUCT` without executing our bytecode. CALLCODE/DELEGATECALL
are not emitted by this compiler. -/
theorem nested_lock_restores_self {c : ContractDef} {rt : YBlock} {is : List Instr}
    {self : AccountAddress} {s : State} {f : Frame} {rest : List Frame}
    (hrt : runtimeBlock c = some rt) (hcomp : compileBlock rt = some is)
    (hf : NestedFrame (assemble is) s)
    (hself : s.executionEnv.address = self)
    (hacc : (s.accountMap self).code = assemble is)
    (hpc : s.pc = EvmSemantics.UInt256.ofNat 0)
    (hstack : s.stack = [])
    (hlock : (s.accountMap self).tstorage ⟨0⟩ ≠ ⟨0⟩)
    (hcs : s.callStack = f :: rest)
    (hcreate : f.createAddr = none) :
    ∃ b, b ≤ lockPrefixGasBound ∧
      (b ≤ s.gasAvailable →
        ∃ sR sP, Steps s sR ∧ sR.halt = .Reverted ∧ sR.hReturn.toList = [] ∧
          sR.callStack = f :: rest ∧ Step sR sP ∧
          (sP.accountMap self).storage = (f.snapAccountMap self).storage ∧
          (sP.accountMap self).tstorage = (f.snapAccountMap self).tstorage ∧
          (sP.accountMap self).code = (f.snapAccountMap self).code ∧
          (sP.accountMap self).nonce = (f.snapAccountMap self).nonce ∧
          sP.substate = f.snapSubstate) :=
  Proof.nested_lock_restores_self hrt hcomp hf hself hacc hpc hstack hlock
    hcs hcreate

/-
Slice 8C-2. `NoReentry` is now a lemma (`ExtOracle.noReentry`): `toCall`
scrubs `self` on input and restores storage / transient / self-logs on
output, which is what `nested_lock_reverts` / `nested_lock_restores_self`
prove of a nested CALL/STATICCALL into the compiled runtime with the
lock held. ETH conjuncts are dropped (not implied by the lock).

`CallsRealized` only exposes endpoints under `FrameOK` (empty call
stack). LSC `Halted` also requires an empty call stack, so
`steps_halted_unique` does not identify nested child frames. Isolation
of foreign frames (SSTORE at an address other than `self`) is therefore
modelled by the `toCall` restore rather than an induction on every
`StepRunning` constructor. CALLCODE/DELEGATECALL write the caller's
account; this compiler does not emit them. CREATE2 cannot overwrite
existing code at `self`.

8C-3: `[Reentrant]` opts a function out of lock acquire/release
(`locks f` is false). The runtime prologue still checks the slot, so
`lock_held_reverts_*` / `runtime_prefix` / `nested_lock_*` keep their
statements. Store-after-call is rejected unless `[Reentrant.Unsafe]`.
-/

end Lsc.Compiler
