import Lsc.Compiler.Proof.LockProof
import Lsc.Compiler.Bytecode
import Lsc.Compiler.CorrectnessDefs
import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.EvmDetTheorems
import YulEvmCompiler.LowerDefs
import YulSemantics.Observation

set_option linter.unusedVariables false

/-!
Held reentrancy lock: the compiled runtime reverts at the prologue, at
Yul and at assembled bytecode. Slice 8C will use these facts to derive
the storage / transient / self-log conjuncts of `ExtOracle.NoReentry`
instead of assuming `hNR`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer.MemorySpill
open EvmSemantics.EVM (State Steps)

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

/-
Groundwork for slice 8C — statement only, not a theorem.

`noInterfere_of_lock` would take `lock_held_reverts_evm`,
`YulEvmCompiler.CallsRealized (toCalls o)`, a pin that code at `self` is
the assembled runtime, and "only the executing account `sstore`s /
`tstore`s / `LOG*`s as itself", and conclude the storage, transient, and
self-log conjuncts of `ExtOracle.NoReentry.noInterfere`:

  st.env.address = BitVec.ofNat 256 self →
  ¬ LockFree st →
  let resp := o req (ExtView.ofState st)
  resp.world.storage = st.storage ∧
  resp.world.transient = st.transient ∧
  (∀ l ∈ resp.world.logs, l.address ≠ st.env.address)

Gaps (do not silently close these in 8C):

1. Nested frames. `FrameOK.callStack = []` is required by
   `compile_correct` / `lock_held_reverts_evm`. A reentrant CALL frame
   has a caller on the stack. Needed in pinned yul-compiler: a
   `compile_correct` (or Phase-B `astep_sim`) variant that allows a
   non-empty `callStack`, restoring the caller on halt — or a lemma that
   a CALL-entered frame whose `executionEnv.code` is `assemble is` and
   whose `tstorage[0] ≠ 0` reverts without writing that account's
   storage / transient / logs.

2. Code-at-self pin. `FrameOK.hcode` identifies executing code with
   `assemble is`. For a CALL to `self`, need
   `(accountMap self).code = assemble is` (and `codeAddr` agreement).
   Deploy / `bytecode_deploy_correct` plus "runtime code is not later
   overwritten" are not in this module.

3. Isolation of `sstore` / `tstore` / `LOG*`. EVM `StepRunning.sstore`,
   `.tstore`, and `logN` update `executionEnv.address` only; Yul
   `step_sstore` / `step_tstore` / `appendLog` are the executing
   account. There is no packaged lemma "a foreign frame cannot write
   `self` except by calling `self`". `CallsRealized` endpoints do not by
   themselves name the intermediate reentrant frame.

4. `ignoresSelf` / `scrubSelf`. `NoReentry.ignoresSelf` is that the
   oracle ignores caller-local fields. The lock lemma does not imply it.
   `scrubSelf` already drops executing-account storage/transient/logs
   (`ExtOracle.lean`); proving `ignoresSelf` is a property of `o`, not
   of the lock.

5. `selfBalance` / `balanceOf`. `noInterfere`'s ETH conjuncts are
   outside the lock: a non-reentering callee can still transfer value.
   8C should keep those as oracle hypotheses or a separate lemma.
-/

end Lsc.Compiler
