import Lsc.Compiler.Proof.DispatchProof
import Lsc.Compiler.Proof.Descend
import Lsc.Compiler.Proof.SpillPath
import Lsc.Compiler.Proof.MemFootprintLift
import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.EvmDetTheorems
import YulSemantics.Observation
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Lock-held runtime revert (slice 8B). If transient slot 0 is set, the
compiled dispatcher reverts at the prologue: Yul `Run` of the
memoryguard-erased `runtimeBlock`, then the same fact lifted through
`compileRuntime_correct` to EVM `Steps`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.MemorySpillStateSound
open EvmSemantics.EVM (State Steps)

/-- Closed model used to lift a lock-held `Run` through `compile_correct`.
`gas` defaults to `.any`, matching `closedModel`. -/
@[instance_reducible] def lockModel : ExternalModel where
  calls := ExternalCalls.none
  creates := ExternalCreates.none

/-- Post-state of the lock-check revert. -/
def lockHeldFinal (st : EvmState) : EvmState :=
  { touchMemory (stAfterGuard st) 0 0 with halted := some (.revert, []) }

theorem lockHeldFinal_halted (st : EvmState) :
    (lockHeldFinal st).halted = some (.revert, []) := rfl

theorem lockHeldFinal_storage (st : EvmState) :
    (lockHeldFinal st).storage = st.storage := by
  simp [lockHeldFinal, stAfterGuard, touchMemory]

theorem lockHeldFinal_transient (st : EvmState) :
    (lockHeldFinal st).transient = st.transient := by
  simp [lockHeldFinal, stAfterGuard, touchMemory]

theorem lockHeldFinal_logs (st : EvmState) :
    (lockHeldFinal st).logs = st.logs := by
  simp [lockHeldFinal, stAfterGuard, touchMemory]

theorem lockHeldFinal_env (st : EvmState) :
    (lockHeldFinal st).env = st.env := by
  simp [lockHeldFinal, stAfterGuard, touchMemory]

theorem lockHeld_committed (st : EvmState) :
    (committedState st (lockHeldFinal st)).storage = st.storage ∧
    (committedState st (lockHeldFinal st)).transient = st.transient ∧
    (committedState st (lockHeldFinal st)).logs = st.logs := by
  rw [committedState_rollback (lockHeldFinal_halted st) HaltKind.revert_commits]
  exact ⟨rfl, rfl, rfl⟩

theorem not_LockFree_stAfterGuard {st : EvmState} (h : ¬ LockFree st) :
    ¬ LockFree (stAfterGuard st) := by
  simpa [stAfterGuard] using h

theorem exec_erased_lockHeld {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {cases : List (Literal × YBlock)} (h : ¬ LockFree st) :
    ExecStmts evm funs V st (erasedRuntime cases) V (lockHeldFinal st) .halt :=
  exec_cons_normal (exec_memoryGuardErased funs V st)
    (exec_head_halt (exec_lockCheck_halt funs V (stAfterGuard st)
      (not_LockFree_stAfterGuard h)))

theorem run_erased_lockHeld {st : EvmState} {cases : List (Literal × YBlock)}
    (h : ¬ LockFree st) :
    Run evm (erasedRuntime cases) st [] (lockHeldFinal st) .halt :=
  run_of_exec (hoist_erased_runtime _ _ cases) (exec_erased_lockHeld h)

namespace Proof

theorem lock_held_reverts_yul {c : ContractDef} {rt : YBlock} {st0 : EvmState}
    (hrt : runtimeBlock c = some rt) (hLock : ¬ LockFree st0) :
    ∃ st', Run evm (eraseMemoryGuardStmts rt) st0 [] st' .halt ∧
      st'.halted = some (.revert, []) ∧
      st'.storage = st0.storage ∧
      st'.transient = st0.transient ∧
      st'.logs = st0.logs ∧
      (committedState st0 st').storage = st0.storage ∧
      (committedState st0 st').transient = st0.transient ∧
      (committedState st0 st').logs = st0.logs := by
  obtain ⟨cases, _, hE⟩ := erase_runtimeBlock hrt
  rw [hE]
  obtain ⟨hs, ht, hl⟩ := lockHeld_committed st0
  exact ⟨lockHeldFinal st0, run_erased_lockHeld (cases := cases) hLock,
    lockHeldFinal_halted st0,
    lockHeldFinal_storage st0,
    lockHeldFinal_transient st0,
    lockHeldFinal_logs st0, hs, ht, hl⟩

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
      (committedState st0 st').logs = st0.logs := by
  obtain ⟨st1, hfwd, hh, hs, ht, hl, hcs, hct, hcl⟩ := lock_held_reverts_yul hrt hLock
  obtain ⟨_, hst, ho⟩ := EVM.run_det hrun hfwd
  subst hst; subst ho
  exact ⟨rfl, hh, hs, ht, hl, hcs, hct, hcl⟩

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
      (committedState st0 st').logs = st0.logs := by
  obtain ⟨st', hrun, hh, hs, ht, hl, hcs, hct, hcl⟩ := lock_held_reverts_yul hrt hLock
  exact ⟨st', run_lift calls .none .none hrun, hh, hs, ht, hl, hcs, hct, hcl⟩

/-- Inversion of `lockCheckStmt` on the held-lock path. -/
theorem exec_lockCheck_halt_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hLock : ¬ LockFree st)
    (h : ExecStmt (yulD calls) funs V st lockCheckStmt V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  have hdesc := execStmt_descend hfuns noExt_lockCheckStmt h
  have hfwd := exec_lockCheck_halt (funEnvUncast calls funs) V st hLock
  have heq := step_det_evm hfwd hdesc
  injection heq with hV hst ho
  exact ⟨ho.symm, hV.symm, hst.symm⟩

theorem runtimeSrc_lock {c : ContractDef} {rt : YBlock} {is : List Instr}
    {yst0 yst' : EvmState} {o : Outcome}
    (hrt : runtimeBlock c = some rt) (hcomp : compileBlock rt = some is)
    (hrun : Run (evmWithExternal ExternalCalls.none ExternalCreates.none ExternalGas.any)
      (eraseMemoryGuardStmts rt) yst0 [] yst' o) :
    RuntimeCompileSrc (model := lockModel) rt is yst0 yst' o := by
  let _model : ExternalModel := lockModel
  cases compileBlock_elim hcomp with
  | inl hce => exact .erased hce hrun
  | inr h =>
    obtain ⟨hne, hsp⟩ := h
    obtain ⟨r, hr, hcr⟩ := compileSpilled_inv hsp
    exact .spilled r hne hr hcr rfl (guardedExternals_none r.base r.reserved)
      (GuardedRunOfErased hrt hr hrun)

theorem ystF_lock_obs {b : YBlock} {is : List Instr} {yst' ystF : EvmState}
    (hcomp : compileBlock b = some is)
    (hFe : compileErased b = some is → ystF = yst')
    (hFs : ∀ r, compileErased b = none → spillRuntime? b = some r →
      ScratchRel r.base r.reserved yst' ystF) :
    ystF.storage = yst'.storage ∧
    ystF.transient = yst'.transient ∧
    ystF.logs = yst'.logs ∧
    ystF.halted = yst'.halted ∧
    ystF.env = yst'.env := by
  cases compileBlock_elim hcomp with
  | inl hce =>
    have heq := hFe hce
    exact ⟨by rw [heq], by rw [heq], by rw [heq], by rw [heq], by rw [heq]⟩
  | inr h =>
    obtain ⟨hne, hsp⟩ := h
    obtain ⟨r, hr, _⟩ := compileSpilled_inv hsp
    have hrel := hFs r hne hr
    exact ⟨(ScratchRel.storage_eq hrel).symm,
      (ScratchRel.transient_eq hrel).symm,
      (ScratchRel.logs_eq hrel).symm,
      (ScratchRel.halted_eq hrel).symm,
      (ScratchRel.env_eq hrel).symm⟩

theorem reverted_of_halted {yst : EvmState} {s : State} {bytes : List UInt8}
    (h : yst.halted = some (.revert, bytes)) (hHM : HaltedMatch yst s) :
    s.halt = .Reverted ∧ s.hReturn.toList = bytes := by
  obtain ⟨hk, hhalt, hM⟩ := hHM
  rw [h] at hhalt
  cases hhalt
  simpa [HaltMatch] using hM

theorem halt_ne_running_of_HaltMatch {hk : HaltKind × List UInt8} {s : State}
    (h : HaltMatch hk s) : s.halt ≠ .Running := by
  intro hrun
  unfold HaltMatch at h
  split at h
  · cases (h.symm.trans hrun)
  · cases (h.1.symm.trans hrun)
  · cases (h.1.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.1.symm.trans hrun)

theorem Halted_of_HaltedMatch {yst : EvmState} {s : State}
    (h : HaltedMatch yst s) (hcs : s.callStack = []) : Halted s :=
  ⟨by
    obtain ⟨hk, _, hM⟩ := h
    exact halt_ne_running_of_HaltMatch hM, hcs⟩

theorem Halted_of_compile_out {s' : State} {yst' : EvmState} {o : Outcome}
    (hcs : s'.callStack = [])
    (hOut : (o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
            (o = .halt ∧ HaltedMatch yst' s')) : Halted s' := by
  rcases hOut with ⟨_, hs, _⟩ | ⟨_, hHM⟩
  · exact ⟨by simp [hs], hcs⟩
  · exact Halted_of_HaltedMatch hHM hcs

theorem HaltedMatch_of_ystF {yst' ystF : EvmState} {s' : State}
    (hHM : HaltedMatch ystF s') (hh : ystF.halted = yst'.halted) :
    HaltedMatch yst' s' := by
  obtain ⟨hk, hy, hM⟩ := hHM
  exact ⟨hk, hh ▸ hy, hM⟩

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
        LogsMatch yst0.logs s'.substate.logSeries := by
  let _model : ExternalModel := lockModel
  have hY := lock_held_reverts_yul hrt hLock
  obtain ⟨yst', hrunY, hhY, hsY, htY, hlY, _, _, _⟩ := hY
  have hrunA :=
    run_lift ExternalCalls.none ExternalCreates.none ExternalGas.any hrunY
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have hsrc := runtimeSrc_lock hrt hcomp hrunA
  have ⟨b, hb0⟩ :=
    compileRuntime_correct (model := lockModel) ExternalsRealized.none
      hcomp himm hsrc
  refine ⟨b, ?_⟩
  intro s0 hOK hM hpc hstk hgas
  obtain ⟨s', ystF, hSteps, hcs, hSM, hOut, hFe, hFs⟩ :=
    hb0 s0 hOK hM hpc hstk hgas
  have ⟨hstor, htrans, hlogs, hhalt, _⟩ := ystF_lock_obs hcomp hFe hFs
  have hH : Halted s' := Halted_of_compile_out hcs hOut
  have hHM : HaltedMatch yst' s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH'⟩
    · cases hn
    · exact HaltedMatch_of_ystF hH' hhalt
  have hr := reverted_of_halted hhY hHM
  have hstor' : ∀ k, conv (yst0.storage k) =
      (s'.accountMap s'.executionEnv.address).storage.get (conv k) := by
    intro k
    have := hSM.stor k
    rw [hstor, hsY] at this
    exact this
  have htrans' : ∀ k, conv (yst0.transient k) =
      (s'.accountMap s'.executionEnv.address).tstorage.get (conv k) := by
    intro k
    have := hSM.tstor k
    rw [htrans, htY] at this
    exact this
  have hlogs' : LogsMatch yst0.logs s'.substate.logSeries := by
    have := hSM.logs
    rw [hlogs, hlY] at this
    exact this
  have hconcl :
      s'.halt = .Reverted ∧ s'.hReturn.toList = [] ∧
      (∀ k, conv (yst0.storage k) =
        (s'.accountMap s'.executionEnv.address).storage.get (conv k)) ∧
      (∀ k, conv (yst0.transient k) =
        (s'.accountMap s'.executionEnv.address).tstorage.get (conv k)) ∧
      LogsMatch yst0.logs s'.substate.logSeries :=
    ⟨hr.1, hr.2, hstor', htrans', hlogs'⟩
  refine ⟨⟨s', hSteps, hH, hconcl⟩, ?_⟩
  intro s'' hS'' hH''
  rw [steps_halted_unique hS'' hSteps hH'' hH]
  exact hconcl

end Proof

end Lsc.Compiler
