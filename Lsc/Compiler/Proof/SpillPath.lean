import Lsc.Compiler.Bytecode
import Lsc.Compiler.Proof.Layout
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs
import YulEvmCompiler.Optimizer.Spec.Observe
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`compileBlock` path split, scratch transport, and the Lsc-level
`compileRuntime_correct` covering erase and powdr spill.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.MemorySpillSound
open EvmSemantics.EVM (State Steps)

/-- If `compileRuntime` emitted `is`, that list is either the memoryguard-erased
compile of the runtime or a successful powdr spill of the raw runtime
when erasure is rejected (`DUP17+`). The disjuncts are exclusive. -/
theorem compileInstr_elim {b : YBlock} {is : List Instr}
    (h : (compileErased b <|> compileSpilled b) = some is) :
    compileErased b = some is ∨
      (compileErased b = none ∧ compileSpilled b = some is) := by
  cases he : compileErased b with
  | some is0 =>
    have : some is0 = some is := by
      simpa [he] using h
    cases this
    exact Or.inl rfl
  | none =>
    exact Or.inr ⟨rfl, by simpa [he] using h⟩

theorem compileBlock_elim {b : YBlock} {is : List Instr}
    (h : compileBlock b = some is) :
    compileErased b = some is ∨
      (compileErased b = none ∧ compileSpilled b = some is) :=
  compileInstr_elim (by simpa [compileBlock] using h)

/-- A spilled compile is a `spillBlock?` of the raw runtime together
with an ordinary compile of that spilled block. Storage, logs, halt, and
environment of a matching Yul run agree with the guarded source except on
compiler scratch (`R_of_scratchRel`). -/
theorem compileSpilled_inv {b : YBlock} {is : List Instr}
    (h : compileSpilled b = some is) :
    ∃ r, spillRuntime? b = some r ∧ compile r.block = some is := by
  unfold compileSpilled at h
  split at h
  · next r hr => exact ⟨r, hr, h⟩
  · cases h

theorem guardedExternals_none (base reserved : Nat) :
    GuardedExternals ExternalCalls.none ExternalCreates.none base reserved where
  calls_insensitive := by
    intro req left right response hrel
    simp [ExternalCalls.none]
  creates_insensitive := by
    intro req left right response hrel
    simp [ExternalCreates.none]

theorem R_of_scratchRel {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {base reserved : Nat}
    {st st' : EvmState} (hR : R c Γ κ w st)
    (h : ScratchRel base reserved st st') : R c Γ κ w st' := by
  rcases hR with ⟨hs, hlog, hκ, hwf⟩
  refine ⟨?_, ?_, ?_, hwf⟩
  · simpa [MemorySpillStateSound.ScratchRel.storage_eq h] using hs
  · have henv := MemorySpillStateSound.ScratchRel.env_eq h
    have hlogs := MemorySpillStateSound.ScratchRel.logs_eq h
    unfold logsRel selfLogs at hlog ⊢
    simpa [henv, hlogs] using hlog
  · have henv := MemorySpillStateSound.ScratchRel.env_eq h
    simpa [henv] using hκ

theorem R_of_observables {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {st st' : EvmState}
    (hR : R c Γ κ w st) (h : observables st = observables st') :
    R c Γ κ w st' := by
  rcases hR with ⟨hs, hlog, hκ, hwf⟩
  have hs' : st'.storage = st.storage := by
    exact (congrArg Obs.storage h).symm
  have henv : st'.env = st.env := by
    exact (congrArg Obs.env h).symm
  have hlogs : st'.logs = st.logs := by
    exact (congrArg Obs.logs h).symm
  refine ⟨?_, ?_, ?_, hwf⟩
  · simpa [hs'] using hs
  · unfold logsRel selfLogs at hlog ⊢
    simpa [henv, hlogs] using hlog
  · simpa [henv] using hκ

/-- Source run matching a successful `compileBlock` branch. Erase uses the
ordinary dialect on `eraseMemoryGuardStmts`; spill uses `GuardedRun` of the
resolved raw runtime (`memoryguard(k)` → `reserved`). -/
inductive RuntimeCompileSrc [model : ExternalModel]
    (b : YBlock) (is : List Instr) (yst0 yst' : EvmState) (o : Outcome) : Prop
  | erased
      (hce : compileErased b = some is)
      (hrun : Run (evmWithExternal model.calls model.creates model.gas)
        (eraseMemoryGuardStmts b) yst0 [] yst' o)
  | spilled (r : Result)
      (hne : compileErased b = none)
      (hsp : spillRuntime? b = some r)
      (hcr : compile r.block = some is)
      (hgas : model.gas = ExternalGas.any)
      (hg : GuardedExternals model.calls model.creates r.base r.reserved)
      (hrun : GuardedRun model.calls model.creates b r.base r.reserved
        yst0 [] yst' o)

/-- A successful `compileBlock` is simulated by the pinned compiler: the erase
branch is `compile_correct` on the erased source; the spill branch is
`compile_memorySpill_correct` on a `GuardedRun` of the resolved raw runtime.
The EVM `StateMatch` final is the erased Yul state on the erase path and the
spilled Yul state (scratch-related to the guarded source) on the spill path. -/
theorem compileRuntime_correct [model : ExternalModel]
    (hexternal : ExternalsRealized model)
    {b : YBlock} {is : List Instr}
    (_hcomp : compileBlock b = some is)
    {yst0 yst' : EvmState} {o : Outcome}
    (himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (YulSemantics.EVM.litValue (.string key)))
    (hsrc : RuntimeCompileSrc b is yst0 yst' o) :
    ∃ bound : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] →
      bound ≤ s0.gasAvailable →
      ∃ s' ystF, Steps s0 s' ∧ s'.callStack = [] ∧
        StateMatch ystF s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch ystF s')) ∧
        (compileErased b = some is → ystF = yst') ∧
        (∀ r, compileErased b = none → spillRuntime? b = some r →
          ScratchRel r.base r.reserved yst' ystF) := by
  cases hsrc with
  | erased hce hrun =>
    have ⟨bound, hb⟩ := compile_correct hexternal hce himm hrun
    refine ⟨bound, ?_⟩
    intro s0 hOK hM hpc hstk hgas
    obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
    refine ⟨s', yst', hSteps, hcs, hSM, hOut, fun _ => rfl, ?_⟩
    intro r hne _
    exact absurd (hce.symm.trans hne) (by simp)
  | spilled r hne hsp hcr hgas hg hrun =>
    have ⟨_, targetFinal, _, hscratch, _, bound, hb⟩ :=
      compile_memorySpill_correct hexternal hgas hsp hg hcr himm hrun
    refine ⟨bound, ?_⟩
    intro s0 hOK hM hpc hstk hgas
    obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
    refine ⟨s', targetFinal, hSteps, hcs, hSM, hOut, ?_, ?_⟩
    · intro hce
      exact absurd (hne.symm.trans hce) (by simp)
    · intro r' _ hsp'
      have heq : r' = r := Option.some.inj (hsp'.symm.trans hsp)
      exact heq ▸ hscratch

end Lsc.Compiler
