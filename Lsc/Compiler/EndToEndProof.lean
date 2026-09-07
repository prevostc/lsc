import Lsc.Compiler.EndToEnd
import Lsc.Compiler.Proof.SpillPath
import Lsc.Compiler.Proof.MemFootprint

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of S1 bytecode glue. Statements live in `EndToEndTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open EvmSemantics.EVM (State Steps)

namespace Proof

theorem bytecode_call_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is := by
  let _model : ExternalModel := closedModel
  simp only [BytecodeCallCorrect]
  obtain ⟨stObs, hRC, hconcl⟩ :=
    runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound rt hrt ctx w yst0 hctx hR
  obtain ⟨yst', hrun, hobs⟩ := runCommitted_lift_run .none .none .any hRC
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have hcompB := compileErased_to_compileBlock hcomp
  have ⟨b, hb⟩ :=
    compileRuntime_correct (model := closedModel) ExternalsRealized.none hcompB himm
      (.erased hcomp hrun)
  refine ⟨b, ?_⟩
  intro s0 hOK hM hpc hstk hgas
  obtain ⟨s', ystF, hSteps, hcs, hSM, hOut, hF, _⟩ := hb s0 hOK hM hpc hstk hgas
  have hSM' : StateMatch yst' s' := by
    simpa [hF hcomp] using hSM
  have hOut' :
      ((Outcome.halt = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
       (Outcome.halt = .halt ∧ HaltedMatch yst' s')) := by
    simpa [hF hcomp] using hOut
  have hHM : HaltedMatch yst' s' := by
    rcases hOut' with ⟨hn, _⟩ | ⟨_, hH⟩
    · cases hn
    · exact hH
  have hhalted : stObs.halted = yst'.halted := by
    rw [hobs, committedState_halted]
  refine ⟨s', hSteps, hcs, ?_⟩
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    obtain ⟨hh, _⟩ := hconcl
    exact reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      obtain ⟨hsucc, hR'⟩ := hconcl
      obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
      have heq : stObs = yst' := obs_eq_of_commit hobs hhalted hh hk
      rcases hR' with ⟨hs, _, _, _⟩
      exact ⟨haltOK_of_success (heq ▸ hsucc) hHM, storageRel_account (heq ▸ hs) hSM'⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      obtain ⟨bytes, hh, herr, _⟩ := hconcl
      have hr := reverted_of_halted (hhalted ▸ hh) hHM
      exact ⟨hr.1, bytes, hr.2, herr⟩

/-- Spill branch of `bytecode_call_correct`. `GuardedRun` of the resolved raw
runtime is an explicit hypothesis (`GuardedRunOfErased`); the footprint lift
that discharges it is the remaining Checkpoint-2 goal. -/
theorem bytecode_call_correct_spill {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hne : compileErased rt = none)
    (hsp : compileSpilled rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0)
    (hG : ∀ {yst' : EvmState} {r : YulEvmCompiler.Optimizer.MemorySpillSelect.Result},
      spillRuntime? rt = some r →
      Run (evmWithExternal ExternalCalls.none ExternalCreates.none ExternalGas.any)
        (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts rt) yst0 [] yst' .halt →
      YulEvmCompiler.Optimizer.GuardedRun ExternalCalls.none ExternalCreates.none
        rt r.base r.reserved yst0 [] yst' .halt) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is := by
  let _model : ExternalModel := closedModel
  simp only [BytecodeCallCorrect]
  obtain ⟨stObs, hRC, hconcl⟩ :=
    runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound rt hrt ctx w yst0 hctx hR
  obtain ⟨yst', hrun, hobs⟩ := runCommitted_lift_run .none .none .any hRC
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  obtain ⟨r, hr, hcr⟩ := compileSpilled_inv hsp
  have hrunG := hG hr hrun
  have hcompB : compileBlock rt = some is := by
    simp [compileBlock, hne, hsp]
  have ⟨b, hb⟩ :=
    compileRuntime_correct (model := closedModel) ExternalsRealized.none hcompB himm
      (.spilled r hne hr hcr rfl (guardedExternals_none r.base r.reserved) hrunG)
  refine ⟨b, ?_⟩
  intro s0 hOK hM hpc hstk hgas
  obtain ⟨s', ystF, hSteps, hcs, hSM, hOut, _, hscr⟩ := hb s0 hOK hM hpc hstk hgas
  have hscratch : ScratchRel r.base r.reserved yst' ystF :=
    hscr r hne hr
  have hHM : HaltedMatch ystF s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH⟩
    · cases hn
    · exact hH
  have hhalted : stObs.halted = yst'.halted := by
    rw [hobs, committedState_halted]
  have hhaltF : ystF.halted = yst'.halted :=
    (congrArg Obs.halted hscratch.observables_eq).symm
  have hHM' : HaltedMatch yst' s' := by
    obtain ⟨hk, hh, hM⟩ := hHM
    refine ⟨hk, ?_, hM⟩
    rw [← hhaltF]
    exact hh
  refine ⟨s', hSteps, hcs, ?_⟩
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    obtain ⟨hh, _⟩ := hconcl
    exact reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM'
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      obtain ⟨hsucc, hR'⟩ := hconcl
      obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
      have heq : stObs = yst' := obs_eq_of_commit hobs hhalted hh hk
      have hR'' : R c Γ evmKeccak w' ystF :=
        R_of_scratchRel (heq ▸ hR') hscratch
      rcases hR'' with ⟨hs, _, _, _⟩
      have hsuccF : haltSuccess f.ret v ystF.halted := by
        simpa [hhaltF, heq] using hsucc
      exact ⟨haltOK_of_success hsuccF hHM, storageRel_account hs hSM⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      obtain ⟨bytes, hh, herr, _⟩ := hconcl
      have hr' := reverted_of_halted (hhalted ▸ hh) hHM'
      exact ⟨hr'.1, bytes, hr'.2, herr⟩

theorem bytecode_trace_all {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound)
    (hE : EvmTraceRunAll is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ') :
    storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
    WorldWF c Γ (coreRun Γ calls { w with log := [] }) := by
  induction calls generalizing w σ σ' with
  | nil =>
    cases hE
    refine ⟨?_, ?_⟩
    · simpa [coreRun] using hs
    · simpa [coreRun] using WorldWF_log [] hwf
  | cons p rest ih =>
    rcases p with ⟨ctx, f, args⟩
    have hp := hcalls ⟨ctx, f, args⟩ (List.mem_cons.mpr (Or.inl rfl))
    rcases hp with ⟨hf, hk, hlenA, hW, hctxWF, hcd⟩
    have hrest : ∀ q ∈ rest, _ := fun q hq =>
      hcalls q (List.mem_cons_of_mem _ hq)
    have hE' : EvmTraceRunAll is
        (⟨ctx, fnCalldata f args⟩ :: rest.map fun q => ⟨q.1, fnCalldata q.2.1 q.2.2⟩) σ σ' := by
      simpa using hE
    cases hE' with
    | cons hstart h1 htl =>
      let yst0 := mkEvmState (fnCalldata f args) σ evmKeccak ctx
      obtain ⟨σp, hRun, hpost⟩ :=
        evmCallRun_fnCalldata c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp
          ctx f args { w with log := [] } σ hf hk hlenA hW hctxWF (by simpa using hs) rfl
          (WorldWF_log [] hwf) hcd
      have heq := evmCallRun_eq_of_start h1 hRun hstart
      rw [heq] at htl
      let w1 : World S X E :=
        let w' := Security.worldAfter (Core.denote Γ f.core args.reverse) ctx { w with log := [] }
        { w' with log := [] }
      have hs1 : storageRel c Γ evmKeccak w1.self σp := by
        dsimp [w1]
        cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          have htx' : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } =
              .ok (_, w') := htx
          simp [htx'] at hpost
          rw [Security.worldAfter_ok htx']
          exact hpost.1
        | error e =>
          have htx' : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } =
              .error e := htx
          simp [htx'] at hpost
          rw [Security.worldAfter_error htx']
          simpa [hpost] using hs
      have hwf1 : WorldWF c Γ w1 := by
        dsimp [w1]
        cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          have htx' : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } =
              .ok (_, w') := htx
          simp [htx'] at hpost
          rw [Security.worldAfter_ok htx']
          exact WorldWF_log [] hpost.2
        | error e =>
          have htx' : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } =
              .error e := htx
          simp [htx'] at hpost
          rw [Security.worldAfter_error htx']
          exact WorldWF_log [] hwf
      obtain ⟨hs', hwf'⟩ := ih w1 σp σ' hs1 rfl hwf1 hrest htl
      refine ⟨?_, ?_⟩
      · simpa [coreRun, w1] using hs'
      · simpa [coreRun, w1] using hwf'

end Proof

end Lsc.Compiler
