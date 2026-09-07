import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.DispatchExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.EvmDetTheorems
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of S2 bytecode glue. Statements live in `EndToEndExtTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

theorem externalsRealized_open {calls : ExternalCalls}
    (h : CallsRealized calls) :
    ExternalsRealized (openModel calls) :=
  ⟨h, CreatesRealized.none, GasCallsRealized.noneOracle calls⟩

namespace Proof

theorem bytecode_call_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt bs c Γ evmKeccak calls ctx w yst0 rt is := by
  intro st' o hrun
  have hpred : EvmCallRunExt bs c Γ evmKeccak calls ctx w yst0 st' o :=
    runtimeBlock_correct_ext (I := I) bs c Γ hΓ evmKeccak hκ calls
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot
      st' o hrun
  refine ⟨hpred, ?_⟩
  let _model : ExternalModel := openModel calls
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have hce : compileErased rt = some is := hcomp
  have ⟨b, hb⟩ :=
    compile_correct (model := openModel calls) (externalsRealized_open hCalls)
      hce himm hrun
  obtain ⟨fo, hconcl⟩ := hpred
  let stObs := committedState yst0 st'
  have hobs : stObs = committedState yst0 st' := rfl
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  rcases hstart with ⟨hOK, hM, hpc, hstk⟩
  obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
  have hH : Halted s' := Halted_of_compile_out hcs hOut
  have ho : o = Outcome.halt := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      exact hconcl.1
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        simp only [htx] at hconcl
        exact hconcl.1
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨ho', _⟩⟩
        exact ho'
  have hHM : HaltedMatch st' s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH'⟩
    · cases (hn.symm.trans ho)
    · exact hH'
  have hpost : stObs.storage = postStorage yst0 s' := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      rcases hconcl with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postStorage_commit hnr, storage_eq_account hSM, heq]
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
  have hpostξ : evmForeign stObs = postForeign yst0 s' := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      rcases hconcl with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postForeign_commit hnr, foreign_eq_account hSM, heq]
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
  refine ⟨⟨s', hSteps, hH⟩, ?_⟩
  intro s'' hS'' hH''
  rw [steps_halted_unique hS'' hSteps hH'' hH]
  exact ⟨hpost, hpostξ⟩

theorem evmCallRunExtAll_of_progress {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunExtAll bs c Γ evmKeccak calls ctx w is yst0 σ' ξ' := by
  obtain ⟨st', o, hrun⟩ :=
    yul_progress (I := I) bs c Γ hΓ evmKeccak hκ calls htot hctor hS2 hlen hbound
      rt hrt ctx w yst0 hctx hR hconf hBind hslot
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext (I := I) bs c Γ hΓ hκ calls hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot himm0
      st' o hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, ?_⟩
  obtain ⟨b, hb⟩ := hEvm
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  obtain ⟨hex, huni⟩ := hb s0 hstart hgas
  refine ⟨hex, ?_⟩
  intro s'' hS hH
  refine ⟨(huni s'' hS hH).1, (huni s'' hS hH).2, ?_⟩
  obtain ⟨fo, hconcl⟩ := hpred
  refine ⟨fo, ?_⟩
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    rcases hconcl with ⟨_, ⟨hh, _⟩⟩
    exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
        ctx { w with faults := fo } with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨_, hsucc, hR', hRX'⟩
      exact ⟨hR'.1, stObs, rfl, rfl, hR', hRX'⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

end Proof

end Lsc.Compiler
