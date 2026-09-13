import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.DispatchExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.EvmDetTheorems
import Lsc.Compiler.ExtOracleTheorems
import Lsc.Compiler.Proof.SpillOpen
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

namespace Proof

theorem bytecode_call_correct_ext {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hAgr : ExtAgree ctx.self w.ext yst0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt c Γ evmKeccak o ctx w yst0 rt is := by
  intro st' out hrun
  have hpred : EvmCallRunExt c Γ evmKeccak o ctx w yst0 st' out :=
    runtimeBlock_correct_ext c Γ hΓ evmKeccak hκ o
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hAgr hOr hNR
      st' out hrun
  refine ⟨hpred, ?_⟩
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have ⟨b, hb0⟩ := compileBlock_open_sim hCalls hrt hcomp himm hrun
  let stObs := committedState yst0 st'
  have hobs : stObs = committedState yst0 st' := rfl
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  rcases hstart with ⟨hOK, hM, hpc, hstk⟩
  obtain ⟨s', ystF, hSteps, hcs, hSM, hOut, hFe, hFs⟩ :=
    hb0 s0 hOK hM hpc hstk hgas
  have ⟨hstor, hhalt⟩ := ystF_agree hcomp hFe hFs
  have hξeq := ystF_foreign hcomp hFe hFs
  have hH : Halted s' := Halted_of_compile_out hcs hOut
  have ho : out = Outcome.halt := by
    simp only [EvmCallRunExt] at hpred
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hpred
      exact hpred.1
    | some f =>
      simp only [hsel] at hpred
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx w with
      | ok prod =>
        simp only [htx] at hpred
        exact hpred.1
      | error e =>
        simp only [htx] at hpred
        rcases hpred with ⟨_, ⟨ho', _⟩⟩
        exact ho'
  have hHM : HaltedMatch st' s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH'⟩
    · cases (hn.symm.trans ho)
    · exact HaltedMatch_of_ystF hH' hhalt
  have hpost : stObs.storage = postStorage yst0 s' := by
    simp only [EvmCallRunExt] at hpred
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hpred
      rcases hpred with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hpred
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx w with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hpred
        rcases hpred with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postStorage_commit hnr, storage_eq_account hSM, hstor, heq]
      | error e =>
        simp only [htx] at hpred
        rcases hpred with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
  have hpostξ : evmForeign stObs = postForeign yst0 s' := by
    simp only [EvmCallRunExt] at hpred
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hpred
      rcases hpred with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hpred
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx w with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hpred
        rcases hpred with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postForeign_commit hnr, foreign_eq_account hSM, hξeq, heq]
      | error e =>
        simp only [htx] at hpred
        rcases hpred with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
  refine ⟨⟨s', hSteps, hH⟩, ?_⟩
  intro s'' hS'' hH''
  rw [steps_halted_unique hS'' hSteps hH'' hH]
  exact ⟨hpost, hpostξ⟩

theorem evmCallRunExtAll_of_progress {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hAgr : ExtAgree ctx.self w.ext yst0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunExtAll c Γ evmKeccak o ctx w is yst0 σ' ξ' := by
  obtain ⟨st', out, hrun⟩ :=
    yul_progress c Γ hΓ evmKeccak hκ o hctor hS2 hlen hbound rt hrt
      ctx w yst0 hctx hR hNR
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hAgr hOr hNR himm0
      st' out hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, ?_⟩
  obtain ⟨b, hb⟩ := hEvm
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  obtain ⟨hex, huni⟩ := hb s0 hstart hgas
  refine ⟨hex, ?_⟩
  intro s'' hS hH
  refine ⟨(huni s'' hS hH).1, (huni s'' hS hH).2, ?_⟩
  simp only [EvmCallRunExt] at hpred
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hpred ⊢
    rcases hpred with ⟨_, ⟨hh, _⟩⟩
    exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩
  | some f =>
    simp only [hsel] at hpred ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
        ctx w with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hpred ⊢
      rcases hpred with ⟨_, hsucc, hR', hAgr'⟩
      exact ⟨hR'.1, stObs, rfl, rfl, hR', hAgr'⟩
    | error e =>
      simp only [htx] at hpred ⊢
      rcases hpred with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

end Proof

end Lsc.Compiler
