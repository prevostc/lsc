import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.DispatchExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.EvmDetTheorems
import Lsc.Compiler.ExtOracle
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

theorem bytecode_call_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self (toCalls o))
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt bs c Γ evmKeccak (toCalls o) ctx w yst0 rt is := by
  intro st' out hrun
  have hpred : EvmCallRunExt bs c Γ evmKeccak (toCalls o) ctx w yst0 st' out :=
    runtimeBlock_correct_ext (I := I) bs c Γ hΓ evmKeccak hκ (toCalls o)
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot
      st' out hrun
  refine ⟨hpred, ?_⟩
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have ⟨b, hb0⟩ := compileBlock_open_sim hCalls hrt hcomp himm hrun
  obtain ⟨fo, hconcl⟩ := hpred
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
    · exact HaltedMatch_of_ystF hH' hhalt
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
        rw [postStorage_commit hnr, storage_eq_account hSM, hstor, heq]
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
        rw [postForeign_commit hnr, foreign_eq_account hSM, hξeq, heq]
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
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self (toCalls o))
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunExtAll bs c Γ evmKeccak (toCalls o) ctx w is yst0 σ' ξ' := by
  obtain ⟨st', out, hrun⟩ :=
    yul_progress (I := I) bs c Γ hΓ evmKeccak hκ (toCalls o) (toCalls_total o)
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hconf hBind hslot
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext (I := I) bs c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot himm0
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
