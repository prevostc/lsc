import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.EndToEndExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.ExtOracleTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
S2 glue helpers: composition of `bytecode_call_correct_ext` into a single
`EvmCallRunξ`, and `mkEvmStateExt` framing for `ExtAgree`. Exported
guarantees live in `EndToEndExtTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

theorem evmCallRun_of_correct_ext {S E ε : Type}
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
    (himm0 : ∀ k, yst0.env.immutable k = 0)
    (hLock : LockFree yst0) :
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      match selectedFn c yst0.env.calldata with
      | none => σ' = yst0.storage ∧ ξ' = evmForeign yst0
      | some f =>
          match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
              ctx w with
          | .ok (_, w') =>
              storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
                ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                  R c Γ evmKeccak w' stObs ∧ ExtAgree ctx.self w'.ext stObs
          | .error _ => σ' = yst0.storage ∧ ξ' = evmForeign yst0 := by
  obtain ⟨st', out, hrun⟩ :=
    yul_progress c Γ hΓ evmKeccak hκ o hctor hS2 hlen hbound rt hrt
      ctx w yst0 hctx hR
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hAgr hOr himm0 hLock
      st' out hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, hEvm, ?_⟩
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
      exact ⟨hR'.1, hR'.2.2.2, stObs, rfl, rfl, hR', hAgr'⟩
    | error e =>
      simp only [htx] at hpred ⊢
      rcases hpred with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

/-- Drop the `EvmStartOK` witness; `ExtAll` is a stricter `EvmTraceRunExt`.
The converse needs a start state for every call, which `EvmTraceRunExt` does not store. -/
theorem EvmTraceRunExt_of_ExtAll {is : List Instr}
    {tr : List EvmCall} {σ ξ σ' ξ'}
    (h : EvmTraceRunExtAll is tr σ ξ σ' ξ') :
    EvmTraceRunExt is tr σ ξ σ' ξ' := by
  induction h with
  | nil => exact .nil _ _
  | cons hstart h1 htl ih => exact .cons h1 ih

theorem evmCallRun_fnCalldata_ext {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (f : FnDef) (args : List Nat) (w : World S ExtState E)
    (σ : U256 → U256) (ξ : Foreign)
    (hf : f ∈ c.functions) (hk : f.kind ≠ .constructor)
    (hlenA : args.length = f.params.length)
    (hW : ∀ n ∈ args, n < wordBound)
    (hctxWF : CtxWF ctx)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcd : (fnCalldata f args).length < wordBound)
    (hAgr : ExtAgree ctx.self w.ext
      (mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx))
    (hOr : w.oracle = Oracle.ofExt o) :
    let yst0 := mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
      | .ok (_, w') =>
          storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
            ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
              R c Γ evmKeccak w' stObs ∧ ExtAgree ctx.self w'.ext stObs
      | .error _ => σ' = σ ∧ ξ' = evmForeign yst0 := by
  intro yst0
  have hsel : selectedFn c (fnCalldata f args) = some f :=
    selectedFn_fnCalldata c f args hf hnd hlenA
  have hdec : decodeArgs f (fnCalldata f args) = args :=
    decodeArgs_fnCalldata f args hk hlenA hW
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R c Γ evmKeccak w yst0 := R_mkEvmStateExt evmKeccak w _ σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  have hLock : LockFree yst0 := LockFree_mkEvmStateExt _ _ _ _ _
  obtain ⟨σ', ξ', hRun, hpost⟩ :=
    evmCallRun_of_correct_ext c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hAgr hOr himm0 hLock
  refine ⟨σ', ξ', hRun, ?_⟩
  rw [mkEvmStateExt_calldata] at hpost
  simp only [hsel] at hpost
  rw [hdec] at hpost
  rw [show yst0.storage = σ from mkEvmStateExt_storage _ _ _ _ _] at hpost
  exact hpost

end Lsc.Compiler
