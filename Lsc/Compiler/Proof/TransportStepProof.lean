import Lsc.Compiler.Transport.Defs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Per-call transport simulation used by `transport_trace` / `_ext`.
Statements live in `TransportTheorems`; this file holds the proofs.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

namespace Proof

theorem transport_step (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (ctx : Ctx) (cd : List UInt8) (w : World S X E) (σ : U256 → U256)
    (hctxWF : CtxWF ctx) (hcd : cd.length < wordBound)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w) :
    let yst0 := mkEvmState cd σ evmKeccak ctx
    ∃ σ', EvmCallRun T.is yst0 σ' ∧
      match decodeCall T ctx cd with
      | none => σ' = σ
      | some c =>
          let w' := { step (.call c) w with log := [] }
          storageRel T.c T.Γ evmKeccak w'.self σ' ∧ WorldWF T.c T.Γ w' := by
  intro yst0
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmState _ _ _ _ hctxWF hcd
  have hR : R T.c T.Γ evmKeccak w yst0 :=
    R_mkEvmState evmKeccak w cd σ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmState_immutable _ _ _ _ k
  have hLock : LockFree yst0 := by
    simp only [yst0, mkEvmState]
    rfl
  obtain ⟨σ', hRun, hpost⟩ :=
    evmCallRun_of_correct T.c T.Γ T.lawful T.hκ hcf T.hctor T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR himm0 hLock
  refine ⟨σ', hRun, ?_⟩
  rw [mkEvmState_calldata] at hpost
  cases hsel : selectedFn T.c cd with
  | none =>
    have hdec : decodeCall T ctx cd = none := by simp [decodeCall, hsel]
    simp only [hsel] at hpost
    simp [hdec]
    simpa [yst0, mkEvmState_storage] using hpost
  | some f =>
    obtain ⟨fn, hfn, heq⟩ := T.codec.decodeFn_of_mem f (selectedFn_mem hsel)
    have hdec : decodeCall T ctx cd =
        some (Call.ofCtx ctx fn (T.codec.decode fn (decodeArgs f cd))) := by
      simp [decodeCall, hsel, hfn]
    simp only [hsel] at hpost
    simp only [hdec]
    rw [step_ofCtx]
    have hwa := core_exec_cd T heq ctx w cd
    rw [← hwa]
    cases htx : Tx.run (Core.denote T.Γ f.core (decodeArgs f cd).reverse) ctx w with
    | ok prod =>
      rcases prod with ⟨_, w'⟩
      simp only [htx] at hpost
      simp [worldAfter_ok htx]
      exact ⟨hpost.1, WorldWF_log [] hpost.2⟩
    | error e =>
      simp only [htx] at hpost
      simp [worldAfter_error htx]
      refine ⟨?_, WorldWF_log [] hwf⟩
      simpa [yst0, mkEvmState_storage, hpost] using hs


theorem transport_step_ext (T : TransportSetup S ExtState E ε)
    (Xpkg : TransportBindings S E ε T)
    (ctx : Ctx) (cd : List UInt8) (w : World S ExtState E)
    (σ : U256 → U256) (ξ : Foreign)
    (hctxWF : CtxWF ctx) (hcd : cd.length < wordBound)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hAgr : ExtAgree ctx.self w.ext (mkEvmStateExt cd σ ξ evmKeccak ctx))
    (hOr : w.oracle = Oracle.ofExt Xpkg.oracle)
    (hNR : ExtOracle.NoReentry Xpkg.oracle ctx.self) :
    let yst0 := mkEvmStateExt cd σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ T.is yst0 σ' ξ' ∧
      match decodeCall T ctx cd with
      | none => σ' = σ ∧ ξ' = evmForeign yst0
      | some c =>
          let w' : World S ExtState E := { step (.call c) w with log := [] }
          storageRel T.c T.Γ evmKeccak w'.self σ' ∧ WorldWF T.c T.Γ w' ∧
            ∃ stObs : EvmState,
              stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                ExtAgree ctx.self w'.ext stObs := by
  intro yst0
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R T.c T.Γ evmKeccak w yst0 :=
    R_mkEvmStateExt evmKeccak w cd σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 :=
    fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  have hLock : LockFree yst0 := LockFree_mkEvmStateExt _ _ _ _ _
  obtain ⟨σ', ξ', hRun, hpost⟩ :=
    evmCallRun_of_correct_ext T.c T.Γ T.lawful T.hκ
      Xpkg.oracle Xpkg.hCalls T.hctor Xpkg.hS2 T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR hAgr hOr hNR himm0 hLock
  refine ⟨σ', ξ', hRun, ?_⟩
  rw [mkEvmStateExt_calldata] at hpost
  cases hsel : selectedFn T.c cd with
  | none =>
    have hdec : decodeCall T ctx cd = none := by simp [decodeCall, hsel]
    simp only [hsel] at hpost
    simp [hdec]
    simpa [yst0, mkEvmStateExt_storage] using hpost
  | some f =>
    obtain ⟨fn, hfn, heq⟩ := T.codec.decodeFn_of_mem f (selectedFn_mem hsel)
    have hdec : decodeCall T ctx cd =
        some (Call.ofCtx ctx fn (T.codec.decode fn (decodeArgs f cd))) := by
      simp [decodeCall, hsel, hfn]
    simp only [hsel] at hpost
    simp only [hdec]
    rw [step_ofCtx]
    have hwa := core_exec_cd T heq ctx w cd
    rw [← hwa]
    cases htx : Tx.run (Core.denote T.Γ f.core (decodeArgs f cd).reverse)
        ctx w with
    | ok prod =>
      rcases prod with ⟨_, w'⟩
      rw [htx] at hpost
      rw [worldAfter_ok htx]
      rcases hpost with ⟨hs', hwf', stObs, hσ, hξ, _hR', hAgr'⟩
      exact ⟨hs', WorldWF_log [] hwf', stObs, hσ, hξ, hAgr'⟩
    | error e =>
      rw [htx] at hpost
      rw [worldAfter_error htx]
      rcases hpost with ⟨hσeq, hξeq⟩
      refine ⟨?_, WorldWF_log [] hwf, yst0, ?_, ?_, ?_⟩
      · simpa [yst0, mkEvmStateExt_storage, hσeq] using hs
      · simpa [yst0, mkEvmStateExt_storage, hσeq]
      · simpa [hξeq]
      · simpa [yst0, hlog] using hAgr

end Proof

end Lsc.Compiler
