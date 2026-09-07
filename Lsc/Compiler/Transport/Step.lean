import Lsc.Compiler.Transport.Defs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Per-call transport steps (`transport_step` / `transport_step_ext`).
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

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
  obtain ⟨σ', hRun, hpost⟩ :=
    evmCallRun_of_correct T.c T.Γ T.lawful T.hκ hcf T.hctor T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR himm0
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


variable {I : Interface}

theorem transport_step_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (ctx : Ctx) (cd : List UInt8) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hctxWF : CtxWF ctx) (hcd : cd.length < wordBound)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hRX : RXs Xpkg.bs w (mkEvmStateExt cd σ ξ evmKeccak ctx))
    (hBindNe : BindEnvs.neSelf Xpkg.bs ctx.self w.self)
    (hconf : BindEnvs.conforms Xpkg.bs ctx.self w.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    let yst0 := mkEvmStateExt cd σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ T.is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match decodeCall T ctx cd with
        | none => σ' = σ ∧ ξ' = evmForeign yst0
        | some c =>
            let wfo : World S X E := { w with faults := fo }
            let w' : World S X E := { step (.call c) wfo with log := [] }
            storageRel T.c T.Γ evmKeccak w'.self σ' ∧ WorldWF T.c T.Γ w' ∧
              ∃ stObs : EvmState,
                stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                  RXs Xpkg.bs w' stObs := by
  intro yst0
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R T.c T.Γ evmKeccak w yst0 :=
    R_mkEvmStateExt evmKeccak w cd σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 :=
    fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  obtain ⟨σ', ξ', hRun, fo, hpost⟩ :=
    evmCallRun_of_correct_ext (I := I) Xpkg.bs T.c T.Γ T.lawful T.hκ
      Xpkg.oracle Xpkg.hCalls T.hctor Xpkg.hS2 T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR hRX Xpkg.hign hBindNe hconf
      Xpkg.hsame Xpkg.horth hinj Xpkg.hBind Xpkg.hslot himm0
  refine ⟨σ', ξ', hRun, fo, ?_⟩
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
    let wfo : World S X E := { w with faults := fo }
    have hwa := core_exec_cd T heq ctx wfo cd
    rw [← hwa]
    cases htx : Tx.run (Core.denote T.Γ f.core (decodeArgs f cd).reverse)
        ctx wfo with
    | ok prod =>
      rcases prod with ⟨_, w'⟩
      rw [htx] at hpost
      rw [worldAfter_ok htx]
      rcases hpost with ⟨hs', hwf', stObs, hσ, hξ, hRX'⟩
      exact ⟨hs', WorldWF_log [] hwf', stObs, hσ, hξ, hRX'⟩
    | error e =>
      rw [htx] at hpost
      rw [worldAfter_error htx]
      refine ⟨?_, WorldWF_of_self (w := w) rfl hwf, yst0, ?_, ?_, ?_⟩
      · simpa [yst0, mkEvmStateExt_storage, hpost] using hs
      · simpa [hpost, yst0, mkEvmStateExt_storage]
      · simpa [hpost]
      · exact RXs_irrel_log_faults (fo := fo) ([] : List E) hRX

theorem RXs_dummy_of_ξ {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    (hF : BindEnvs.ofState_foreign bs)
    (self : Address) (w : World S X E)
    (σ ξ σ₁ ξ₁ : _) (κ : List UInt8 → U256)
    (hne : BindEnvs.neSelf bs self w.self)
    (hξ : ∀ e ∈ bs,
      ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
      ξ (BitVec.ofNat 256 (e.bind.addr w.self)))
    (hRX : RXs bs w (mkEvmStateExt ([] : List UInt8) σ ξ κ (dummyCtx self))) :
    RXs bs w (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ κ (dummyCtx self)) := by
  refine RXs_of_foreign hF ?_ hRX
  intro e he k
  have hne' := hne e he
  have hloc :
      evmForeign (mkEvmStateExt ([] : List UInt8) σ ξ κ (dummyCtx self))
        (BitVec.ofNat 256 (e.bind.addr w.self)) k =
      ξ (BitVec.ofNat 256 (e.bind.addr w.self)) k := by
    simp [dummyCtx, mkEvmStateExt_foreign, hne']
  have hloc' :
      evmForeign (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ κ (dummyCtx self))
        (BitVec.ofNat 256 (e.bind.addr w.self)) k =
      ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) k := by
    simp [dummyCtx, mkEvmStateExt_foreign, hne']
  simp [hloc, hloc', hξ e he]

end Lsc.Compiler
