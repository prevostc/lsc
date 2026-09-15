import Lsc.Compiler.Transport.Defs
import Lsc.Compiler.Transport.Abi
import Lsc.Compiler.Proof.TransportStepProof
import Lsc.Compiler.Proof.TransportSlotsProof
import Lsc.Compiler.Proof.CallFreeCongr

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Proofs of generic bytecode ↔ Security transport. Statements live in `TransportTheorems`. An arbitrary halted EVM call list
decodes to a well-formed Security trace (dispatcher rejects dropped). S1 is
`transport_*`; S2 threads `Oracle.ofExt` / `NoReentry` as `transport_*_ext`. Worlds are
log-cleared (`w.log = []`): Yul `mkEvmState*` starts empty, and Security
`Inv`/`claim` on Token/Vault ignore `log`.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

namespace Proof

theorem post_congr_callFree {S X E ε} (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    (worldAfter (T.spec.exec fn args) ctx w).self =
      (worldAfter (T.spec.exec fn args) ctx w').self ∧
    (worldAfter (T.spec.exec fn args) ctx w).ext =
      (worldAfter (T.spec.exec fn args) ctx w').ext := by
  have h1 := T.codec.core_exec fn args ctx w
  have h2 := T.codec.core_exec fn args ctx w'
  rw [← h1, ← h2]
  exact worldAfter_callFree_congr (T.codec.fnDef fn).core
    (hcf _ (T.codec.mem fn)) (T.codec.encode fn args).reverse ctx w w' hs he

/-- Universal S1: every halted EVM run of an arbitrary calldata list is
`storageRel` of `Security.run` of the decoded trace (dispatcher rejects
dropped). Requires `w.log = []`. -/
theorem transport_trace (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hE : EvmTraceRunAll T.is calls σ σ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      storageRel T.c T.Γ evmKeccak (run tr w).self σ' ∧
      WorldWF T.c T.Γ { run tr w with log := [] } := by
  refine ⟨wf_decodeTrace T self calls hWF, ?_⟩
  induction calls generalizing w σ σ' with
  | nil =>
    cases hE
    refine ⟨?_, ?_⟩
    · simpa [decodeTrace, run] using hs
    · simpa [decodeTrace, run] using WorldWF_log [] hwf
  | cons call rest ih =>
    have ⟨hctxWF, hcd⟩ := (CallsWF.head hWF).2.2
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      obtain ⟨σ₁, hRun, hpost⟩ :=
        transport_step T hcf call.ctx call.calldata w σ hctxWF hcd hs hlog hwf
      have heq := evmCallRun_eq_of_start h1 hRun hstart
      rw [heq] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        have htl' : EvmTraceRunAll T.is rest σ σ' := by simpa [hpost] using htl
        simpa [decodeTrace, hdec] using
          ih (w := w) (σ := σ) (σ' := σ') hs hlog hwf hWFtl htl'
      | some c =>
        simp only [hdec] at hpost
        let w1 : World S X E := { step (.call c) w with log := [] }
        have ⟨hs', hwf'⟩ :=
          ih (w := w1) (σ := σ₁) (σ' := σ') hpost.1 rfl hpost.2 hWFtl htl
        have hself : (run (.call c :: decodeTrace T rest) w).self =
            (run (decodeTrace T rest) w1).self :=
          post_congr_run hpc (decodeTrace T rest) (step (.call c) w) w1 rfl rfl
        refine ⟨?_, ?_⟩
        · simp only [decodeTrace, hdec]
          rwa [hself]
        · simp only [decodeTrace, hdec]
          exact WorldWF_of_self (w := { run (decodeTrace T rest) w1 with log := [] })
            hself.symm hwf'

theorem transport_exists (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (tr : List (Step T.spec)) (w : World S X E) (σ : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) :
    ∃ σ', EvmTraceRun T.is (encodeCalls T tr) σ σ' ∧
      storageRel T.c T.Γ evmKeccak
        (run (decodeTrace T (encodeCalls T tr)) { w with log := [] }).self σ' ∧
      WorldWF T.c T.Γ
        { run (decodeTrace T (encodeCalls T tr)) { w with log := [] } with log := [] } := by
  induction tr generalizing w σ with
  | nil =>
    refine ⟨σ, EvmTraceRun.nil σ, ?_, ?_⟩
    · simpa [encodeCalls, decodeTrace, run] using hs
    · simpa [encodeCalls, decodeTrace, run] using WorldWF_log [] hwf
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls] using
        ih (w := w) (σ := σ) hs hwf (by simpa [EncodeBounded] using hb)
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      have hf := T.codec.mem c.fn
      have hk := T.hctor _ hf
      have hlenA := T.codec.encode_length c.fn c.args
      have hcd : (fnCalldata (T.codec.fnDef c.fn)
          (T.codec.encode c.fn c.args)).length < wordBound := by
        rw [length_fnCalldata, hlenA]
        exact T.hbound _ hf
      obtain ⟨σ₁, h1, hpost⟩ :=
        evmCallRun_fnCalldata T.c T.Γ T.lawful T.hκ hcf T.hctor T.hlen T.hbound
          T.nodup T.rt T.hrt T.is T.hcomp c.toCtx (T.codec.fnDef c.fn)
          (T.codec.encode c.fn c.args) { w with log := [] } σ hf hk hlenA hWargs
          hctxWF (by simpa using hs) rfl (WorldWF_log [] hwf) hcd
      have hdecC := encodeCall_decode T c hWargs
      have hwa := T.codec.core_exec c.fn c.args c.toCtx { w with log := [] }
      let w1 : World S X E :=
        { worldAfter (T.spec.exec c.fn c.args) c.toCtx { w with log := [] }
          with log := [] }
      have hs1 : storageRel T.c T.Γ evmKeccak w1.self σ₁ := by
        cases htx : Tx.run
            (Core.denote T.Γ (T.codec.fnDef c.fn).core
              (T.codec.encode c.fn c.args).reverse)
            c.toCtx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_ok htx]
          exact hpost.1
        | error e =>
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_error htx]
          simpa [hpost] using hs
      have hwf1 : WorldWF T.c T.Γ w1 := by
        cases htx : Tx.run
            (Core.denote T.Γ (T.codec.fnDef c.fn).core
              (T.codec.encode c.fn c.args).reverse)
            c.toCtx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_ok htx]
          exact WorldWF_log [] hpost.2
        | error e =>
          simp only [w1]
          rw [← hwa, worldAfter_error htx]
          exact WorldWF_log [] hwf
      obtain ⟨σ', htl, hs', hwf'⟩ := ih w1 σ₁ hs1 hwf1 htlB
      have hdt : decodeTrace T (encodeCall T c :: encodeCalls T rest) =
          .call c :: decodeTrace T (encodeCalls T rest) := by
        simp [encodeCall] at hdecC
        simp [decodeTrace, encodeCall, hdecC]
      have hself := post_congr_run hpc (decodeTrace T (encodeCalls T rest))
          (step (.call c) { w with log := [] }) w1 rfl rfl
      refine ⟨σ',
        EvmTraceRun.cons (call := encodeCall T c) (tr := encodeCalls T rest)
          (yst0 := mkEvmState (encodeCall T c).calldata σ evmKeccak c.toCtx)
          (mkEvmState_calldata _ _ _ _) (mkEvmState_storage _ _ _ _) h1 htl, ?_, ?_⟩
      · simp only [encodeCalls, hdt, run_cons]
        rwa [hself]
      · simp only [encodeCalls, hdt, run_cons]
        exact WorldWF_of_self (w := { run (decodeTrace T (encodeCalls T rest)) w1
            with log := [] }) hself.symm hwf'

/-! ## S2 (oracle / foreign storage)

Each EVM call in `EvmTraceRunExtAll` starts from `mkEvmStateExt`, which
keeps executing storage `σ` and foreign persistent storage `ξ` and
rebuilds the rest of the env. `reframeExt` puts the high-level world
on that same skeleton so `ExtAgree` is definitional; `InvReframe` is
the corresponding `Inv` obligation (it replaces `hInvF`).
-/

theorem transport_trace_ext (T : TransportSetup S ExtState E ε)
    (Xpkg : TransportBindings S E ε T)
    (self : Address) (calls : List EvmCall)
    (w : World S ExtState E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hOr : w.oracle = Oracle.ofExt Xpkg.oracle)
    (Inv : World S ExtState E → Prop)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvR : InvReframe Inv Xpkg.oracle)
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      ∃ w' : World S ExtState E,
        storageRel T.c T.Γ evmKeccak w'.self σ' ∧
        WorldWF T.c T.Γ w' ∧
        ExtAgree self w'.ext
          (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
        Inv w' := by
  refine ⟨wf_decodeTrace T self calls hWF, ?_⟩
  -- Each call reframes onto `Oracle.ofExt`; `hOr` is the user's starting world.
  clear hOr
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    let w0 := reframeExt (S := S) (E := E) Xpkg.oracle
      { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    refine ⟨w0, ?_, ?_, ?_, ?_⟩
    · simpa [w0] using hs
    · exact WorldWF_of_self (w := { w with log := ([] : List E) }) (by simp [w0])
        (WorldWF_log ([] : List E) hwf)
    · simpa [w0, dummyCtx] using
        ExtAgree_reframeExt (S := S) (E := E) Xpkg.oracle
          { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    · exact hInvR { w with log := ([] : List E) } ([] : List UInt8) σ ξ
        (dummyCtx self) (hInvL w ([] : List E) hw)
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      let wF := reframeExt Xpkg.oracle w call.calldata σ ξ call.ctx
      have hAgr := ExtAgree_reframeExt Xpkg.oracle w call.calldata σ ξ call.ctx
      have hsF : storageRel T.c T.Γ evmKeccak wF.self σ := by simpa [wF] using hs
      have hlogF : wF.log = [] := by simpa [wF] using hlog
      have hwfF : WorldWF T.c T.Γ wF :=
        WorldWF_of_self (w := w) (by simp [wF]) hwf
      obtain ⟨σ₁, ξ₁, hRun, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata wF σ ξ hctxWF hcd
          hsF hlogF hwfF hAgr (by simp [wF])
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, _hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        simpa [decodeTrace, hdec] using
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl hw htl
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, _hσ, _hξobs, _hAgrObs⟩
        let w1 : World S ExtState E := { step (.call c) wF with log := [] }
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hwFInv : Inv wF := hInvR w call.calldata σ ξ call.ctx hw
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wF (htgtc.trans htgt)
            (by simpa [hsend] using hne) hwFInv)
        have ⟨w', hs', hwf', hAgr', hInv'⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl hw1 htl
        exact ⟨w', hs', hwf', hAgr', hInv'⟩

/-- S2 claim transport: `NoUnauthorizedDecrease` along the reframed fold
from `transport_trace_ext`, when `Auth`/`Inv` ignore log and `claim`
depends only on storage (`Claim.ofSelf`). -/
theorem transport_claim_ext (T : TransportSetup S ExtState E ε)
    (Xpkg : TransportBindings S E ε T)
    (Inv : World S ExtState E → Prop) (claim : Claim S ExtState E)
    (Auth : AuthPred T.spec)
    (self : Address) (a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvR : InvReframe Inv Xpkg.oracle)
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (hC : ∀ w w' x, w.self = w'.self → claim x w = claim x w')
    (calls : List EvmCall)
    (w : World S ExtState E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hOr : w.oracle = Oracle.ofExt Xpkg.oracle)
    (hA : NoAuthAlong Auth a (decodeTrace T calls) w)
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    ∃ w' : World S ExtState E,
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      ExtAgree self w'.ext
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w ≤ claim a w' := by
  clear hOr
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    let w0 := reframeExt (S := S) (E := E) Xpkg.oracle
      { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    refine ⟨w0, ?_, ?_, ?_, ?_, Nat.le_of_eq (hC w w0 a (by simp [w0]))⟩
    · simpa [w0] using hs
    · exact WorldWF_of_self (w := { w with log := ([] : List E) }) (by simp [w0])
        (WorldWF_log ([] : List E) hwf)
    · simpa [w0, dummyCtx] using
        ExtAgree_reframeExt (S := S) (E := E) Xpkg.oracle
          { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    · exact hInvR { w with log := ([] : List E) } ([] : List UInt8) σ ξ
        (dummyCtx self) (hInvL w ([] : List E) hw)
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      let wF := reframeExt Xpkg.oracle w call.calldata σ ξ call.ctx
      have hAgr := ExtAgree_reframeExt Xpkg.oracle w call.calldata σ ξ call.ctx
      have hsF : storageRel T.c T.Γ evmKeccak wF.self σ := by simpa [wF] using hs
      have hlogF : wF.log = [] := by simpa [wF] using hlog
      have hwfF : WorldWF T.c T.Γ wF :=
        WorldWF_of_self (w := w) (by simp [wF]) hwf
      obtain ⟨σ₁, ξ₁, hRun, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata wF σ ξ hctxWF hcd
          hsF hlogF hwfF hAgr (by simp [wF])
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, _hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        have ⟨w', hs', hwf', hAgr', hInv', hle⟩ :=
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl
            (by simpa [decodeTrace, hdec] using hA) hw htl
        exact ⟨w', hs', hwf', hAgr', hInv', hle⟩
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, _hσ, _hξobs, _hAgrObs⟩
        let w1 : World S ExtState E := { step (.call c) wF with log := [] }
        have hwFInv : Inv wF := hInvR w call.calldata σ ξ call.ctx hw
        have ⟨hna, hAtl⟩ : ¬ Auth a c w ∧
            NoAuthAlong Auth a (decodeTrace T rest) (step (.call c) w) := by
          simpa [decodeTrace, hdec, NoAuthAlong] using hA
        have hle1 : claim a w ≤ claim a w1 := by
          have hna' : ¬ Auth a c wF :=
            ((hAirr [.call c] w wF).mp ⟨hna, trivial⟩).1
          have hcw : claim a w = claim a wF := hC w wF a (by simp [wF])
          have hcw1 : claim a w1 = claim a (step (.call c) wF) :=
            hC w1 (step (.call c) wF) a (by simp [w1])
          have hnot : ¬ claim a w1 < claim a w := by
            intro hlt
            have hlt' : claim a (step (.call c) wF) < claim a wF := by
              simpa [hcw1, hcw] using hlt
            exact hna' (hN c wF a hwFInv hlt')
          exact Nat.le_of_not_lt hnot
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wF (htgtc.trans htgt)
            (by simpa [hsend] using hne) hwFInv)
        have ⟨w', hs', hwf', hAgr', hInv', hle⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl
            ((hAirr (decodeTrace T rest) (step (.call c) w) w1).mp hAtl) hw1 htl
        exact ⟨w', hs', hwf', hAgr', hInv', Nat.le_trans hle1 hle⟩


theorem transport_exists_ext (T : TransportSetup S ExtState E ε)
    (Xpkg : TransportBindings S E ε T)
    (Inv : World S ExtState E → Prop)
    (self : Address)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvR : InvReframe Inv Xpkg.oracle)
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (tr : List (Step T.spec)) (w : World S ExtState E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr)     (hw : Inv w)
    (hOr : w.oracle = Oracle.ofExt Xpkg.oracle) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      ExtAgree self w'.ext
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' := by
  clear hOr
  induction tr generalizing w σ ξ with
  | nil =>
    let w0 := reframeExt (S := S) (E := E) Xpkg.oracle
      { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    refine ⟨σ, ξ, w0, EvmTraceRunExt.nil σ ξ, ?_, ?_, ?_, ?_⟩
    · simpa [w0] using hs
    · exact WorldWF_of_self (w := { w with log := ([] : List E) }) (by simp [w0])
        (WorldWF_log ([] : List E) hwf)
    · simpa [w0, dummyCtx] using
        ExtAgree_reframeExt (S := S) (E := E) Xpkg.oracle
          { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    · exact hInvR { w with log := ([] : List E) } ([] : List UInt8) σ ξ
        (dummyCtx self) (hInvL w ([] : List E) hw)
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      let wL : World S ExtState E := { w with log := ([] : List E) }
      let wF := reframeExt Xpkg.oracle wL (encodeCall T c).calldata σ ξ c.toCtx
      have hAgr := ExtAgree_reframeExt Xpkg.oracle wL
        (encodeCall T c).calldata σ ξ c.toCtx
      obtain ⟨σ₁, ξ₁, h1, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          wF σ ξ hctxWF hcd (by simpa [wF] using hs) (by simp [wF, wL])
          (WorldWF_of_self (w := wL) (by simp [wF]) (WorldWF_log [] hwf))
          hAgr (by simp [wF])
      simp only [hdecC] at hpost
      let w1 : World S ExtState E := { step (.call c) wF with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, _hσ, _hξobs, _hAgrObs⟩
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wF (by simpa [wF] using htgt)
          (by simpa [wF] using hne)
          (hInvR wL (encodeCall T c).calldata σ ξ c.toCtx (hInvL w [] hw)))
      obtain ⟨σ', ξ', w', htl, hs', hwf', hAgr', hInv'⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hAgr', hInv'⟩


/-- Forward S2 with claim monotonicity along the reframed fold of `encodeCalls`. -/
theorem transport_exists_claim_ext (T : TransportSetup S ExtState E ε)
    (Xpkg : TransportBindings S E ε T)
    (Inv : World S ExtState E → Prop) (claim : Claim S ExtState E)
    (Auth : AuthPred T.spec)
    (self a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvR : InvReframe Inv Xpkg.oracle)
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (hC : ∀ w w' x, w.self = w'.self → claim x w = claim x w')
    (tr : List (Step T.spec)) (w : World S ExtState E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hA : NoAuthAlong Auth a (callsOf tr) w)
    (hOr : w.oracle = Oracle.ofExt Xpkg.oracle) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      ExtAgree self w'.ext
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w ≤ claim a w' := by
  clear hOr
  induction tr generalizing w σ ξ with
  | nil =>
    let w0 := reframeExt (S := S) (E := E) Xpkg.oracle
      { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    refine ⟨σ, ξ, w0, EvmTraceRunExt.nil σ ξ, ?_, ?_, ?_, ?_,
      Nat.le_of_eq (hC w w0 a (by simp [w0]))⟩
    · simpa [w0] using hs
    · exact WorldWF_of_self (w := { w with log := ([] : List E) }) (by simp [w0])
        (WorldWF_log ([] : List E) hwf)
    · simpa [w0, dummyCtx] using
        ExtAgree_reframeExt (S := S) (E := E) Xpkg.oracle
          { w with log := ([] : List E) } ([] : List UInt8) σ ξ (dummyCtx self)
    · exact hInvR { w with log := ([] : List E) } ([] : List UInt8) σ ξ
        (dummyCtx self) (hInvL w ([] : List E) hw)
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls, callsOf] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw hA
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      rcases hA with ⟨hna, hAtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      let wL : World S ExtState E := { w with log := ([] : List E) }
      let wF := reframeExt Xpkg.oracle wL (encodeCall T c).calldata σ ξ c.toCtx
      have hAgr := ExtAgree_reframeExt Xpkg.oracle wL
        (encodeCall T c).calldata σ ξ c.toCtx
      obtain ⟨σ₁, ξ₁, h1, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          wF σ ξ hctxWF hcd (by simpa [wF] using hs) (by simp [wF, wL])
          (WorldWF_of_self (w := wL) (by simp [wF]) (WorldWF_log [] hwf))
          hAgr (by simp [wF])
      simp only [hdecC] at hpost
      let w1 : World S ExtState E := { step (.call c) wF with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, _hσ, _hξobs, _hAgrObs⟩
      have hwFInv : Inv wF :=
        hInvR wL (encodeCall T c).calldata σ ξ c.toCtx (hInvL w [] hw)
      have hle1 : claim a w ≤ claim a w1 := by
        have hna' : ¬ Auth a c wF :=
          ((hAirr [.call c] w wF).mp ⟨hna, trivial⟩).1
        have hcw : claim a w = claim a wF := hC w wF a (by simp [wF, wL])
        have hcw1 : claim a w1 = claim a (step (.call c) wF) :=
          hC w1 (step (.call c) wF) a (by simp [w1])
        have hnot : ¬ claim a w1 < claim a w := by
          intro hlt
          have hlt' : claim a (step (.call c) wF) < claim a wF := by
            simpa [hcw1, hcw] using hlt
          exact hna' (hN c wF a hwFInv hlt')
        exact Nat.le_of_not_lt hnot
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wF (by simpa [wF] using htgt)
          (by simpa [wF] using hne) hwFInv)
      obtain ⟨σ', ξ', w', htl, hs', hwf', hAgr', hInv', hle⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1
          ((hAirr (callsOf rest) (step (.call c) w) w1).mp hAtl)
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hAgr', hInv',
        Nat.le_trans hle1 hle⟩

end Proof

end Lsc.Compiler
