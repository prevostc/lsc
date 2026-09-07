import Lsc.Compiler.Transport.Defs
import Lsc.Compiler.Transport.Step
import Lsc.Compiler.Transport.Abi
import Lsc.Compiler.Transport.Slots

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Proofs of generic bytecode ↔ Security transport. Statements live in `TransportTheorems`. An arbitrary halted EVM call list
decodes to a well-formed Security trace (dispatcher rejects dropped). S1 is
`transport_*`; S2 threads bindings/`ξ` as `transport_*_ext`. Worlds are
log-cleared (`w.log = []`): Yul `mkEvmState*` starts empty, and Security
`Inv`/`claim` on Token/Vault ignore `log`.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

namespace Proof

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

/-! ## S2 (bindings / foreign storage) -/

variable {I : Interface}

/-- Universal S2: every halted EVM run of an arbitrary calldata list yields a
decoded well-formed Security trace and a post-world `w'` with `R`/`RX`.
`w'` is the fo-adjusted fold (Core revert keeps storage); it need not equal
`run tr w` when the EVM-chosen `fo` differs from `w.faults`. -/
theorem transport_trace_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (Inv : World S X E → Prop)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      ∃ w' : World S X E,
        storageRel T.c T.Γ evmKeccak w'.self σ' ∧
        WorldWF T.c T.Γ w' ∧
        RXs Xpkg.bs w'
          (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
        Inv w' ∧
        (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) := by
  refine ⟨wf_decodeTrace T self calls hWF, ?_⟩
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    exact ⟨{ w with log := [] }, hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, fun _ _ => rfl⟩
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      have hRXcall : RXs Xpkg.bs w
          (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx] using htgt.symm) hRX
      have hBindNe' : BindEnvs.neSelf Xpkg.bs call.ctx.self w.self := by
        simpa [htgt] using hBindNe
      have hconfCall : BindEnvs.conforms Xpkg.bs call.ctx.self w.self Xpkg.extCalls := by
        simpa [htgt] using hconf w
      obtain ⟨σ₁, ξ₁, hRun, fo, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata w σ ξ hctxWF hcd
          hs hlog hwf hRXcall hBindNe' hconfCall hinj
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        have hξeq : ∀ e ∈ Xpkg.bs,
            ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
            ξ (BitVec.ofNat 256 (e.bind.addr w.self)) := by
          intro e he
          rw [hξ]
          exact mkEvmStateExt_foreign_ne _ _ _ _ _ _ (hBindNe' e he)
        have hRX1 : RXs Xpkg.bs w
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_dummy_of_ξ Xpkg.hF self w σ ξ σ₁ ξ₁ evmKeccak hBindNe hξeq hRX
        simpa [decodeTrace, hdec] using
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl hRX1 hBindNe hinj hw htl
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
        let wfo : World S X E := { w with faults := fo }
        let w1 : World S X E := { step (.call c) wfo with log := [] }
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wfo (htgtc.trans htgt) (by simpa [hsend] using hne) (hInvF w fo hw))
        have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
          intro e he
          simpa [w1, wfo, step] using
            Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
        have hRXw1 : RXs Xpkg.bs w1
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
            (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
        have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
          BindEnvs.neSelf_of_addr hBindNe haddr
        have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
          BindEnvs.addrInj_of_addr hinj haddr
        have ⟨w', hs', hwf', hRX', hInv', haddr'⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl hRXw1 hBindNe1 hinj1 hw1 htl
        exact ⟨w', hs', hwf', hRX', hInv', fun e he => (haddr' e he).trans (haddr e he)⟩

/-- S2 claim transport: `NoUnauthorizedDecrease` along the fo-adjusted fold
(`w'` from `transport_trace_ext`), when `Auth`/`Inv` ignore log and faults. -/
theorem transport_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self : Address) (a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (hA : NoAuthAlong Auth a (decodeTrace T calls) w)
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    ∃ w' : World S X E,
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self := by
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    exact ⟨{ w with log := [] }, hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, Nat.le_refl _⟩
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      have hRXcall : RXs Xpkg.bs w
          (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx] using htgt.symm) hRX
      have hBindNe' : BindEnvs.neSelf Xpkg.bs call.ctx.self w.self := by
        simpa [htgt] using hBindNe
      have hconfCall : BindEnvs.conforms Xpkg.bs call.ctx.self w.self Xpkg.extCalls := by
        simpa [htgt] using hconf w
      obtain ⟨σ₁, ξ₁, hRun, fo, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata w σ ξ hctxWF hcd
          hs hlog hwf hRXcall hBindNe' hconfCall hinj
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        have hξeq : ∀ e ∈ Xpkg.bs,
            ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
            ξ (BitVec.ofNat 256 (e.bind.addr w.self)) := by
          intro e he
          rw [hξ]
          exact mkEvmStateExt_foreign_ne _ _ _ _ _ _ (hBindNe' e he)
        have hRX1 : RXs Xpkg.bs w
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_dummy_of_ξ Xpkg.hF self w σ ξ σ₁ ξ₁ evmKeccak hBindNe hξeq hRX
        have ⟨w', hs', hwf', hRX', hInv', hle⟩ :=
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl hRX1 hBindNe hinj
            (by simpa [decodeTrace, hdec] using hA) hw htl
        exact ⟨w', hs', hwf', hRX', hInv', hle⟩
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
        let wfo : World S X E := { w with faults := fo }
        let w1 : World S X E := { step (.call c) wfo with log := [] }
        have hwfo : Inv wfo := hInvF w fo hw
        have ⟨hna, hAtl⟩ : ¬ Auth a c w.self ∧
            NoAuthAlong Auth a (decodeTrace T rest) (step (.call c) w) := by
          simpa [decodeTrace, hdec, NoAuthAlong] using hA
        have hle1 : claim a w.self ≤ claim a w1.self := by
          have hna' : ¬ Auth a c wfo.self := by simpa [wfo] using hna
          have hnot : ¬ claim a w1.self < claim a w.self := by
            intro hlt
            have hlt' : claim a (step (.call c) wfo).self < claim a wfo.self := by
              simpa [w1, wfo] using hlt
            exact hna' (hN c wfo a hwfo hlt')
          exact Nat.le_of_not_lt hnot
        have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
          intro e he
          simpa [w1, wfo, step] using
            Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
        have hRXw1 : RXs Xpkg.bs w1
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
            (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
        have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
          BindEnvs.neSelf_of_addr hBindNe haddr
        have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
          BindEnvs.addrInj_of_addr hinj haddr
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wfo (htgtc.trans htgt) (by simpa [hsend] using hne) hwfo)
        have ⟨w', hs', hwf', hRX', hInv', hle⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl hRXw1 hBindNe1 hinj1
            ((hAirr (decodeTrace T rest) (step (.call c) w) w1).mp hAtl) hw1 htl
        exact ⟨w', hs', hwf', hRX', hInv', Nat.le_trans hle1 hle⟩

theorem transport_exists_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop)
    (self : Address)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) := by
  induction tr generalizing w σ ξ with
  | nil =>
    exact ⟨σ, ξ, { w with log := [] }, EvmTraceRunExt.nil σ ξ,
      hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, fun _ _ => rfl⟩
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw hRX hBindNe hinj
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      have hRXcall :
          RXs Xpkg.bs { w with log := ([] : List E) }
            (mkEvmStateExt (encodeCall T c).calldata σ ξ evmKeccak c.toCtx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx, Call.toCtx] using htgt.symm) hRX
      obtain ⟨σ₁, ξ₁, h1, fo, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          { w with log := ([] : List E) } σ ξ hctxWF hcd
          (by simpa using hs) rfl (WorldWF_log [] hwf) hRXcall
          (by simpa [Call.toCtx, htgt] using hBindNe)
          (by simpa [Call.toCtx, htgt] using hconf { w with log := ([] : List E) })
          hinj
      simp only [hdecC] at hpost
      let wfo : World S X E :=
        { { w with log := ([] : List E) } with faults := fo }
      let w1 : World S X E := { step (.call c) wfo with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
      have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
        intro e he
        simpa [w1, wfo, step] using Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
      have hRXw1 : RXs Xpkg.bs w1
          (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
        RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
          (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
      have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
        BindEnvs.neSelf_of_addr hBindNe haddr
      have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
        BindEnvs.addrInj_of_addr hinj haddr
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wfo (by simpa [wfo] using htgt)
          (by simpa [wfo] using hne) (hInvF _ fo (hInvL w [] hw)))
      obtain ⟨σ', ξ', w', htl, hs', hwf', hRX', hInv', haddr'⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1 hRXw1 hBindNe1 hinj1
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hRX', hInv',
        fun e he => (haddr' e he).trans (haddr e he)⟩

/-- Forward S2 with claim monotonicity along the fo-fold of `encodeCalls`. -/
theorem transport_exists_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hA : NoAuthAlong Auth a (callsOf tr) w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self := by
  induction tr generalizing w σ ξ with
  | nil =>
    exact ⟨σ, ξ, { w with log := [] }, EvmTraceRunExt.nil σ ξ,
      hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, Nat.le_refl _⟩
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls, callsOf] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw hA hRX hBindNe hinj
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      rcases hA with ⟨hna, hAtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      have hRXcall :
          RXs Xpkg.bs { w with log := ([] : List E) }
            (mkEvmStateExt (encodeCall T c).calldata σ ξ evmKeccak c.toCtx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx, Call.toCtx] using htgt.symm) hRX
      obtain ⟨σ₁, ξ₁, h1, fo, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          { w with log := ([] : List E) } σ ξ hctxWF hcd
          (by simpa using hs) rfl (WorldWF_log [] hwf) hRXcall
          (by simpa [Call.toCtx, htgt] using hBindNe)
          (by simpa [Call.toCtx, htgt] using hconf { w with log := ([] : List E) })
          hinj
      simp only [hdecC] at hpost
      let wfo : World S X E :=
        { { w with log := ([] : List E) } with faults := fo }
      let w1 : World S X E := { step (.call c) wfo with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
      have hwfo : Inv wfo := hInvF _ fo (hInvL w [] hw)
      have hle1 : claim a w.self ≤ claim a w1.self := by
        have hna' : ¬ Auth a c wfo.self := by simpa [wfo] using hna
        have hnot : ¬ claim a w1.self < claim a w.self := by
          intro hlt
          have hlt' : claim a (step (.call c) wfo).self < claim a wfo.self := by
            simpa [w1, wfo] using hlt
          exact hna' (hN c wfo a hwfo hlt')
        exact Nat.le_of_not_lt hnot
      have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
        intro e he
        simpa [w1, wfo, step] using Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
      have hRXw1 : RXs Xpkg.bs w1
          (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
        RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
          (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
      have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
        BindEnvs.neSelf_of_addr hBindNe haddr
      have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
        BindEnvs.addrInj_of_addr hinj haddr
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wfo (by simpa [wfo] using htgt)
          (by simpa [wfo] using hne) hwfo)
      obtain ⟨σ', ξ', w', htl, hs', hwf', hRX', hInv', hle⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1
          ((hAirr (callsOf rest) (step (.call c) w) w1).mp hAtl) hRXw1 hBindNe1 hinj1
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hRX', hInv',
        Nat.le_trans hle1 hle⟩

end Proof

end Lsc.Compiler
