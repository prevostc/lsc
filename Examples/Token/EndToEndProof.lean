import Examples.Token.EndToEnd
import Examples.Token.CompileTheorems
import Examples.Token.SecurityTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Proofs of Token bytecode security. Statements live in `TokenEndToEndTheorems`.
-/

open Lsc Lsc.Compiler Lsc.Security Token
open YulSemantics.EVM
open YulEvmCompiler (compile Instr)

namespace Token

namespace Proof

theorem token_bytecode_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (a : Address) (σ : U256 → U256)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (ha : Nat.lt a wordBound) :
    ∀ σ', EvmTraceRunAll is calls σ σ' →
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat := by
  intro σ' hE
  let T := mkTokenSetup hκ rt hrt is hcomp
  have ⟨_, hs', hwf'⟩ :=
    transport_trace T (fun f hf => token_fn_callFree hf) (post_congr_callFree T (fun f hf => token_fn_callFree hf)) self calls w σ σ'
      hs hlog hwf hWF hE
  have hR : RelyAlong (fun _ _ => True) (decodeTrace T calls) w :=
    relyAlong_calls (decodeTrace T calls) w (decodeTrace_are_calls T calls)
  have hclaim := token_no_unauthorized_extraction (decodeTrace T calls) w a
    hw hR hA
  have hpre := token_claim_slot w.self σ a hs ha (token_map1_bound w a hwf ha)
  have hpost := token_claim_slot (run (decodeTrace T calls) w).self σ' a hs' ha
    (token_map1_bound { run (decodeTrace T calls) w with log := [] } a hwf' ha)
  rw [hpre, hpost]
  exact hclaim

theorem token_bytecode_no_unauthorized_extraction_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (a : Address) (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hlog : w.log = [])
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : EncodeBounded (mkTokenSetup hκ rt hrt is hcomp) tr)
    (ha : Nat.lt a wordBound) :
    ∃ σ', EvmTraceRun is
        (encodeCalls (mkTokenSetup hκ rt hrt is hcomp) tr) σ σ' ∧
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat := by
  let T := mkTokenSetup hκ rt hrt is hcomp
  obtain ⟨σ', hE, hs', hwf'⟩ :=
    transport_exists T (fun f hf => token_fn_callFree hf) (post_congr_callFree T (fun f hf => token_fn_callFree hf)) tr w σ hs hwf hb
  refine ⟨σ', hE, ?_⟩
  rw [decodeTrace_encodeCalls T tr hb] at hs' hwf'
  have hwlog : { w with log := [] } = w := by
    cases w; simp at hlog; subst hlog; rfl
  rw [hwlog] at hs' hwf'
  have hR : RelyAlong (fun _ _ => True) (callsOf tr) w :=
    relyAlong_calls (callsOf tr) w (callsOf_are_calls tr)
  have hclaim := token_no_unauthorized_extraction (callsOf tr) w a
    hw hR (token_noAuthAlong_callsOf a tr w hA)
  have hpre := token_claim_slot w.self σ a hs ha (token_map1_bound w a hwf ha)
  have hpost := token_claim_slot (run (callsOf tr) w).self σ' a hs' ha
    (token_map1_bound { run (callsOf tr) w with log := [] } a hwf' ha)
  rw [hpre, hpost]
  exact hclaim

theorem token_bytecode_solvent
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w) :
    ∀ σ', EvmTraceRunAll is calls σ σ' →
      Solvent claim holdings self
        (run (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w) ∧
      storageRel Token.contract Token.schema evmKeccak
        (run (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w).self σ' := by
  intro σ' hE
  let T := mkTokenSetup hκ rt hrt is hcomp
  have ⟨_, hs', _⟩ :=
    transport_trace T (fun f hf => token_fn_callFree hf) (post_congr_callFree T (fun f hf => token_fn_callFree hf)) self calls w σ σ'
      hs hlog hwf hWF hE
  have hR : RelyAlong (fun _ _ => True) (decodeTrace T calls) w :=
    relyAlong_calls (decodeTrace T calls) w (decodeTrace_are_calls T calls)
  exact ⟨inv_solvent self _ (token_solvent self (decodeTrace T calls) w
    (wf_decodeTrace T self calls hWF) hR hw), hs'⟩

theorem token_bytecode_solvent_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hlog : w.log = [])
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : EncodeBounded (mkTokenSetup hκ rt hrt is hcomp) tr) :
    ∃ σ', EvmTraceRun is (encodeCalls (mkTokenSetup hκ rt hrt is hcomp) tr) σ σ' ∧
      Solvent claim holdings self (run (callsOf tr) w) ∧
      storageRel Token.contract Token.schema evmKeccak
        (run (callsOf tr) w).self σ' := by
  let T := mkTokenSetup hκ rt hrt is hcomp
  obtain ⟨σ', hE, hs', _⟩ :=
    transport_exists T (fun f hf => token_fn_callFree hf) (post_congr_callFree T (fun f hf => token_fn_callFree hf)) tr w σ hs hwf hb
  have hwlog : { w with log := [] } = w := by
    cases w; simp at hlog; subst hlog; rfl
  refine ⟨σ', hE, ?_, ?_⟩
  · have hR : RelyAlong (fun _ _ => True) (callsOf tr) w :=
      relyAlong_calls (callsOf tr) w (callsOf_are_calls tr)
    exact inv_solvent self _ (token_solvent self (callsOf tr) w
      (wf_callsOf self tr hW) hR hw)
  · rw [decodeTrace_encodeCalls T tr hb, hwlog] at hs'
    exact hs'

theorem token_deploy_then_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (a : Address) (st : EvmState)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w)
    (hR : R Token.contract Token.schema evmKeccak w st)
    (hwf : WorldWF Token.contract Token.schema w)
    (ha : Nat.lt a wordBound) :
    ∀ σ', EvmDeployThenTrace is st.storage calls σ' →
      (st.storage (mapSlot1 evmKeccak 2 a)).toNat ≤
        (σ' (mapSlot1 evmKeccak 2 a)).toNat := by
  intro σ' hE
  exact token_bytecode_no_unauthorized_extraction rt hrt is hcomp hκ self calls w a
    st.storage hw hlog hWF hA hR.1 hwf ha σ' hE

end Proof

end Token
