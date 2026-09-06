import Lsc.Compiler.EndToEnd
import Lsc.Compiler.Proof.Token
import Lsc.Examples.TokenSecurity
import YulEvmCompiler.Compile

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Bytecode-level Token theorems: Security traces transported onto compiled runtime
bytecode. `token_bytecode_*_exists` is the predicted run; the main theorems are
universal over halted matching executions (`EvmTraceRunAll`).
-/

open Lsc Lsc.Compiler Lsc.Security Token
open YulSemantics.EVM
open YulEvmCompiler (compile Instr)

namespace Token

def tokenFnDef : Fn → FnDef
  | .transfer =>
    { name := "transfer", decl := ``Token.transfer, kind := .tx,
      params := [{ name := "to", ty := .address }, { name := "amount", ty := .uint256 }],
      ret := .unit, core := Token.transfer.core }
  | .approve =>
    { name := "approve", decl := ``Token.approve, kind := .tx,
      params := [{ name := "spender", ty := .address }, { name := "amount", ty := .uint256 }],
      ret := .unit, core := Token.approve.core }
  | .transferFrom =>
    { name := "transferFrom", decl := ``Token.transferFrom, kind := .tx,
      params := [{ name := "src", ty := .address }, { name := "to", ty := .address },
        { name := "amount", ty := .uint256 }],
      ret := .unit, core := Token.transferFrom.core }
  | .mint =>
    { name := "mint", decl := ``Token.mint, kind := .tx,
      params := [{ name := "to", ty := .address }, { name := "amount", ty := .uint256 }],
      ret := .unit, core := Token.mint.core }
  | .burn =>
    { name := "burn", decl := ``Token.burn, kind := .tx,
      params := [{ name := "amount", ty := .uint256 }],
      ret := .unit, core := Token.burn.core }
  | .balanceOf =>
    { name := "balanceOf", decl := ``Token.balanceOf, kind := .view,
      params := [{ name := "who", ty := .address }],
      ret := .word, core := Token.balanceOf.core }
  | .allowance =>
    { name := "allowance", decl := ``Token.allowance, kind := .view,
      params := [{ name := "owner", ty := .address }, { name := "spender", ty := .address }],
      ret := .word, core := Token.allowance.core }
  | .totalSupply =>
    { name := "totalSupply", decl := ``Token.totalSupply, kind := .view,
      params := [], ret := .word, core := Token.totalSupply.core }

theorem tokenFnDef_mem (fn : Fn) : tokenFnDef fn ∈ Token.contract.functions := by
  cases fn <;> simp [tokenFnDef, Token.contract]

/-- `Address` is `Nat` but does not reduce in `List Nat` under `rw`. -/
@[reducible] def asWord (a : Address) : Nat := a

def encodeToken : (fn : Fn) → spec.Args fn → List Nat
  | .transfer, (dst, n) => [asWord dst, n]
  | .approve, (sp, n) => [asWord sp, n]
  | .transferFrom, (src, dst, n) => [asWord src, asWord dst, n]
  | .mint, (dst, n) => [asWord dst, n]
  | .burn, n => [n]
  | .balanceOf, who => [asWord who]
  | .allowance, (o, s) => [asWord o, asWord s]
  | .totalSupply, _ => []

theorem encodeToken_length (fn : Fn) (args : spec.Args fn) :
    (encodeToken fn args).length = (tokenFnDef fn).params.length := by
  cases fn <;> simp [encodeToken, tokenFnDef]

/-- `worldAfter` hides the return type, so Core and Spec programs can be compared. -/
theorem token_worldAfter_core_eq (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Unit Event) :
    worldAfter (Core.denote Token.schema (tokenFnDef fn).core
      (encodeToken fn args).reverse) ctx w =
    worldAfter (Spec.exec spec fn args) ctx w := by
  cases fn with
  | transfer =>
    rcases args with ⟨dst, n⟩
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.transfer.core [n, dst]) ctx w =
      worldAfter (Spec.exec spec .transfer (dst, n)) ctx w
    rw [Token.transfer.core_denote, Token.spec_exec_transfer]
    rfl
  | approve =>
    rcases args with ⟨sp, n⟩
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.approve.core [n, sp]) ctx w =
      worldAfter (Spec.exec spec .approve (sp, n)) ctx w
    rw [Token.approve.core_denote, Token.spec_exec_approve]
    rfl
  | transferFrom =>
    rcases args with ⟨src, dst, n⟩
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.transferFrom.core [n, dst, src]) ctx w =
      worldAfter (Spec.exec spec .transferFrom (src, dst, n)) ctx w
    rw [Token.transferFrom.core_denote, Token.spec_exec_transferFrom]
    rfl
  | mint =>
    rcases args with ⟨dst, n⟩
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.mint.core [n, dst]) ctx w =
      worldAfter (Spec.exec spec .mint (dst, n)) ctx w
    rw [Token.mint.core_denote, Token.spec_exec_mint]
    rfl
  | burn =>
    dsimp [tokenFnDef, encodeToken]
    change worldAfter (Core.denote Token.schema Token.burn.core [args]) ctx w =
      worldAfter (Spec.exec spec .burn args) ctx w
    rw [Token.burn.core_denote, Token.spec_exec_burn]
    rfl
  | balanceOf =>
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.balanceOf.core [args]) ctx w =
      worldAfter (Spec.exec spec .balanceOf args) ctx w
    rw [Token.balanceOf.core_denote, Token.spec_exec_balanceOf]
    rfl
  | allowance =>
    rcases args with ⟨o, s⟩
    dsimp [tokenFnDef, encodeToken, asWord]
    change worldAfter (Core.denote Token.schema Token.allowance.core [s, o]) ctx w =
      worldAfter (Spec.exec spec .allowance (o, s)) ctx w
    rw [Token.allowance.core_denote, Token.spec_exec_allowance]
    rfl
  | totalSupply =>
    cases args
    dsimp [tokenFnDef, encodeToken]
    rfl

def tokenCalls : List (Step spec) → List (Ctx × FnDef × List Nat)
  | [] => []
  | .call c :: tr => (c.toCtx, tokenFnDef c.fn, encodeToken c.fn c.args) :: tokenCalls tr
  | .env _ :: tr => tokenCalls tr

/-- Per-call well-formedness the dispatcher/`fnCalldata` lemmas need. -/
def CallsBounded : List (Step spec) → Prop
  | [] => True
  | .call c :: tr =>
    CtxWF c.toCtx ∧ (∀ n ∈ encodeToken c.fn c.args, n < wordBound) ∧ CallsBounded tr
  | .env _ :: tr => CallsBounded tr

theorem token_fnCalldata_bound (fn : Fn) (args : spec.Args fn) :
    (fnCalldata (tokenFnDef fn) (encodeToken fn args)).length < wordBound := by
  rw [length_fnCalldata, encodeToken_length]
  exact token_fn_params_bound (tokenFnDef_mem fn)

theorem tokenCalls_spec (tr : List (Step spec)) (hb : CallsBounded tr) :
    ∀ p ∈ tokenCalls tr,
      p.2.1 ∈ Token.contract.functions ∧ p.2.1.kind ≠ .constructor ∧
      p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
      CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound := by
  induction tr with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
    match s with
    | .env _ =>
      intro p hp
      exact ih (by simpa [CallsBounded] using hb) p hp
    | .call c =>
      intro p hp
      rcases hb with ⟨hctx, hW, htl⟩
      simp [tokenCalls] at hp
      rcases hp with rfl | hp
      · exact ⟨tokenFnDef_mem c.fn, token_fn_not_ctor (tokenFnDef_mem c.fn),
          encodeToken_length c.fn c.args, hW, hctx, token_fnCalldata_bound c.fn c.args⟩
      · exact ih htl p hp

/-- `worldAfter.self` of a Token entrypoint depends only on `ctx` and `w.self`. -/
theorem token_worldAfter_self_of_self (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w w' : World Storage Unit Event) (hs : w.self = w'.self) :
    (worldAfter (Spec.exec spec fn args) ctx w).self =
    (worldAfter (Spec.exec spec fn args) ctx w').self := by
  cases fn with
  | transfer =>
    rcases args with ⟨dst, amount⟩
    simp only [worldAfter, Token.spec_exec_transfer]
    by_cases hsub : amount ≤ w.self.balances ctx.sender
    · by_cases hadd : debit w.self.balances ctx.sender amount dst + amount < wordBound
      · have hrun := transfer_ok ctx w dst amount hsub hadd
        have hrun' := transfer_ok ctx w' dst amount (hs ▸ hsub) (by simpa [hs] using hadd)
        simp [hrun, hrun', hs]
      · have hrun := transfer_reverts_on_overflow ctx w dst amount hsub (Nat.not_lt.mp hadd)
        have hrun' := transfer_reverts_on_overflow ctx w' dst amount (hs ▸ hsub)
          (by simpa [hs] using Nat.not_lt.mp hadd)
        simpa [worldAfter, hrun, hrun'] using hs
    · have hrun := transfer_reverts_on_insufficient_balance ctx w dst amount (Nat.not_le.mp hsub)
      have hrun' := transfer_reverts_on_insufficient_balance ctx w' dst amount
        (by simpa [hs] using Nat.not_le.mp hsub)
      simpa [worldAfter, hrun, hrun'] using hs
  | approve =>
    rcases args with ⟨sp, amount⟩
    simp only [worldAfter, Token.spec_exec_approve]
    have hrun := approve_ok ctx w sp amount
    have hrun' := approve_ok ctx w' sp amount
    simp [hrun, hrun', hs]
  | transferFrom =>
    rcases args with ⟨src, dst, amount⟩
    simp only [worldAfter, Token.spec_exec_transferFrom]
    by_cases hallow : amount ≤ w.self.allowances src ctx.sender
    · by_cases hsub : amount ≤ w.self.balances src
      · by_cases hadd : debit w.self.balances src amount dst + amount < wordBound
        · have hrun := transferFrom_ok ctx w src dst amount hallow hsub hadd
          have hrun' := transferFrom_ok ctx w' src dst amount (hs ▸ hallow) (hs ▸ hsub)
            (by simpa [hs] using hadd)
          simp [hrun, hrun', hs]
        · have hrun := transferFrom_reverts_on_overflow ctx w src dst amount hallow hsub
            (Nat.not_lt.mp hadd)
          have hrun' := transferFrom_reverts_on_overflow ctx w' src dst amount
            (hs ▸ hallow) (hs ▸ hsub) (by simpa [hs] using Nat.not_lt.mp hadd)
          simpa [worldAfter, hrun, hrun'] using hs
      · have hrun := transferFrom_reverts_on_insufficient_balance ctx w src dst amount hallow
          (Nat.not_le.mp hsub)
        have hrun' := transferFrom_reverts_on_insufficient_balance ctx w' src dst amount
          (hs ▸ hallow) (by simpa [hs] using Nat.not_le.mp hsub)
        simpa [worldAfter, hrun, hrun'] using hs
    · have hrun := transferFrom_reverts_on_insufficient_allowance ctx w src dst amount
        (Nat.not_le.mp hallow)
      have hrun' := transferFrom_reverts_on_insufficient_allowance ctx w' src dst amount
        (by simpa [hs] using Nat.not_le.mp hallow)
      simpa [worldAfter, hrun, hrun'] using hs
  | mint =>
    rcases args with ⟨dst, amount⟩
    simp only [worldAfter, Token.spec_exec_mint]
    by_cases howner : ctx.sender = w.self.owner
    · by_cases hsupply : w.self.totalSupply + amount < wordBound
      · by_cases hadd : w.self.balances dst + amount < wordBound
        · have hrun := mint_ok ctx w dst amount howner hsupply hadd
          have hrun' := mint_ok ctx w' dst amount (hs ▸ howner) (by simpa [hs] using hsupply)
            (by simpa [hs] using hadd)
          simp [hrun, hrun', hs]
        · have hrun := mint_reverts_on_balance_overflow ctx w dst amount howner hsupply
            (Nat.not_lt.mp hadd)
          have hrun' := mint_reverts_on_balance_overflow ctx w' dst amount (hs ▸ howner)
            (by simpa [hs] using hsupply) (by simpa [hs] using Nat.not_lt.mp hadd)
          simpa [worldAfter, hrun, hrun'] using hs
      · have hrun := mint_reverts_on_overflow ctx w dst amount howner (Nat.not_lt.mp hsupply)
        have hrun' := mint_reverts_on_overflow ctx w' dst amount (hs ▸ howner)
          (by simpa [hs] using Nat.not_lt.mp hsupply)
        simpa [worldAfter, hrun, hrun'] using hs
    · have hrun := mint_reverts_for_non_owner ctx w dst amount howner
      have hrun' := mint_reverts_for_non_owner ctx w' dst amount (hs ▸ howner)
      simpa [worldAfter, hrun, hrun'] using hs
  | burn =>
    simp only [worldAfter, Token.spec_exec_burn]
    by_cases hsub : args ≤ w.self.balances ctx.sender
    · by_cases hsupply : args ≤ w.self.totalSupply
      · have hrun := burn_ok ctx w args hsub hsupply
        have hrun' := burn_ok ctx w' args (hs ▸ hsub) (hs ▸ hsupply)
        simp [hrun, hrun', hs]
      · have hrun := burn_reverts_on_insufficient_supply ctx w args hsub (Nat.not_le.mp hsupply)
        have hrun' := burn_reverts_on_insufficient_supply ctx w' args (hs ▸ hsub)
          (by simpa [hs] using Nat.not_le.mp hsupply)
        simpa [worldAfter, hrun, hrun'] using hs
    · have hrun := burn_reverts_on_insufficient_balance ctx w args (Nat.not_le.mp hsub)
      have hrun' := burn_reverts_on_insufficient_balance ctx w' args
        (by simpa [hs] using Nat.not_le.mp hsub)
      simpa [worldAfter, hrun, hrun'] using hs
  | balanceOf =>
    rw [worldAfter, worldAfter, Token.spec_exec_balanceOf,
      balanceOf_returns_stored_balance ctx w, balanceOf_returns_stored_balance ctx w']
    exact hs
  | allowance =>
    rcases args with ⟨o, s⟩
    rw [worldAfter, worldAfter, Token.spec_exec_allowance,
      allowance_returns_stored ctx w o s, allowance_returns_stored ctx w' o s]
    exact hs
  | totalSupply =>
    rw [worldAfter, worldAfter, Token.spec_exec_totalSupply,
      totalSupply_returns_stored ctx w, totalSupply_returns_stored ctx w']
    exact hs

theorem token_step_self_of_self (s : Step spec) (w w' : World Storage Unit Event)
    (h : w.self = w'.self) : (step s w).self = (step s w').self := by
  cases s with
  | env _ => simpa [step] using h
  | call c =>
    simpa [step] using token_worldAfter_self_of_self c.fn c.args c.toCtx w w' h

theorem token_run_self_of_self (tr : List (Step spec)) (w w' : World Storage Unit Event)
    (h : w.self = w'.self) : (run tr w).self = (run tr w').self := by
  induction tr generalizing w w' with
  | nil => simpa [run] using h
  | cons s rest ih =>
    rw [run_cons, run_cons]
    exact ih (step s w) (step s w') (token_step_self_of_self s w w' h)

theorem token_run_self_eq_coreRun (tr : List (Step spec)) (w : World Storage Unit Event) :
    (run tr w).self = (coreRun Token.schema (tokenCalls tr) { w with log := [] }).self := by
  induction tr generalizing w with
  | nil => simp [tokenCalls, coreRun]
  | cons s rest ih =>
    match s with
    | .env x' =>
      rw [run_cons, show step (.env x') w = { w with ext := x' } from rfl]
      simp only [tokenCalls]
      have hself : ({ w with ext := x' } : World Storage Unit Event).self = w.self := rfl
      rw [token_run_self_of_self rest { w with ext := x' } w hself]
      exact ih w
    | .call c =>
      rw [run_cons, show step (.call c) w =
        worldAfter (Spec.exec spec c.fn c.args) c.toCtx w from rfl]
      simp only [tokenCalls, coreRun]
      rw [token_worldAfter_core_eq]
      let wSec := worldAfter (Spec.exec spec c.fn c.args) c.toCtx w
      let wCore : World Storage Unit Event :=
        { worldAfter (Spec.exec spec c.fn c.args) c.toCtx { w with log := [] } with log := [] }
      have hs : wSec.self = wCore.self := by
        simpa [wSec, wCore] using
          token_worldAfter_self_of_self c.fn c.args c.toCtx w { w with log := [] } rfl
      rw [token_run_self_of_self rest wSec wCore hs]
      have ih' := ih wCore
      simpa [wCore] using ih'

theorem token_balances_fd :
    Token.contract.fields[2]? =
      some { name := "balances", kind := .map1, ty := .uint256 } := by
  simp [Token.contract]

theorem token_schema_balances (s : Storage) (k : Address) :
    Token.schema.st.map1 2 s k = s.balances k := rfl

theorem token_claim_slot (s : Storage) (σ : U256 → U256) (a : Address)
    (hs : storageRel Token.contract Token.schema evmKeccak s σ)
    (ha : Nat.lt a wordBound) (hb : s.balances a < wordBound) :
    (σ (mapSlot1 evmKeccak 2 a)).toNat = claim a s := by
  have h := hs 2 _ token_balances_fd a ha
  rw [token_schema_balances] at h
  simpa [claim, Lsc.Compiler.toNat_ofNat_of_lt hb] using congrArg BitVec.toNat h

theorem token_map1_bound (w : World Storage Unit Event) (a : Address)
    (hwf : WorldWF Token.contract Token.schema w) (ha : Nat.lt a wordBound) :
    w.self.balances a < wordBound := by
  have h := hwf 2 _ token_balances_fd a ha
  simpa [token_schema_balances] using h

theorem token_transport
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (tr : List (Step spec)) (w : World Storage Unit Event) (σ : U256 → U256)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr) :
    ∃ σ', EvmTraceRun is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' ∧
      storageRel Token.contract Token.schema evmKeccak (run tr w).self σ' ∧
      WorldWF Token.contract Token.schema (run tr w) := by
  have hnd : selectorsNodup Token.contract = true := (runtimeBlock_inv hrt).1
  obtain ⟨σ', hE, hs', hwf'⟩ :=
    bytecode_trace_transport Token.contract Token.schema Token.schema_lawful hκ
      (fun f hf => token_fn_callFree hf) (fun f hf => token_fn_not_ctor hf)
      token_fields_lt (fun f hf => token_fn_params_bound hf) hnd rt hrt is hcomp
      (tokenCalls tr) { w with log := [] } σ (by simpa using hs) rfl (WorldWF_log [] hwf)
      (tokenCalls_spec tr hb)
  have hself :
      (coreRun Token.schema (tokenCalls tr) { w with log := [] }).self = (run tr w).self :=
    (token_run_self_eq_coreRun tr w).symm
  refine ⟨σ', hE, ?_, ?_⟩
  · simpa [hself] using hs'
  · exact WorldWF_of_self hself hwf'

/-- Compiled Token runtime: a well-formed, no-auth-for-`a` Security trace, executed as
EVM calls predicted by that trace, does not decrease `a`'s balance as read through `R`.
Non-vacuity: `token_bytecode_no_unauthorized_extraction_exists`. -/
theorem token_bytecode_no_unauthorized_extraction_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr) (ha : Nat.lt a wordBound) :
    ∃ σ', EvmTraceRun is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' ∧
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat := by
  obtain ⟨σ', hE, hs', hwf'⟩ := token_transport rt hrt is hcomp hκ tr w σ hs hwf hb
  refine ⟨σ', hE, ?_⟩
  have hclaim := token_no_unauthorized_extraction self tr w a hw hW hR hA
  have hpre := token_claim_slot w.self σ a hs ha (token_map1_bound w a hwf ha)
  have hpost := token_claim_slot (run tr w).self σ' a hs' ha
    (token_map1_bound (run tr w) a hwf' ha)
  simpa [hpre, hpost] using hclaim

theorem token_all_rel
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (tr : List (Step spec)) (w : World Storage Unit Event) (σ σ' : U256 → U256)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr)
    (hE : EvmTraceRunAll is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ') :
    storageRel Token.contract Token.schema evmKeccak (run tr w).self σ' ∧
    WorldWF Token.contract Token.schema (run tr w) := by
  have hnd : selectorsNodup Token.contract = true := (runtimeBlock_inv hrt).1
  obtain ⟨hs', hwf'⟩ :=
    bytecode_trace_all Token.contract Token.schema Token.schema_lawful hκ
      (fun f hf => token_fn_callFree hf) (fun f hf => token_fn_not_ctor hf)
      token_fields_lt (fun f hf => token_fn_params_bound hf) hnd rt hrt is hcomp
      (tokenCalls tr) { w with log := [] } σ σ' (by simpa using hs) rfl (WorldWF_log [] hwf)
      (tokenCalls_spec tr hb) hE
  have hself :
      (coreRun Token.schema (tokenCalls tr) { w with log := [] }).self = (run tr w).self :=
    (token_run_self_eq_coreRun tr w).symm
  refine ⟨?_, ?_⟩
  · simpa [hself] using hs'
  · exact WorldWF_of_self hself hwf'

/-- Compiled Token runtime: every halted matching execution of a well-formed,
no-auth-for-`a` Security trace does not decrease `a`'s balance as read through `R`. -/
theorem token_bytecode_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr) (ha : Nat.lt a wordBound) :
    ∀ σ', EvmTraceRunAll is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' →
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat := by
  intro σ' hE
  obtain ⟨hs', hwf'⟩ := token_all_rel rt hrt is hcomp hκ tr w σ σ' hs hwf hb hE
  have hclaim := token_no_unauthorized_extraction self tr w a hw hW hR hA
  have hpre := token_claim_slot w.self σ a hs ha (token_map1_bound w a hwf ha)
  have hpost := token_claim_slot (run tr w).self σ' a hs' ha
    (token_map1_bound (run tr w) a hwf' ha)
  simpa [hpre, hpost] using hclaim

/-- Non-vacuity: some predicted `EvmTraceRun` stays solvent. -/
theorem token_bytecode_solvent_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr) :
    ∃ σ', EvmTraceRun is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' ∧
      Solvent claim holdings self (run tr w) ∧
      storageRel Token.contract Token.schema evmKeccak (run tr w).self σ' := by
  obtain ⟨σ', hE, hs', _⟩ := token_transport rt hrt is hcomp hκ tr w σ hs hwf hb
  exact ⟨σ', hE, token_solvent self tr w hW hR hw, hs'⟩

/-- Compiled Token runtime: every halted matching execution of a well-formed
Security trace stays solvent in EVM storage. -/
theorem token_bytecode_solvent
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : CallsBounded tr) :
    ∀ σ', EvmTraceRunAll is
        ((tokenCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' →
      Solvent claim holdings self (run tr w) ∧
      storageRel Token.contract Token.schema evmKeccak (run tr w).self σ' := by
  intro σ' hE
  obtain ⟨hs', _⟩ := token_all_rel rt hrt is hcomp hκ tr w σ σ' hs hwf hb hE
  exact ⟨token_solvent self tr w hW hR hw, hs'⟩

end Token
