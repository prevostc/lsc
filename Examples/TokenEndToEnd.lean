import Lsc.Compiler.TransportTheorems
import Examples.TokenCompileTheorems
import Examples.TokenSecurity
import Examples.TokenSecurityTheorems
import YulEvmCompiler.Compile

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Bytecode-level Token theorems via `Transport`. Main theorems are universal over
arbitrary halted calldata (`EvmTraceRunAll`); `_exists` encodes a Security trace.
Trace-predicted-calldata forms are dropped.
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

def decodeTokenFn (f : FnDef) : Option Fn :=
  if f.name = "transfer" then some .transfer
  else if f.name = "approve" then some .approve
  else if f.name = "transferFrom" then some .transferFrom
  else if f.name = "mint" then some .mint
  else if f.name = "burn" then some .burn
  else if f.name = "balanceOf" then some .balanceOf
  else if f.name = "allowance" then some .allowance
  else if f.name = "totalSupply" then some .totalSupply
  else none

theorem decodeTokenFn_fnDef (fn : Fn) : decodeTokenFn (tokenFnDef fn) = some fn := by
  cases fn <;> simp [decodeTokenFn, tokenFnDef]

theorem decodeTokenFn_of_mem (f : FnDef) (hf : f ∈ Token.contract.functions) :
    ∃ fn, decodeTokenFn f = some fn ∧ f = tokenFnDef fn := by
  simp [Token.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.transfer, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.approve, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.transferFrom, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.mint, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.burn, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.balanceOf, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.allowance, by simp [decodeTokenFn, tokenFnDef], rfl⟩
  · exact ⟨.totalSupply, by simp [decodeTokenFn, tokenFnDef], rfl⟩

def decodeToken : (fn : Fn) → List Nat → spec.Args fn
  | .transfer, dst :: n :: _ => (dst, n)
  | .transfer, _ => (0, 0)
  | .approve, sp :: n :: _ => (sp, n)
  | .approve, _ => (0, 0)
  | .transferFrom, src :: dst :: n :: _ => (src, dst, n)
  | .transferFrom, _ => (0, 0, 0)
  | .mint, dst :: n :: _ => (dst, n)
  | .mint, _ => (0, 0)
  | .burn, n :: _ => n
  | .burn, _ => 0
  | .balanceOf, who :: _ => who
  | .balanceOf, _ => 0
  | .allowance, o :: s :: _ => (o, s)
  | .allowance, _ => (0, 0)
  | .totalSupply, _ => ()

theorem encodeToken_decode (fn : Fn) (ns : List Nat)
    (h : ns.length = (tokenFnDef fn).params.length) :
    encodeToken fn (decodeToken fn ns) = ns := by
  cases fn <;> simp [tokenFnDef] at h
  · obtain ⟨dst, n, rfl⟩ := length_eq_two.mp h; rfl
  · obtain ⟨sp, n, rfl⟩ := length_eq_two.mp h; rfl
  · obtain ⟨src, dst, n, rfl⟩ := length_eq_three.mp h; rfl
  · obtain ⟨dst, n, rfl⟩ := length_eq_two.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨who, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨o, s, rfl⟩ := length_eq_two.mp h; rfl
  · subst h; rfl

theorem decodeToken_encode (fn : Fn) (args : spec.Args fn) :
    decodeToken fn (encodeToken fn args) = args := by
  cases fn <;> simp [decodeToken, encodeToken, asWord]

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

theorem token_post_congr (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w w' : World Storage Unit Event)
    (hs : w.self = w'.self) (_he : w.ext = w'.ext) :
    (worldAfter (Spec.exec spec fn args) ctx w).self =
      (worldAfter (Spec.exec spec fn args) ctx w').self ∧
    (worldAfter (Spec.exec spec fn args) ctx w).ext =
      (worldAfter (Spec.exec spec fn args) ctx w').ext := by
  refine ⟨token_worldAfter_self_of_self fn args ctx w w' hs, ?_⟩
  cases (worldAfter (Spec.exec spec fn args) ctx w).ext
  cases (worldAfter (Spec.exec spec fn args) ctx w').ext
  rfl

def tokenCodec : TransportCodec Token.contract Token.schema Token.spec where
  fnDef := tokenFnDef
  encode := encodeToken
  decodeFn := decodeTokenFn
  decode := decodeToken
  mem := tokenFnDef_mem
  encode_length := encodeToken_length
  decodeFn_fnDef := decodeTokenFn_fnDef
  decodeFn_of_mem := decodeTokenFn_of_mem
  encode_decode := encodeToken_decode
  decode_encode := decodeToken_encode
  core_exec := token_worldAfter_core_eq

def mkTokenSetup (hκ : KeccakSep Token.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is) :
    TransportSetup Storage Unit Event Error where
  c := Token.contract
  Γ := Token.schema
  spec := Token.spec
  codec := tokenCodec
  lawful := Token.schema_lawful
  hκ := hκ
  hctor := fun f hf => token_fn_not_ctor hf
  hlen := token_fields_lt
  hbound := fun f hf => token_fn_params_bound hf
  rt := rt
  hrt := hrt
  is := is
  hcomp := hcomp

theorem token_noAuthAlong_callsOf (a : Address) (tr : List (Step spec))
    (w : World Storage Unit Event) (h : NoAuthAlong Auth a tr w) :
    NoAuthAlong Auth a (callsOf tr) w := by
  induction tr generalizing w with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env x' =>
      have hw : { w with ext := x' } = w := by cases w.ext; cases x'; rfl
      simpa [callsOf, hw] using ih (w := { w with ext := x' }) (by simpa [NoAuthAlong] using h)
    | .call c =>
      rcases h with ⟨hAc, hAtl⟩
      exact ⟨hAc, ih (w := step (.call c) w) hAtl⟩

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
  simpa [claim, token_schema_balances] using
    storageRel_map1_toNat hs token_balances_fd rfl (by rw [token_schema_balances]) ha hb

theorem token_map1_bound (w : World Storage Unit Event) (a : Address)
    (hwf : WorldWF Token.contract Token.schema w) (ha : Nat.lt a wordBound) :
    w.self.balances a < wordBound := by
  have h := hwf 2 _ token_balances_fd a ha
  simpa [token_schema_balances] using h

end Token
