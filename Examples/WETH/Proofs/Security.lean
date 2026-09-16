import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
import Examples.WETH.Spec
import Examples.WETH.Proofs.Tx

set_option linter.unusedSimpArgs false

open Lsc Lsc.Security WETH

attribute [local simp] Claim.ofSelf AuthPred.ofSelf

namespace WETH

/-!
WETH anti-extraction and backing. Wrapped `claim` is storage-only.
`withdraw` burns then `Native.send`s the same amount to the caller.
`deposit` credits incoming value then mints it. `Inv` (finite support,
`totalSupply ≤ nativeBalance`, honest send) is a proof device: public
theorems take `State`. The dispatcher wrap-guard makes backing
preservable; `HasRely` keeps native balance from falling between calls.
-/

lemma Auth_transfer (a : Address) (ctx : Ctx) (dst : Address)
    (n : Amount native) (w : World) :
    Auth a (Call.ofCtx ctx .transfer (dst, n)) w ↔ ctx.sender = a :=
  Iff.rfl

lemma Auth_withdraw (a : Address) (ctx : Ctx) (n : Amount native)
    (w : World) :
    Auth a (Call.ofCtx ctx .withdraw n) w ↔
      ctx.sender = a ∧ n ≤ w.self.balances a :=
  Iff.rfl

lemma Auth_transferFrom (a : Address) (ctx : Ctx) (src dst : Address)
    (n : Amount native) (w : World) :
    Auth a (Call.ofCtx ctx .transferFrom (src, dst, n)) w ↔
      src = a ∧ n ≤ w.self.allowances src ctx.sender :=
  Iff.rfl

/-- Finite support of balances. -/
def InvStorage (s : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → s.balances a = 0) ∧
    H.sum (fun a => (s.balances a).raw) = s.totalSupply.raw

/-- Balances have finite support summing to `totalSupply`, wrapped supply
is covered by `self`'s native balance, and `oracle.send` debits that
balance by the sent amount. -/
def Inv (w : World) : Prop :=
  InvStorage w.self ∧
    w.self.totalSupply.raw ≤ World.nativeBalance w ∧
    DebitsOnSend w.oracle

/-- Wrapped supply is covered by native ETH held by `self`. -/
def Backed (w : World) : Prop :=
  w.self.totalSupply.raw ≤ World.nativeBalance w

/-! ### Sum helpers for `Inv` -/

private abbrev rawBals (bals : Address → Amount native) : Address → Nat :=
  fun a => (bals a).raw

private theorem rawBals_update (bals : Address → Amount native) (src : Address)
    (n : Amount native) :
    rawBals (Function.update bals src n) =
      Function.update (rawBals bals) src n.raw := by
  funext a
  by_cases h : a = src <;> simp [rawBals, Function.update, h]

private theorem nat_sum_update_sub (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) {n : Nat} (hn : n ≤ f i) :
    H.sum (Function.update f i (f i - n)) + n = H.sum f := by
  have hS := sum_update_mem H f hi (f i - n)
  have : f i - n + n = f i := Nat.sub_add_cancel hn
  omega

private theorem nat_sum_update_add (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i (f i + n)) = H.sum f + n := by
  have hS := sum_update_mem H f hi (f i + n)
  omega

private theorem sum_debit (H : Finset Address) (bals : Address → Amount native)
    {src : Address} (hs : src ∈ H) {n : Amount native}
    (hn : n.raw ≤ (bals src).raw) :
    H.sum (rawBals (debit bals src n)) + n.raw = H.sum (rawBals bals) := by
  unfold debit
  rw [rawBals_update, Amount.raw_sub]
  exact nat_sum_update_sub H (rawBals bals) hs hn

private theorem inv_of_transferPost (σ : Storage) (src dst : Address)
    (n : Amount native)
    (hInv : InvStorage σ) (hn : n ≤ σ.balances src) :
    InvStorage (transferPost σ src dst n) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hn' : n.raw ≤ (σ.balances src).raw := hn
  by_cases hsrc : src ∈ H
  · by_cases hto : dst ∈ H
    · refine ⟨H, ?_, ?_⟩
      · intro a ha
        have ha_to : a ≠ dst := by intro h; subst h; exact ha hto
        have ha_src : a ≠ src := by intro h; subst h; exact ha hsrc
        simp [transferPost, credit_other _ ha_to, debit_other _ ha_src]
        exact h0 a ha
      · have hs1 := sum_debit H σ.balances hsrc hn'
        let f := rawBals (debit σ.balances src n)
        have hsum' :
            H.sum (rawBals (Function.update (debit σ.balances src n) dst
              (debit σ.balances src n dst + n))) =
              H.sum f + n.raw := by
          rw [rawBals_update, Amount.raw_add]
          exact nat_sum_update_add H f hto n.raw
        change H.sum (rawBals (transferPost σ src dst n).balances) =
          (transferPost σ src dst n).totalSupply.raw
        simp only [transferPost, credit]
        exact (hsum'.trans hs1).trans hsum
    · have hne : src ≠ dst := by intro h; subst h; exact hto hsrc
      refine ⟨insert dst H, ?_, ?_⟩
      · intro a ha
        have hat : a ≠ dst := by
          intro h; subst h; exact ha (Finset.mem_insert_self _ _)
        have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
        have ha_src : a ≠ src := by intro h; subst h; exact haH hsrc
        simp [transferPost, credit_other _ hat, debit_other _ ha_src]
        exact h0 a haH
      · have hs1 := sum_debit H σ.balances hsrc hn'
        let f := rawBals (debit σ.balances src n)
        have hframe := sum_update_not_mem H f hto (f dst + n.raw)
        have hb0 : σ.balances dst = 0 := h0 dst hto
        have hdt : debit σ.balances src n dst = 0 := by
          simp [debit, Function.update_of_ne hne.symm, hb0]
        have hsum' :
            (∑ a ∈ insert dst H, rawBals (transferPost σ src dst n).balances a) =
              H.sum (rawBals σ.balances) := by
          rw [Finset.sum_insert hto]
          simp only [transferPost, credit]
          rw [rawBals_update, Amount.raw_add, Function.update_self, hframe]
          simp [hdt, Amount.raw_zero]
          rw [Nat.add_comm]
          exact hs1
        change (∑ a ∈ insert dst H,
            ((transferPost σ src dst n).balances a).raw) =
          (transferPost σ src dst n).totalSupply.raw
        simpa [transferPost] using hsum'.trans hsum
  · have hb0 : σ.balances src = 0 := h0 src hsrc
    have hn0 : n = 0 := by
      cases n with | mk nraw =>
      have hz : (σ.balances src).raw = 0 := by
        simpa [Amount.raw_zero] using congrArg Amount.raw hb0
      have : nraw = 0 := Nat.eq_zero_of_le_zero (hn'.trans_eq hz)
      subst this
      rfl
    subst hn0
    have hbals : (transferPost σ src dst 0).balances = σ.balances := by
      have hsub0 : σ.balances src - 0 = σ.balances src :=
        Amount.ext (by simp [Amount.raw_sub, Amount.raw_zero])
      have hadd0 (x : Amount native) : x + 0 = x :=
        Amount.ext (by simp [Amount.raw_add, Amount.raw_zero])
      funext a
      simp [transferPost, credit, debit, hsub0, hadd0, Function.update_eq_self]
    refine ⟨H, fun a ha => ?_, ?_⟩
    · rw [show (transferPost σ src dst 0).balances a = σ.balances a from
        congrFun hbals a]
      exact h0 a ha
    · have hsum' :
          (∑ a ∈ H, ((transferPost σ src dst 0).balances a).raw) =
            H.sum (fun a => (σ.balances a).raw) := by
        apply Finset.sum_congr rfl
        intro a _; rw [hbals]
      simpa [transferPost] using hsum'.trans hsum

private theorem inv_of_depositPost (σ : Storage) (dst : Address) (n : Amount native)
    (hInv : InvStorage σ) :
    InvStorage (depositPost σ dst n) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  refine ⟨insert dst H, ?_, ?_⟩
  · intro a ha
    have hat : a ≠ dst := by
      intro h; subst h; exact ha (Finset.mem_insert_self _ _)
    have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
    simp [depositPost, credit_other _ hat]
    exact h0 a haH
  · by_cases ht : dst ∈ H
    · rw [Finset.insert_eq_of_mem ht]
      let f := rawBals σ.balances
      have hcancel :
          H.sum (rawBals (Function.update σ.balances dst (σ.balances dst + n))) =
            H.sum f + n.raw := by
        rw [rawBals_update, Amount.raw_add]
        exact nat_sum_update_add H f ht n.raw
      change H.sum (fun a => ((depositPost σ dst n).balances a).raw) =
        (depositPost σ dst n).totalSupply.raw
      simp only [depositPost, credit]
      simpa [rawBals] using hcancel.trans (by rw [hsum])
    · let f := rawBals σ.balances
      have hframe := sum_update_not_mem H f ht (f dst + n.raw)
      have hb0 : σ.balances dst = 0 := h0 dst ht
      have hsum' :
          (∑ a ∈ insert dst H, ((depositPost σ dst n).balances a).raw) =
            H.sum f + n.raw := by
        rw [Finset.sum_insert ht]
        simp only [depositPost, credit, Function.update_self]
        change (σ.balances dst + n).raw +
            H.sum (rawBals (Function.update σ.balances dst (σ.balances dst + n))) =
          H.sum f + n.raw
        rw [rawBals_update, Amount.raw_add, hb0, Amount.raw_zero, Nat.zero_add]
        have hf0 : f dst = 0 := by
          simpa [rawBals, Amount.raw_zero] using congrArg Amount.raw hb0
        have hfr : H.sum (Function.update f dst n.raw) = H.sum f := by
          simpa [hf0, Nat.zero_add] using hframe
        rw [hfr, Nat.add_comm]
      change (∑ a ∈ insert dst H, ((depositPost σ dst n).balances a).raw) =
        (depositPost σ dst n).totalSupply.raw
      simpa [depositPost] using hsum'.trans (by rw [hsum])

private theorem inv_of_withdrawPost (σ : Storage) (src : Address) (n : Amount native)
    (hInv : InvStorage σ) (hn : n ≤ σ.balances src) :
    InvStorage (withdrawPost σ src n) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hn' : n.raw ≤ (σ.balances src).raw := hn
  by_cases hs : src ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ src := by intro h; subst h; exact ha hs
      simp [withdrawPost, debit_other _ ha_src]
      exact h0 a ha
    · have hs1 := sum_debit H σ.balances hs hn'
      have hsumd :
          H.sum (rawBals (debit σ.balances src n)) =
            H.sum (rawBals σ.balances) - n.raw := by
        rw [← Nat.add_sub_cancel (H.sum (rawBals (debit σ.balances src n))) n.raw, hs1]
      change H.sum (fun a => ((withdrawPost σ src n).balances a).raw) =
        (withdrawPost σ src n).totalSupply.raw
      simp only [withdrawPost, debit, Amount.raw_sub]
      simpa [rawBals] using hsumd.trans (by rw [hsum])
  · have hb0 : σ.balances src = 0 := h0 src hs
    have hn0 : n = 0 := by
      cases n with | mk nraw =>
      have hz : (σ.balances src).raw = 0 := by
        simpa [Amount.raw_zero] using congrArg Amount.raw hb0
      have : nraw = 0 := Nat.eq_zero_of_le_zero (hn'.trans_eq hz)
      subst this
      rfl
    subst hn0
    have hbals0 : σ.balances src - 0 = σ.balances src :=
      Amount.ext (by simp [Amount.raw_sub])
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp [withdrawPost, debit, hbals0, Function.update_eq_self]
      exact h0 a ha
    · simpa [withdrawPost, debit, hbals0, Function.update_eq_self, Amount.raw_zero,
        Amount.raw_sub, Nat.sub_zero] using hsum

/-- Finite support and honest `Native.send`. Extraction uses this; backing
is proved from the dispatcher wrap-guard plus `HasRely`. -/
private abbrev InvTrace (w : World) : Prop :=
  InvStorage w.self ∧ DebitsOnSend w.oracle

private theorem Inv_to_trace {w : World} (h : Inv w) :
    InvTrace w :=
  ⟨h.1, h.2.2⟩

/-! ### (a) No unauthorized decrease -/

theorem transfer_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .transfer :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨dst, amount⟩ ctx w a ret w' _hInv hrun hdec => by
    have hr : ret = true := transfer_returns_true ctx w dst amount hrun
    rw [hr] at hrun
    rw [Auth_transfer]
    by_cases hs : ctx.sender = a
    · exact hs
    · obtain ⟨_, hw'⟩ := transfer_ok_inv ctx w dst amount hrun
      simp [claim] at hdec
      rw [hw'] at hdec
      simp [transferPost] at hdec
      by_cases ht : a = dst
      · subst ht
        simp [credit, debit, Function.update_of_ne (Ne.symm hs)] at hdec
        exact (Nat.not_lt.mpr (Nat.le_add_right _ _) hdec).elim
      · simp [credit_other _ ht, debit_other _ (Ne.symm hs)] at hdec

theorem transferFrom_auth :
    NoUnauthorizedDecreaseFn spec InvTrace claim Auth .transferFrom :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨src, dst, amount⟩ ctx w a ret w' _hInv hrun
      hdec => by
    have hr : ret = true := transferFrom_returns_true ctx w src dst amount hrun
    rw [hr] at hrun
    rw [Auth_transferFrom]
    by_cases ha : src = a
    · obtain ⟨hallow, _, _⟩ := transferFrom_ok_inv ctx w src dst amount hrun
      exact ⟨ha, hallow⟩
    · obtain ⟨_, _, hw'⟩ := transferFrom_ok_inv ctx w src dst amount hrun
      simp [claim] at hdec
      rw [hw'] at hdec
      simp [transferFromPost] at hdec
      by_cases ht : a = dst
      · subst ht
        simp [credit, debit, Function.update_of_ne (Ne.symm ha)] at hdec
        exact (Nat.not_lt.mpr (Nat.le_add_right _ _) hdec).elim
      · simp [credit_other _ ht, debit_other _ (Ne.symm ha)] at hdec

private theorem withdraw_outflow (amount : Amount native)
    {ctx : Ctx} {w w' : World}
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w')) :
    NativeOutflow claim ctx.sender amount.raw w w' where
  drop := by
    obtain ⟨hbal, _, ⟨_, _, hw'⟩⟩ := withdraw_ok_inv ctx w amount h
    subst hw'
    simp [claim, withdrawPost, debit, Amount.raw_sub]
    exact Nat.sub_add_cancel hbal
  frame := by
    intro a hne
    have hb := withdraw_others ctx w amount h a hne
    simp [claim, hb]

/-- Success burns `v` from the caller then `Native.send`s the caller `v`
(`NativeOutflow`). Tight `Auth` also requires `amount ≤ balances`, which
holds on this success path. -/
theorem withdraw_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .withdraw :=
  NoUnauthorizedDecreaseFn_of_native_send_ok
    (fun amount ctx w _ret w' hrun => by
      obtain ⟨hbal, _, _⟩ := withdraw_ok_inv ctx w amount hrun
      exact ⟨rfl, hbal⟩)
    (fun amount ctx w _ret w' _hInv hrun =>
      Or.inr ⟨amount.raw, withdraw_outflow amount hrun⟩)

theorem deposit_auth : NoUnauthorizedDecreaseCreditFn spec InvTrace claim Auth .deposit := by
  intro u ctx w a ret w' _hvo _hInv hrun hdec
  obtain ⟨_, _, hw'⟩ := deposit_ok_inv ctx (World.creditValue w ctx.value) hrun
  simp [claim] at hdec
  rw [hw'] at hdec
  simp [depositPost] at hdec
  by_cases ha : a = ctx.sender
  · subst ha
    simp [credit] at hdec
    exact (Nat.not_lt.mpr (Nat.le_add_right _ _) hdec).elim
  · simp [credit_other _ ha] at hdec

theorem approve_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .approve :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨spender, amount⟩ ctx w a _ret w' _hInv hrun hdec => by
    rw [approve_ok] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [claim, approvePost] at hdec

theorem balanceOf_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .balanceOf :=
  NoUnauthorizedDecreaseFn_of_ok fun who ctx w a ret w' _hInv hrun hdec => by
    rw [balanceOf_returns_stored_balance] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [claim] at hdec

theorem allowance_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .allowance :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨owner, spender⟩ ctx w a ret w' _hInv hrun hdec => by
    rw [allowance_returns_stored] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [claim] at hdec

theorem totalSupply_auth : NoUnauthorizedDecreaseFn spec InvTrace claim Auth .totalSupply :=
  NoUnauthorizedDecreaseFn_of_ok fun u ctx w a ret w' _hInv hrun hdec => by
    rw [totalSupply_returns_stored] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [claim] at hdec

theorem weth_no_unauth {self : Address} :
    NoUnauthorizedDecrease spec self InvTrace claim Auth :=
  NoUnauthorizedDecrease.of_fns_credit (C := spec) fun fn =>
    match fn with
    | .deposit => deposit_auth
    | .withdraw =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) withdraw_auth
    | .transfer =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) transfer_auth
    | .transferFrom =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) transferFrom_auth
    | .approve =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) approve_auth
    | .balanceOf =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) balanceOf_auth
    | .allowance =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) allowance_auth
    | .totalSupply =>
      NoUnauthorizedDecreaseCreditFn_of_fn (by rfl) totalSupply_auth

/-! ### (c) Invariant preservation -/

theorem transfer_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .transfer :=
  PreservesInvFnAt_of_ok fun ⟨dst, amount⟩ ctx w ret w' _hself _hsne hInv hrun => by
    have hr : ret = true := transfer_returns_true ctx w dst amount hrun
    rw [hr] at hrun
    obtain ⟨hsub, hw'⟩ := transfer_ok_inv ctx w dst amount hrun
    subst hw'
    exact ⟨inv_of_transferPost w.self ctx.sender dst amount hInv.1 hsub, hInv.2⟩

theorem transferFrom_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .transferFrom :=
  PreservesInvFnAt_of_ok fun ⟨src, dst, amount⟩ ctx w ret w' _hself _hsne hInv hrun => by
    have hr : ret = true := transferFrom_returns_true ctx w src dst amount hrun
    rw [hr] at hrun
    obtain ⟨_, hsub, hw'⟩ := transferFrom_ok_inv ctx w src dst amount hrun
    subst hw'
    exact ⟨inv_of_transferPost w.self src dst amount hInv.1 hsub, hInv.2⟩

theorem withdraw_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .withdraw :=
  PreservesInvFnAt_of_ok fun amount ctx w _ret w' _hself _hsne hInv hrun => by
    obtain ⟨hbal, _, ⟨_, _, hw'⟩⟩ := withdraw_ok_inv ctx w amount hrun
    subst hw'
    exact ⟨inv_of_withdrawPost w.self ctx.sender amount hInv.1 hbal, hInv.2⟩

theorem deposit_preserves_inv (self : Address) :
    PreservesInvCreditFnAt spec InvTrace self .deposit := by
  intro _u ctx w _ret w' _hself _hsne _hvo hInv hrun
  obtain ⟨_, _, hw'⟩ := deposit_ok_inv ctx (World.creditValue w ctx.value) hrun
  subst hw'
  exact ⟨inv_of_depositPost w.self ctx.sender ⟨ctx.value⟩ hInv.1, hInv.2⟩

theorem approve_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .approve :=
  PreservesInvFnAt_of_ok fun ⟨spender, amount⟩ ctx w _ret w' _hself _hsne hInv hrun => by
    rw [approve_ok] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hInv.1, hInv.2⟩

theorem balanceOf_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .balanceOf :=
  PreservesInvFnAt_of_ok fun who ctx w _ret w' _hself _hsne hInv hrun => by
    rw [balanceOf_returns_stored_balance] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hInv

theorem allowance_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .allowance :=
  PreservesInvFnAt_of_ok fun ⟨owner, spender⟩ ctx w _ret w' _hself _hsne hInv hrun => by
    rw [allowance_returns_stored] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hInv

theorem totalSupply_preserves_inv (self : Address) :
    PreservesInvFnAt spec InvTrace self .totalSupply :=
  PreservesInvFnAt_of_ok fun _u ctx w _ret w' _hself _hsne hInv hrun => by
    rw [totalSupply_returns_stored] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hInv

theorem weth_preserves_inv (self : Address) : PreservesInvAt spec InvTrace self :=
  PreservesInvAt.of_fns_credit fun fn =>
    match fn with
    | .deposit => deposit_preserves_inv self
    | .withdraw =>
      PreservesInvCreditFnAt_of_fn (by rfl) (withdraw_preserves_inv self)
    | .transfer =>
      PreservesInvCreditFnAt_of_fn (by rfl) (transfer_preserves_inv self)
    | .transferFrom =>
      PreservesInvCreditFnAt_of_fn (by rfl) (transferFrom_preserves_inv self)
    | .approve =>
      PreservesInvCreditFnAt_of_fn (by rfl) (approve_preserves_inv self)
    | .balanceOf =>
      PreservesInvCreditFnAt_of_fn (by rfl) (balanceOf_preserves_inv self)
    | .allowance =>
      PreservesInvCreditFnAt_of_fn (by rfl) (allowance_preserves_inv self)
    | .totalSupply =>
      PreservesInvCreditFnAt_of_fn (by rfl) (totalSupply_preserves_inv self)

theorem weth_inv_rely {self : Address} :
    PreservesInvEnv spec InvTrace (HasRely.rely (C := spec) self) := by
  intro w x' hw _hr
  exact hw

theorem backed_env {w : World} {x' : ExtState}
    (hr : rely w.ext x') (h : Backed w) : Backed { w with ext := x' } :=
  Nat.le_trans h hr

theorem backed_deposit {ctx : Ctx} {w : World}
    {ret : Unit} {w' : World}
    (hb : World.nativeBalance w + ctx.value < wordBound)
    (hw : Inv w)
    (hrun : Tx.run depositTx ctx (World.creditValue w ctx.value) = .ok (ret, w')) :
    Backed w' := by
  obtain ⟨_, _, rfl⟩ := deposit_ok_inv ctx (World.creditValue w ctx.value) hrun
  have hnat :
      World.nativeBalance
        { World.creditValue w ctx.value with
            self := depositPost (World.creditValue w ctx.value).self ctx.sender
              ⟨ctx.value⟩
            log := (World.creditValue w ctx.value).log ++
              [.Deposit ctx.sender ⟨ctx.value⟩] } =
      World.nativeBalance w + ctx.value := by
    change World.nativeBalance (World.creditValue w ctx.value) = _
    exact nativeBalance_creditValue w ctx.value hb
  have hts :
      (depositPost (World.creditValue w ctx.value).self ctx.sender
        ⟨ctx.value⟩).totalSupply.raw =
      w.self.totalSupply.raw + ctx.value := by
    simp [depositPost, Amount.raw_add]
  rw [Backed, hnat, hts]
  exact Nat.add_le_add_right hw.2.1 ctx.value

theorem backed_withdraw (amount : Amount native) {ctx : Ctx}
    {w w' : World}
    (hw : Inv w)
    (hrun : Tx.run (withdraw amount) ctx w = .ok ((), w')) :
    Backed w' := by
  obtain ⟨_, hsup, x', hsend, rfl⟩ := withdraw_ok_inv ctx w amount hrun
  have hnat :
      World.nativeBalance
          { w with
            self := withdrawPost w.self ctx.sender amount
            ext := x'
            log := w.log ++ [.Withdrawal ctx.sender amount] } +
        amount.raw =
      World.nativeBalance w := by
    change HasSelfBalance.get x' + amount.raw = HasSelfBalance.get w.ext
    exact hw.2.2 ctx.sender amount.raw w.ext x' hsend
  have hts :
      (withdrawPost w.self ctx.sender amount).totalSupply.raw + amount.raw =
      w.self.totalSupply.raw := by
    simp [withdrawPost, Amount.raw_sub]
    exact Nat.sub_add_cancel hsup
  have hle :
      (withdrawPost w.self ctx.sender amount).totalSupply.raw + amount.raw ≤
        World.nativeBalance
            { w with
              self := withdrawPost w.self ctx.sender amount
              ext := x'
              log := w.log ++ [.Withdrawal ctx.sender amount] } +
          amount.raw := by
    rw [hts, hnat]
    exact hw.2.1
  exact Nat.le_of_add_le_add_right hle

theorem backed_transfer {ctx : Ctx} {w w' : World}
    (dst : Address) (amount : Amount native)
    (hw : Inv w)
    (hrun : Tx.run (transfer dst amount) ctx w = .ok (true, w')) :
    Backed w' := by
  obtain ⟨_, rfl⟩ := transfer_ok_inv ctx w dst amount hrun
  simp [Backed, transferPost]
  exact hw.2.1

theorem backed_transferFrom {ctx : Ctx} {w w' : World}
    (src dst : Address) (amount : Amount native)
    (hw : Inv w)
    (hrun : Tx.run (transferFrom src dst amount) ctx w = .ok (true, w')) :
    Backed w' := by
  obtain ⟨_, _, rfl⟩ := transferFrom_ok_inv ctx w src dst amount hrun
  simp [Backed, transferFromPost]
  exact hw.2.1

theorem backed_approve {ctx : Ctx} {w w' : World}
    (spender : Address) (amount : Amount native)
    (hw : Inv w)
    (hrun : Tx.run (approve spender amount) ctx w = .ok (true, w')) :
    Backed w' := by
  rw [approve_ok] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  simp [Backed, approvePost]
  exact hw.2.1

theorem backed_credit (fn : spec.Fn)
    (args : spec.Args fn) (ctx : Ctx) (w : World)
    (ret : spec.Ret fn) (w' : World)
    (hb : World.nativeBalance w + ctx.value < wordBound)
    (hw : Inv w)
    (hvo : spec.valueOk fn ctx.value = true)
    (hrun : Tx.run (spec.exec fn args) ctx (World.creditValue w ctx.value) =
      .ok (ret, w')) :
    Backed w' := by
  cases fn with
  | deposit =>
    exact backed_deposit hb hw hrun
  | withdraw =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    exact backed_withdraw args hw (by convert hrun)
  | transfer =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    have ht : ret = true := transfer_returns_true ctx w args.1 args.2 (by convert hrun)
    rw [ht] at hrun
    exact backed_transfer args.1 args.2 hw (by convert hrun)
  | transferFrom =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    have ht : ret = true :=
      transferFrom_returns_true ctx w args.1 args.2.1 args.2.2 (by convert hrun)
    rw [ht] at hrun
    exact backed_transferFrom args.1 args.2.1 args.2.2 hw (by convert hrun)
  | approve =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    rw [approve_ok args.1 args.2 (ctx := ctx) (w := w)] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [Backed, approvePost]
    exact hw.2.1
  | balanceOf =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    rw [balanceOf_returns_stored_balance ctx w args] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hw.2.1
  | allowance =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    rw [allowance_returns_stored ctx w args.1 args.2] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hw.2.1
  | totalSupply =>
    have hv : ctx.value = 0 := spec.value_eq_zero_of_valueOk (by rfl) hvo
    rw [hv, World.creditValue_zero] at hrun
    rw [totalSupply_returns_stored ctx w] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hw.2.1

theorem backed_step (self : Address) {c : Call spec} {w : World}
    (hw : Inv w) : Backed (step self (.call c) w) := by
  rw [step_eq_run self]
  split_ifs with hvo hwrap
  · exact hw.2.1
  · cases hrun : spec.exec c.fn c.args (c.toCtx self)
        (World.creditValue w c.value) with
    | error _ => exact hw.2.1
    | ok p =>
      have hb : World.nativeBalance w + c.value < wordBound := by
        by_cases hp : spec.payable c.fn = true
        · have hcw : creditWraps w c.value = false := by
            simp [hp] at hwrap
            exact hwrap
          exact creditWraps_false_lt w c.value hcw
        · have hpF : spec.payable c.fn = false := Bool.eq_false_iff.mpr hp
          have hv0 : c.value = 0 :=
            spec.value_eq_zero_of_valueOk hpF hvo
          simpa [hv0] using nativeBalance_lt_wordBound w
      exact backed_credit c.fn c.args (c.toCtx self) w p.1 p.2 hb hw hvo hrun
  · exact hw.2.1

theorem weth_inv_run (self : Address) {w : World}
    {tr : List (Step spec)}
    (hw : Inv w) (hW : Wf self tr w)
    (hR : RelyAlong self (HasRely.rely (C := spec) self) tr w) :
    Inv (run self tr w) := by
  induction tr generalizing w with
  | nil => simpa using hw
  | cons s rest ih =>
    match s with
    | .call c =>
      have ⟨hs, htl⟩ := hW
      have hTr : InvTrace (step self (.call c) w) :=
        weth_preserves_inv self c w hs (Inv_to_trace hw)
      have hB : Backed (step self (.call c) w) := backed_step self hw
      exact ih ⟨hTr.1, hB, hTr.2⟩ htl hR
    | .env x' =>
      have ⟨hr, htl⟩ := hR
      have hTr : InvTrace { w with ext := x' } :=
        weth_inv_rely (self := self) w x' (Inv_to_trace hw) hr
      exact ih ⟨hTr.1, backed_env hr hw.2.1, hTr.2⟩ hW htl

theorem deployed_inv {w : World}
    (h : Deployed spec w) : Inv w := by
  obtain ⟨hbals, hts, hO⟩ := h
  refine ⟨⟨∅, fun a _ => hbals a, ?sum⟩, ?backed, hO⟩
  · simp [hts]
  · simp [hts, Amount.raw_zero]

theorem weth_inv_of_reachable {self : Address} {w : World}
    (h : Reachable (C := spec) (HasRely.rely (C := spec) self) self w) :
    Inv w := by
  obtain ⟨w₀, tr, hDep, hW, hR, rfl⟩ := h
  exact weth_inv_run self (deployed_inv hDep) hW hR

namespace Proof

private theorem le_add (x y : Amount native) : x ≤ x + y := by
  simp [Amount.le_iff, Amount.raw_add]

private theorem raw_ite (p : Prop) [Decidable p] {α : Asset} (x y : Amount α) :
    (if p then x else y).raw = if p then x.raw else y.raw := by
  split_ifs <;> rfl

private theorem nat_ite_cover (f : Nat → Nat) (src dst a n : Nat)
    (hn : n ≤ f src) :
    f a ≤
      (if a = dst then (if dst = src then f src - n else f dst) + n
        else if a = src then f src - n else f a) +
      (if src = a then n else 0) := by
  split_ifs <;> subst_vars <;> omega

private theorem balances_transferPost (σ : Storage) (src dst : Address)
    (n : Amount native) (a : Address) (hn : n ≤ σ.balances src) :
    σ.balances a ≤ (transferPost σ src dst n).balances a +
      if src = a then n else 0 := by
  simp [Amount.le_iff, Amount.raw_add, transferPost, credit, debit,
    Amount.raw_sub, Function.update_apply, raw_ite] at hn ⊢
  exact nat_ite_cover (fun i => (σ.balances i).raw) src dst a n.raw hn

private theorem nat_ite_burn (f : Nat → Nat) (src a n : Nat)
    (hn : n ≤ f src) :
    f a ≤ (if a = src then f src - n else f a) + (if src = a then n else 0) := by
  split_ifs <;> subst_vars <;> omega

private theorem balances_withdrawPost (σ : Storage) (src : Address)
    (n : Amount native) (a : Address) (hn : n ≤ σ.balances src) :
    σ.balances a ≤ (withdrawPost σ src n).balances a +
      if src = a then n else 0 := by
  simp [Amount.le_iff, Amount.raw_add, withdrawPost, debit, Amount.raw_sub,
    Function.update_apply, raw_ite] at hn ⊢
  exact nat_ite_burn (fun i => (σ.balances i).raw) src a n.raw hn

private theorem spent_covers_ok (self : Address) (c : Call spec)
    (w w' : World) (a : Address) {r : spec.Ret c.fn}
    (h : spec.exec c.fn c.args (c.toCtx self) w = .ok (r, w')) :
    w.self.balances a ≤ w'.self.balances a + spentCall a c := by
  revert r h
  rcases c with ⟨sender, value, ts, bn, fn, args⟩
  cases fn <;> intro r h
  case transfer =>
    rcases args with ⟨dst, amount⟩
    have hrun : Tx.run (transfer dst amount)
        { sender, value, timestamp := ts, blockNumber := bn, self } w = .ok (r, w') := by
      simpa [Tx.run, spec_exec_transfer, Call.toCtx] using h
    have hr := transfer_returns_true { sender, value, timestamp := ts, blockNumber := bn, self } w dst amount
      hrun
    subst hr
    have ⟨hsub, hw'⟩ :=
      transfer_ok_inv { sender, value, timestamp := ts, blockNumber := bn, self } w dst amount hrun
    simp [spentCall, hw', Call.toCtx]
    exact balances_transferPost w.self sender dst amount a hsub
  case withdraw =>
    have hrun : Tx.run (withdraw args) { sender, value, timestamp := ts, blockNumber := bn, self } w =
        .ok (r, w') := by
      simpa [Tx.run, spec_exec_withdraw, Call.toCtx] using h
    have ⟨hsub, _, hx⟩ :=
      withdraw_ok_inv { sender, value, timestamp := ts, blockNumber := bn, self } w args hrun
    obtain ⟨_, _, hw'⟩ := hx
    simp [spentCall, hw', Call.toCtx]
    exact balances_withdrawPost w.self sender args a hsub
  case transferFrom =>
    rcases args with ⟨src, dst, amount⟩
    have hrun : Tx.run (transferFrom src dst amount)
        { sender, value, timestamp := ts, blockNumber := bn, self } w = .ok (r, w') := by
      simpa [Tx.run, spec_exec_transferFrom, Call.toCtx] using h
    have hr := transferFrom_returns_true { sender, value, timestamp := ts, blockNumber := bn, self } w
      src dst amount hrun
    subst hr
    have ⟨_, hsub, hw'⟩ :=
      transferFrom_ok_inv { sender, value, timestamp := ts, blockNumber := bn, self } w src dst amount hrun
    simp [spentCall, hw', Call.toCtx]
    have hbals :
        (transferFromPost w.self src sender dst amount).balances =
          (transferPost w.self src dst amount).balances := rfl
    rw [hbals]
    exact balances_transferPost w.self src dst amount a hsub
  case deposit =>
    have hrun : Tx.run depositTx { sender, value, timestamp := ts, blockNumber := bn, self } w =
        .ok (r, w') := by
      simpa [Tx.run, spec_exec_deposit, depositTx, Call.toCtx] using h
    have ⟨_, _, hw'⟩ :=
      deposit_ok_inv { sender, value, timestamp := ts, blockNumber := bn, self } w hrun
    simp [spentCall, hw', Call.toCtx]
    by_cases hd : sender = a
    · subst hd
      simp [depositPost, credit]
    · simp [depositPost, credit_other _ (Ne.symm hd)]
  case approve =>
    rcases args with ⟨spender, amount⟩
    have hrun : Tx.run (approve spender amount)
        { sender, value, timestamp := ts, blockNumber := bn, self } w = .ok (r, w') := by
      simpa [Tx.run, spec_exec_approve, Call.toCtx] using h
    rw [approve_ok { sender, value, timestamp := ts, blockNumber := bn, self } w spender amount] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [spentCall, approvePost]
  case balanceOf =>
    have hrun : Tx.run (balanceOf args) { sender, value, timestamp := ts, blockNumber := bn, self } w =
        .ok (r, w') := by
      simpa [Tx.run, spec_exec_balanceOf, Call.toCtx] using h
    rw [balanceOf_returns_stored_balance { sender, value, timestamp := ts, blockNumber := bn, self } w args]
      at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [spentCall]
  case allowance =>
    rcases args with ⟨owner, spender⟩
    have hrun : Tx.run (allowance owner spender)
        { sender, value, timestamp := ts, blockNumber := bn, self } w = .ok (r, w') := by
      simpa [Tx.run, spec_exec_allowance, Call.toCtx] using h
    rw [allowance_returns_stored { sender, value, timestamp := ts, blockNumber := bn, self } w owner spender]
      at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [spentCall]
  case totalSupply =>
    have hrun : Tx.run totalSupply { sender, value, timestamp := ts, blockNumber := bn, self } w =
        .ok (r, w') := by
      simpa [Tx.run, spec_exec_totalSupply, Call.toCtx] using h
    rw [totalSupply_returns_stored { sender, value, timestamp := ts, blockNumber := bn, self } w] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [spentCall]

private theorem spent_covers_accepted (self : Address) (c : Call spec)
    (w : World) (a : Address)
    (hacc : accepted self c w = true) :
    w.self.balances a ≤ (step self (.call c) w).self.balances a +
      spentCall a c := by
  obtain ⟨_, _, ⟨⟨r, w'⟩, hrun, hstep⟩⟩ := accepted_ok hacc
  rw [hstep]
  simpa [World.creditValue_self] using
    spent_covers_ok self c (World.creditValue w c.value) w' a hrun

theorem weth_backed (w : State) : w.self.totalSupply ≤ w.nativeBalance := by
  have hInv := weth_inv_of_reachable (self := w.addr) w.reachable
  simp [State.nativeBalance, Amount.le_iff, State.self]
  exact hInv.2.1

private theorem foldAccepted_raw_add {s : State} (t : Txs s) (a : Address)
    (x : Amount native) :
    (t.foldAccepted (fun acc c _ => acc + HasSpent.spentCall (C := spec) a c) x).raw =
      x.raw + (Txs.spent t a).raw := by
  induction t generalizing x with
  | nil => simp [Txs.foldAccepted, Txs.spent, Amount.raw_add]
  | @call s c hne rest ih =>
    simp [Txs.foldAccepted, Txs.spent]
    split_ifs
    · have hx := ih (x + HasSpent.spentCall (C := spec) a (c))
      have hsc := ih (HasSpent.spentCall (C := spec) a (c))
      rw [hx, hsc]
      exact Nat.add_assoc _ _ _
    · exact ih x
  | @env s _x' _hr rest ih =>
    simp [Txs.foldAccepted, Txs.spent]
    exact ih x

theorem weth_no_unauthorized_extraction (w : State) (t : Txs w) (a : Address) :
    w.self.balances a ≤ t.end.self.balances a + t.spent a := by
  induction t with
  | nil =>
    simp [Txs.spent, Txs.foldAccepted, Amount.le_iff, Amount.raw_add]
  | @call s c hne rest ih =>
    simp [Txs.spent, Txs.foldAccepted]
    by_cases hacc : accepted s.addr c s.w = true
    · have hcov := spent_covers_accepted s.addr c s.w a hacc
      have hstepEq : (s.afterCall c hne).w = step s.addr (.call c) s.w :=
        State.afterCall_w s c hne
      have hthis : s.self.balances a ≤
          (s.afterCall c hne).self.balances a + spentCall a c := by
        simpa [State.self, hstepEq] using hcov
      simp [Amount.le_iff, Amount.raw_add] at hthis ih
      have hfold := foldAccepted_raw_add rest a
        (HasSpent.spentCall (C := spec) a c)
      simp [Amount.le_iff, Amount.raw_add, Txs.spent, Txs.foldAccepted, hacc,
        HasSpent.spentCall] at hthis ih hfold ⊢
      rw [hfold]
      refine Nat.le_trans hthis ?_
      have hih := Nat.add_le_add_right ih (spentCall a c).raw
      convert hih using 1
      ac_rfl
    · have hfalse : accepted s.addr c s.w = false :=
        Bool.eq_false_iff.mpr hacc
      have hstep := step_of_not_accepted hfalse
      have hs : (s.afterCall c hne).self = s.self := by
        simp only [State.self, State.afterCall_w]
        exact congrArg World.self hstep
      simp [hs, Txs.spent, Txs.foldAccepted, hfalse] at ih ⊢
      exact ih
  | @env s x' hr rest ih =>
    have hs : (s.afterEnv x' hr).self = s.self := State.afterEnv_self s x' hr
    simpa [Txs.spent, Txs.foldAccepted, hs] using ih

end Proof

end WETH
