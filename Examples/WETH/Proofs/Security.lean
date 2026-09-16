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
WETH anti-extraction: wrapped `claim` is storage-only. `withdraw` burns
then `Native.send`s the same amount to the caller (`NativeOutflow`).
`deposit` is payable and only increases claims. `Inv` carries finite
support, `totalSupply ≤ nativeBalance`, and `DebitsOnSend`. Trace
preservation uses the first and last conjuncts: BitVec wrap of a payable
credit can drop `nativeBalance` below `totalSupply`.
-/

lemma Auth_transfer (a : Address) (ctx : Ctx) (dst : Address)
    (n : Amount native) (w : World Storage ExtState Event) :
    Auth a (Call.ofCtx ctx .transfer (dst, n)) w ↔ ctx.sender = a :=
  Iff.rfl

lemma Auth_withdraw (a : Address) (ctx : Ctx) (n : Amount native)
    (w : World Storage ExtState Event) :
    Auth a (Call.ofCtx ctx .withdraw n) w ↔
      ctx.sender = a ∧ n ≤ w.self.balances a :=
  Iff.rfl

lemma Auth_transferFrom (a : Address) (ctx : Ctx) (src dst : Address)
    (n : Amount native) (w : World Storage ExtState Event) :
    Auth a (Call.ofCtx ctx .transferFrom (src, dst, n)) w ↔
      src = a ∧ n ≤ w.self.allowances src ctx.sender :=
  Iff.rfl

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

/-- Trace invariant: finite support and honest `Native.send`. Backing
`totalSupply ≤ nativeBalance` is the extra conjunct of `Inv` used by
`weth_backed`. Payable `creditValue` wraps `selfBalance` at `2^256`, so
that conjunct is not preserved by `deposit` after a donation near the
word bound; extraction of wrapped claims does not need it. -/
private abbrev InvTrace (w : World Storage ExtState Event) : Prop :=
  InvStorage w.self ∧ DebitsOnSend w.oracle

private theorem Inv_to_trace {w : World Storage ExtState Event} (h : Inv w) :
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
    {ctx : Ctx} {w w' : World Storage ExtState Event}
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

theorem weth_no_unauth : NoUnauthorizedDecrease spec InvTrace claim Auth :=
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

theorem weth_inv_rely : PreservesInvEnv spec InvTrace rely := by
  intro w x' hw _hr
  exact hw

namespace Proof

theorem weth_backed {w : World Storage ExtState Event} (h : Inv w) :
    w.self.totalSupply.raw ≤ World.nativeBalance w :=
  h.2.1

theorem weth_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  no_unauthorized_extraction_at weth_no_unauth (weth_preserves_inv self)
    weth_inv_rely
    (ClaimMonoEnv.of_self (fun a (s : Storage) => (s.balances a).raw) rely)
    tr w a (Inv_to_trace hw) hW hR hA

end Proof

end WETH
