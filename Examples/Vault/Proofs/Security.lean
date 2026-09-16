import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
import Examples.Vault.Spec
import Examples.Vault.Proofs.Tx
import Stdlib.SharesTheorems

set_option linter.unusedSimpArgs false

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-!
Security obligations for the vault. `InvT` locks the bound asset, the oracle,
and `IERC20.Spec`. Well-formed traces use `PreservesInvFnAt`
(`ctx.self = self`, `ctx.sender ≠ self`).
-/

/-- Invariant plus the callee promise, pinned to the starting asset/oracle. -/
def InvT (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (w : World) : Prop :=
  Inv self w ∧ w.self.asset = asset ∧ w.oracle = oracle ∧
    IERC20.Spec (asset.impl : AssetImpl)

/-! ### Environment -/

theorem inv_rely (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) :
    PreservesInvEnv spec (InvT self asset oracle)
      (HasRely.rely (C := spec) self) := by
  intro w x' ⟨⟨hst, hbd⟩, ha, ho, hT⟩ hr
  have ⟨hbal, _hsup⟩ : vaultRely self asset oracle w.ext x' := by
    simpa [HasRely.rely, vaultRely, ha, ho] using hr
  refine ⟨⟨hst, ?_⟩, ha, ho, by simpa [IERC20.Ref.impl] using hT⟩
  have hH : holdings self w = (viewBal asset self oracle w.ext).raw := by
    simp [holdings_view, ha, ho]
  have hH' : holdings self { w with ext := x' } =
      (viewBal asset self oracle x').raw := by
    simp [holdings_view, ha, ho]
  rw [hH']
  exact Nat.le_trans (hH ▸ hbd) (Nat.mul_le_mul_right _ hbal)

/-! ### Share-support preservation -/

private abbrev rawShares (shares : Address → Amount vShare) : Address → Nat :=
  fun a => (shares a).raw

private theorem rawShares_update (shares : Address → Amount vShare) (who : Address)
    (n : Amount vShare) :
    rawShares (Function.update shares who n) =
      Function.update (rawShares shares) who n.raw := by
  funext a
  by_cases h : a = who <;> simp [rawShares, Function.update, h]

private theorem nat_sum_update_add (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i (f i + n)) = H.sum f + n := by
  have hS := sum_update_mem H f hi (f i + n)
  omega

private theorem nat_sum_update_sub (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) {n : Nat} (hn : n ≤ f i) :
    H.sum (Function.update f i (f i - n)) = H.sum f - n := by
  have hS := sum_update_mem H f hi (f i - n)
  omega

private theorem invStorage_of_depositPost (σ : Storage) (who : Address)
    (minted : Nat) (hInv : InvStorage σ) :
    InvStorage (depositPost σ who minted) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  by_cases ht : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ who := by intro h; subst h; exact ha ht
      simp [depositPost, Function.update_of_ne hne]
      exact h0 a ha
    · have hsum' :
          H.sum (rawShares (depositPost σ who minted).shares) =
            H.sum (rawShares σ.shares) + minted := by
        simp only [depositPost, rawShares_update, Amount.raw_add, Amount.raw_ofWord]
        exact nat_sum_update_add H (rawShares σ.shares) ht minted
      change H.sum (rawShares (depositPost σ who minted).shares) =
        (depositPost σ who minted).totalShares.raw
      rw [hsum', hsumr]
      simp [depositPost, Amount.raw_add, Amount.raw_ofWord, Nat.add_comm]
  · refine ⟨insert who H, ?_, ?_⟩
    · intro a ha
      have hat : a ≠ who := by
        intro h; subst h; exact ha (Finset.mem_insert_self _ _)
      have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
      simp [depositPost, Function.update_of_ne hat]
      exact h0 a haH
    · have hb0 : σ.shares who = 0 := h0 who ht
      have hwho0 : (σ.shares who).raw = 0 := by
        simpa [Amount.raw_zero] using congrArg Amount.raw hb0
      have hupd :
          (fun x =>
            (Function.update σ.shares who
              (σ.shares who + Amount.ofWord minted) x).raw) =
            Function.update (rawShares σ.shares) who
              ((σ.shares who).raw + minted) := by
        funext x
        by_cases hx : x = who <;>
          simp [rawShares, Function.update, hx, Amount.raw_add, Amount.raw_ofWord]
      have hframe :=
        sum_update_not_mem H (rawShares σ.shares) ht
          ((σ.shares who).raw + minted)
      have hframe' :
          H.sum (Function.update (rawShares σ.shares) who minted) =
            H.sum (rawShares σ.shares) := by
        simpa [hwho0] using hframe
      have hsum' :
          (∑ a ∈ insert who H, rawShares (depositPost σ who minted).shares a) =
            H.sum (rawShares σ.shares) + minted := by
        rw [Finset.sum_insert ht]
        simp only [depositPost, Function.update_self, rawShares, Amount.raw_add,
          Amount.raw_ofWord]
        simp [hupd, hframe', hwho0, Nat.add_comm]
      change (∑ a ∈ insert who H, ((depositPost σ who minted).shares a).raw) =
        (depositPost σ who minted).totalShares.raw
      rw [hsum', hsumr]
      simp [depositPost, Amount.raw_add, Amount.raw_ofWord, Nat.add_comm]

private theorem invStorage_of_withdrawPost (σ : Storage) (who : Address)
    (sharesIn : Amount vShare)
    (hInv : InvStorage σ) (hn : sharesIn ≤ σ.shares who) :
    InvStorage (withdrawPost σ who sharesIn) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  have hn' : sharesIn.raw ≤ (σ.shares who).raw := hn
  by_cases hs : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ who := by intro h; subst h; exact ha hs
      simp [withdrawPost, Function.update_of_ne ha_src]
      exact h0 a ha
    · have hsumd :
          H.sum (rawShares (withdrawPost σ who sharesIn).shares) =
            H.sum (rawShares σ.shares) - sharesIn.raw := by
        simp only [withdrawPost, rawShares_update, Amount.raw_sub]
        exact nat_sum_update_sub H (rawShares σ.shares) hs hn'
      change H.sum (rawShares (withdrawPost σ who sharesIn).shares) =
        (withdrawPost σ who sharesIn).totalShares.raw
      rw [hsumd, hsumr]
      simp [withdrawPost, Amount.raw_sub]
  · have hb0 : σ.shares who = 0 := h0 who hs
    have hn0 : sharesIn = 0 := by
      have hwho0 : (σ.shares who).raw = 0 := by
        simpa [Amount.raw_zero] using congrArg Amount.raw hb0
      exact Amount.ext (Nat.eq_zero_of_le_zero (hn'.trans_eq hwho0))
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp [withdrawPost, hn0]
      exact h0 a ha
    · simp [withdrawPost, hn0, hsum]

private theorem invStorage_shares_le (σ : Storage) (hInv : InvStorage σ) (x : Address) :
    σ.shares x ≤ σ.totalShares := by
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hx : x ∈ H
  · have hle : (σ.shares x).raw ≤ H.sum (fun a => (σ.shares a).raw) := by
      rw [← Finset.sum_erase_add (s := H) (f := fun a => (σ.shares a).raw) hx]
      exact Nat.le_add_left _ _
    exact (Amount.le_iff _ _).mpr (hsum ▸ hle)
  · have hz : σ.shares x = 0 := h0 x hx
    simp [Amount.le_iff, hz, Amount.raw_zero]

private theorem invStorage_bystander_zero (σ : Storage) (who a : Address)
    (hInv : InvStorage σ) (hne : who ≠ a) (hall : σ.totalShares ≤ σ.shares who) :
    σ.shares a = 0 := by
  have hwho := invStorage_shares_le σ hInv who
  have heq : (σ.shares who).raw = σ.totalShares.raw :=
    Nat.le_antisymm ((Amount.le_iff _ _).mp hwho) ((Amount.le_iff _ _).mp hall)
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hw : who ∈ H
  · have herase : (H.erase who).sum (fun x => (σ.shares x).raw) = 0 := by
      have hsplit := Finset.sum_erase_add (s := H) (f := fun x => (σ.shares x).raw) hw
      rw [hsum, heq] at hsplit
      exact Nat.add_eq_right.mp hsplit
    by_cases ha : a ∈ H
    · have hae : a ∈ H.erase who := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
      have hle : (σ.shares a).raw ≤ (H.erase who).sum (fun x => (σ.shares x).raw) := by
        rw [← Finset.sum_erase_add (s := H.erase who)
          (f := fun x => (σ.shares x).raw) hae]
        exact Nat.le_add_left _ _
      exact Amount.ext (Nat.eq_zero_of_le_zero (hle.trans_eq herase))
    · exact h0 a ha
  · have hwho0 : σ.shares who = 0 := h0 who hw
    have hts0 : σ.totalShares.raw = 0 :=
      Nat.eq_zero_of_le_zero (by
        have hwho0r : (σ.shares who).raw = 0 := by
          simpa [Amount.raw_zero] using congrArg Amount.raw hwho0
        exact ((Amount.le_iff _ _).mp hall).trans_eq hwho0r)
    by_cases ha : a ∈ H
    · have hle : (σ.shares a).raw ≤ H.sum (fun x => (σ.shares x).raw) := by
        rw [← Finset.sum_erase_add (s := H) (f := fun x => (σ.shares x).raw) ha]
        exact Nat.le_add_left _ _
      exact Amount.ext (Nat.eq_zero_of_le_zero (hle.trans_eq (hsum.trans hts0)))
    · exact h0 a ha

/-- Virtual-offset redeemable assets of `a` against holdings `TA`. -/
private def rate (σ : Storage) (TA : Nat) (a : Address) : Nat :=
  Shares.toAssetsRaw offset (σ.shares a).raw TA σ.totalShares.raw

private theorem claim_eq_rate (self a : Address)
    (w : World) :
    claim self a w = rate w.self (holdings self w) a :=
  rfl

/-- Deposit never decreases an offset claim when holdings rise by `assets`. -/
private theorem rate_le_of_depositPost (σ : Storage) (who a : Address)
    (ta assets : Amount vaultAsset) :
    let m := mintedShares σ.totalShares ta assets
    rate σ ta.raw a ≤
      rate (depositPost σ who m) (ta.raw + assets.raw) a := by
  set m := mintedShares σ.totalShares ta assets
  set V : Nat := Word.scale offset.decimals
  have hV : 0 < σ.totalShares.raw + V :=
    Nat.lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 10))
      (Nat.le_add_left V σ.totalShares.raw)
  have hm : m = assets.raw * (σ.totalShares.raw + V) / (ta.raw + 1) := rfl
  unfold rate
  simp only [Shares.toAssetsRaw]
  have hTS : 0 < σ.totalShares.raw + V := hV
  by_cases ha : a = who
  · subst ha
    simp only [depositPost, Function.update_self, Amount.raw_add, Amount.raw_ofWord, hm]
    have hmono :=
      deposit_rate_nondecreasing (ta.raw + 1) (σ.totalShares.raw + V)
        (σ.shares a).raw assets.raw hTS
    have hstep :=
      Nat.le_trans hmono (Nat.div_le_div_right (Nat.mul_le_mul_right
        (ta.raw + 1 + assets.raw) (Nat.le_add_right _ m)))
    convert hstep using 1
    simp [V, hm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  · simp only [depositPost, Function.update_of_ne ha, Amount.raw_add,
      Amount.raw_ofWord, hm]
    have hmono :=
      deposit_rate_nondecreasing (ta.raw + 1) (σ.totalShares.raw + V)
        (σ.shares a).raw assets.raw hTS
    convert hmono using 1
    simp [V, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Another account's withdraw does not decrease an offset claim. -/
private theorem rate_le_of_withdrawPost (σ : Storage) (who a : Address)
    (ta : Amount vaultAsset) (sharesIn : Amount vShare)
    (hne : who ≠ a) (hsup : sharesIn ≤ σ.totalShares) :
    rate σ ta.raw a ≤
      rate (withdrawPost σ who sharesIn)
        (ta.raw - redeemedAssets σ.totalShares ta sharesIn) a := by
  set V : Nat := Word.scale offset.decimals
  have hVpos : 0 < V := Nat.pow_pos (by decide : 0 < 10)
  have hTS : 0 < σ.totalShares.raw + V :=
    Nat.lt_of_lt_of_le hVpos (Nat.le_add_left V σ.totalShares.raw)
  have hs_lt : sharesIn.raw < σ.totalShares.raw + V :=
    Nat.lt_of_le_of_lt ((Amount.le_iff _ _).mp hsup)
      (Nat.lt_add_of_pos_right hVpos)
  unfold rate
  simp only [Shares.toAssetsRaw, withdrawPost, Function.update_of_ne hne.symm,
    Amount.raw_sub]
  have hr : redeemedAssets σ.totalShares ta sharesIn =
      sharesIn.raw * (ta.raw + 1) / (σ.totalShares.raw + V) := by
    unfold redeemedAssets Shares.toAssetsRaw
    rw [Nat.mul_comm]
  have hs : sharesIn.raw ≤ σ.totalShares.raw := (Amount.le_iff _ _).mp hsup
  have hdenEq :
      σ.totalShares.raw - sharesIn.raw + V =
        σ.totalShares.raw + V - sharesIn.raw := (Nat.sub_add_comm hs).symm
  have hr_le : redeemedAssets σ.totalShares ta sharesIn ≤ ta.raw + 1 := by
    have hle : sharesIn.raw * (ta.raw + 1) ≤
        (σ.totalShares.raw + V) * (ta.raw + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_trans hs (Nat.le_add_right _ _))
    rw [hr]
    exact Nat.div_le_of_le_mul hle
  set r := redeemedAssets σ.totalShares ta sharesIn
  have hnum : (ta.raw + 1) - r ≤ (ta.raw - r) + 1 := by
    cases Nat.lt_or_ge ta.raw r with
    | inl hlt =>
      have hz : ta.raw - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
      rw [hz]
      have : r = ta.raw + 1 := Nat.le_antisymm hr_le (Nat.succ_le_of_lt hlt)
      simp [this]
    | inr hge =>
      rw [Nat.sub_add_comm hge]
  have hmono :=
    withdraw_rate_nondecreasing (ta.raw + 1) (σ.totalShares.raw + V)
      (σ.shares a).raw sharesIn.raw hTS hs_lt
  have hmono' :
      (σ.shares a).raw * (ta.raw + 1) / (σ.totalShares.raw + V) ≤
        (σ.shares a).raw * ((ta.raw + 1) - r) /
          (σ.totalShares.raw + V - sharesIn.raw) := by
    simpa [hr] using hmono
  have hstep :
      (σ.shares a).raw * ((ta.raw + 1) - r) /
          (σ.totalShares.raw + V - sharesIn.raw) ≤
        (σ.shares a).raw * ((ta.raw - r) + 1) /
          (σ.totalShares.raw - sharesIn.raw + V) := by
    rw [hdenEq]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hnum)
  simpa [V, r] using Nat.le_trans hmono' hstep

private theorem nat_add_div_le (x y d : Nat) : x / d + y / d ≤ (x + y) / d := by
  by_cases hd : d = 0
  · subst hd; simp
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hx : d * (x / d) ≤ x := Nat.mul_div_le x d
    have hy : d * (y / d) ≤ y := Nat.mul_div_le y d
    have hsum : d * (x / d + y / d) ≤ x + y := by
      rw [Nat.mul_add]; exact Nat.add_le_add hx hy
    exact (Nat.le_div_iff_mul_le hpos).mpr (Nat.mul_comm _ _ ▸ hsum)

private theorem sum_div_le_div_sum {α : Type} [DecidableEq α]
    (H : Finset α) (f : α → Nat) (d : Nat) :
    H.sum (fun a => f a / d) ≤ H.sum f / d := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact Nat.le_trans (Nat.add_le_add (Nat.le_refl (f x / d)) ih)
      (nat_add_div_le (f x) (S.sum f) d)

private theorem offset_claims_le (A S V : Nat) (hV : 0 < V)
    (h : S ≤ A * V) :
    S * (A + 1) / (S + V) ≤ A := by
  have _hden : 0 < S + V := Nat.lt_of_lt_of_le hV (Nat.le_add_left V S)
  have hmul : S * (A + 1) ≤ (S + V) * A := by
    calc
      S * (A + 1) = S * A + S := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ A * S + A * V := Nat.add_le_add (Nat.mul_comm S A ▸ Nat.le_refl _) h
      _ = A * (S + V) := (Nat.mul_add A S V).symm
      _ = (S + V) * A := Nat.mul_comm _ _
  exact Nat.div_le_of_le_mul hmul

private theorem sum_mul_const {α : Type} [DecidableEq α]
    (H : Finset α) (f : α → Nat) (c : Nat) :
    H.sum (fun a => f a * c) = H.sum f * c := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, Nat.add_mul]

theorem inv_solvent (self : Address) (w : World)
    (h : Inv self w) :
    Solvent (claim self) holdings self w := by
  obtain ⟨⟨H, h0, hs⟩, hbd⟩ := h
  refine ⟨H, ?_, ?_⟩
  · intro a ha
    have hs0 := h0 a ha
    simp [claim, Shares.toAssetsRaw, hs0, Amount.raw_zero]
  · have hV : 0 < Word.scale offset.decimals :=
      Nat.pow_pos (by decide : 0 < 10)
    have hcl :
        H.sum (fun a => claim self a w) =
          H.sum (fun a => (w.self.shares a).raw * (holdings self w + 1) /
            (w.self.totalShares.raw + Word.scale offset.decimals)) := by
      apply Finset.sum_congr rfl
      intro a _; simp [claim, Shares.toAssetsRaw]
    have hsum :
        H.sum (fun a => (w.self.shares a).raw * (holdings self w + 1) /
            (w.self.totalShares.raw + Word.scale offset.decimals)) ≤
          w.self.totalShares.raw * (holdings self w + 1) /
            (w.self.totalShares.raw + Word.scale offset.decimals) := by
      have := sum_div_le_div_sum H
        (fun a => (w.self.shares a).raw * (holdings self w + 1))
        (w.self.totalShares.raw + Word.scale offset.decimals)
      have hfactor :
          H.sum (fun a => (w.self.shares a).raw * (holdings self w + 1)) =
            w.self.totalShares.raw * (holdings self w + 1) := by
        rw [sum_mul_const, hs]
      simpa [hfactor] using this
    have hcov :=
      offset_claims_le (holdings self w) w.self.totalShares.raw
        (Word.scale offset.decimals) hV hbd
    rw [hcl]
    exact Nat.le_trans hsum hcov

private theorem holdings_add_of_transferFrom
    (self : Address) {ctx : Ctx} {w w1 : World}
    {assets : Amount vaultAsset}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hcall : Tx.run (tfCall w.self.asset ctx.sender ctx.self assets) ctx w =
      .ok (true, w1)) :
    holdings self w1 = holdings self w + assets.raw := by
  subst hself
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w.view) (w' := w1.view)
    (by
      have hopt := Tx.run_ok_toOption hcall
      have := congrArg (Option.map (Prod.map id World.view)) hopt
      simpa [impl_transferFrom] using this)
  have hdst := hmoves.2.1 hsne
  have hframe := transferFrom_frame (by simpa [tfCall] using hcall)
  simpa [holdings, holdingsAt, IERC20.Ref.impl, Amount.raw_add, hframe.1,
    hframe.2.1, World.view] using
    congrArg Amount.raw hdst

private theorem holdings_sub_of_transfer
    (self : Address) {ctx : Ctx} {w wCall w1 : World}
    {amt : Amount vaultAsset}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (ha : wCall.self.asset = w.self.asset) (ho : wCall.oracle = w.oracle)
    (hx : wCall.ext = w.ext)
    (hcall : Tx.run (trCall w.self.asset ctx.sender amt) ctx wCall =
      .ok (true, w1)) :
    holdings self w1 + amt.raw = holdings self w := by
  subst hself
  have hTcall : IERC20.Spec (wCall.self.asset.impl : AssetImpl) := by
    simpa [IERC20.Ref.impl, ha] using hT
  have hrunT :
      wCall.self.asset.impl.transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall.view =
        some (true, w1.view) := by
    have htr' :
        Tx.run (trCall w.self.asset ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := w.self.asset) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      simpa using hcall
    have hopt := Tx.run_ok_toOption htr'
    have := congrArg (Option.map (Prod.map id World.view)) hopt
    simpa [impl_transfer, ha] using this
  have hmoves := hTcall.transfer_moves hrunT
  have hto := hmoves.2.1 hsne.symm
  have hsumr := congrArg Amount.raw hmoves.1
  rw [Amount.raw_add, Amount.raw_add] at hsumr
  simp at hsumr
  have htor := congrArg Amount.raw hto
  simp [Amount.raw_add] at htor
  have heq0 : holdings ctx.self wCall = holdings ctx.self w :=
    holdings_congr ctx.self (by simp [ha]) ho hx
  have hframe := transfer_frame (w := wCall) (by simpa [trCall, ha] using hcall)
  have hs : w1.self = wCall.self := hframe.1
  rw [← heq0]
  simp [holdings, holdingsAt, hs] at hsumr htor ⊢
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

private theorem claim_le_of_rely (self : Address)
    (asset : IERC20.Ref vaultAsset) (oracle : Oracle ExtState)
    (w : World) (x' : ExtState) (a : Address)
    (ha : w.self.asset = asset) (ho : w.oracle = oracle)
    (hr : vaultRely self asset oracle w.ext x') :
    claim self a w ≤ claim self a { w with ext := x' } := by
  obtain ⟨hbal, _⟩ := hr
  have hH : holdings self w = (viewBal asset self oracle w.ext).raw := by
    simp [holdings_view, ha, ho]
  have hH' : holdings self { w with ext := x' } =
      (viewBal asset self oracle x').raw := by
    simp [holdings_view, ha, ho]
  rw [claim_eq_rate, claim_eq_rate, hH, hH']
  dsimp [rate]
  simp [Shares.toAssetsRaw]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hbal 1))

/-! ### Invariant preservation -/

section InvPreserve

variable (self : Address) (asset : IERC20.Ref vaultAsset) (oracle : Oracle ExtState)

theorem deposit_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .deposit :=
  PreservesInvFnAt_of_ok fun assets ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨hst, hbd⟩, ha, ho, hT⟩ := hInvT
    have hok := deposit_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := deposit_post assets hok hrun
    obtain ⟨w1, htf, hself1, hor1, _, hext, _⟩ := deposit_call assets hok hrun
    have hT' : IERC20.Spec (w.self.asset.impl : AssetImpl) := by
      simpa [IERC20.Ref.impl, ha] using hT
    have hTA : holdings self w = hok.ta.raw := by
      subst hself
      exact viewBal?_some_holdings ctx.self hok.viewOk
    have hhold := holdings_add_of_transferFrom self hself hsne hT' htf
    have hhold' : holdings self w' = holdings self w1 :=
      holdings_congr self (by simp [hσ, depositPost, hself1])
        (hor.trans hor1.symm) hext
    have hH' : holdings self w' = holdings self w + assets.raw := by
      rw [hhold', hhold]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa [hσ] using
        invStorage_of_depositPost w.self ctx.sender
          (mintedShares w.self.totalShares hok.ta assets) hst
    · rw [hσ]
      simp only [depositPost, Amount.raw_add, Amount.raw_ofWord, mintedShares]
      have hbd' : w.self.totalShares.raw ≤ hok.ta.raw * Word.scale offset.decimals :=
        hTA ▸ hbd
      simpa [hH', hTA] using Shares.toSharesRaw_preserves_inv offset hbd'
    · simpa [hσ, depositPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, depositPost, ha] using hT

theorem withdraw_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .withdraw :=
  PreservesInvFnAt_of_ok fun sharesIn ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨hst, hbd⟩, ha, ho, hT⟩ := hInvT
    have hok := withdraw_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := withdraw_post sharesIn hok hrun
    obtain ⟨w1, htr, hself1, hor1, hext, _, _⟩ := withdraw_call sharesIn hok hrun
    have hT' : IERC20.Spec (w.self.asset.impl : AssetImpl) := by
      simpa [IERC20.Ref.impl, ha] using hT
    have hTA : holdings self w = hok.ta.raw := by
      subst hself
      exact viewBal?_some_holdings ctx.self hok.viewOk
    have hhold := holdings_sub_of_transfer self hself hsne hT'
      (wCall := withdrawTailWorld w ctx.sender sharesIn)
      (by simp [withdrawTailWorld, withdrawPost]) rfl rfl
      (by simpa [withdrawTailWorld] using htr)
    have hhold' : holdings self w' = holdings self w1 :=
      holdings_congr self (by simp [hσ, withdrawPost, hself1])
        (hor.trans hor1.symm) hext
    set amt := Amount.ofWord (redeemedAssets w.self.totalShares hok.ta sharesIn)
    have hH' : holdings self w' + amt.raw = holdings self w := by
      rw [hhold', hhold]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa [hσ] using
        invStorage_of_withdrawPost w.self ctx.sender sharesIn hst hok.bal
    · rw [hσ]
      simp only [withdrawPost, Amount.raw_sub]
      have hbd' : w.self.totalShares.raw ≤ hok.ta.raw * Word.scale offset.decimals :=
        hTA ▸ hbd
      have hsub : holdings self w' =
          hok.ta.raw - redeemedAssets w.self.totalShares hok.ta sharesIn := by
        have : amt.raw = redeemedAssets w.self.totalShares hok.ta sharesIn :=
          Amount.raw_ofWord _
        rw [hTA] at hH'
        rw [this] at hH'
        exact Nat.eq_sub_of_add_eq hH'
      simpa [hsub, redeemedAssets] using
        Shares.toAssetsRaw_preserves_inv (o := offset)
          ((Amount.le_iff _ _).mp hok.supply) hbd'
    · simpa [hσ, withdrawPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, withdrawPost, ha] using hT

theorem pause_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .pause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := pause_ok howner
    simp [worldAfter, hrun]
    exact ⟨hInv, ha, ho, hT⟩
  · have hrun := pause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem unpause_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .unpause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := unpause_ok howner
    simp [worldAfter, hrun]
    exact ⟨hInv, ha, ho, hT⟩
  · have hrun := unpause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem isPaused_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .isPaused := by
  intro u ctx w _ _ hInvT
  unfold worldAfter
  rw [isPaused_returns_stored]
  exact hInvT

private theorem previewDeposit_worldAfter (assets : Amount vaultAsset)
    (ctx : Ctx) (w : World) :
    worldAfter (previewDeposit assets) ctx w = w :=
  worldAfter_eq_self (fun _ _ h => previewDeposit_success_world h)

private theorem previewRedeem_worldAfter (sharesIn : Amount vShare)
    (ctx : Ctx) (w : World) :
    worldAfter (previewRedeem sharesIn) ctx w = w :=
  worldAfter_eq_self (fun _ _ h => previewRedeem_success_world h)

theorem previewDeposit_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .previewDeposit := by
  intro assets ctx w _ _ hInvT
  rw [previewDeposit_worldAfter]
  exact hInvT

theorem previewRedeem_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .previewRedeem := by
  intro sharesIn ctx w _ _ hInvT
  rw [previewRedeem_worldAfter]
  exact hInvT

theorem vault_preserves_inv :
    PreservesInvAt spec (InvT self asset oracle) self :=
  PreservesInvAt.of_fns (C := spec) fun fn =>
    match fn with
    | .deposit => deposit_preserves_inv self asset oracle
    | .withdraw => withdraw_preserves_inv self asset oracle
    | .previewDeposit => previewDeposit_preserves_inv self asset oracle
    | .previewRedeem => previewRedeem_preserves_inv self asset oracle
    | .pause => pause_preserves_inv self asset oracle
    | .unpause => unpause_preserves_inv self asset oracle
    | .isPaused => isPaused_preserves_inv self asset oracle

/-! ### Claim monotonicity of well-formed calls (caller ≠ vault) -/

private theorem claim_le_deposit_run (assets : Amount vaultAsset)
    {ctx : Ctx} {w w' : World} {n : Amount vShare}
    {a : Address}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    claim self a w ≤ claim self a w' := by
  subst hself
  have hok := deposit_ok_of_run hrun
  obtain ⟨_, hσ, hor, _⟩ := deposit_post assets hok hrun
  obtain ⟨w1, htf, hself1, hor1, _, hext, _⟩ := deposit_call assets hok hrun
  have hhold := holdings_add_of_transferFrom ctx.self rfl hsne hT htf
  have hhold' : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, depositPost, hself1])
      (hor.trans hor1.symm) hext
  have hH' : holdings ctx.self w' = holdings ctx.self w + assets.raw := by
    rw [hhold', hhold]
  have hTA : holdings ctx.self w = hok.ta.raw :=
    viewBal?_some_holdings ctx.self hok.viewOk
  have hrate := rate_le_of_depositPost w.self ctx.sender a hok.ta assets
  rw [claim_eq_rate, claim_eq_rate, hσ, hH', hTA]
  exact hrate

private theorem claim_le_withdraw_run (sharesIn : Amount vShare)
    {ctx : Ctx} {w w' : World} {n : Amount vaultAsset}
    {a : Address}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hneA : ctx.sender ≠ a)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    claim self a w ≤ claim self a w' := by
  subst hself
  have hok := withdraw_ok_of_run hrun
  obtain ⟨hn, hσ, hor, _⟩ := withdraw_post sharesIn hok hrun
  obtain ⟨w1, htr, hself1, hor1, hext, _, _⟩ := withdraw_call sharesIn hok hrun
  subst hn
  set σ' := withdrawPost w.self ctx.sender sharesIn
  set amt := Amount.ofWord (redeemedAssets w.self.totalShares hok.ta sharesIn)
  have hhold := holdings_sub_of_transfer ctx.self rfl hsne hT
    (wCall := withdrawTailWorld w ctx.sender sharesIn)
    (by simp [withdrawTailWorld, σ', withdrawPost]) rfl rfl
    (by simpa [withdrawTailWorld, σ', amt] using htr)
  have hhold' : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, σ', hself1])
      (hor.trans hor1.symm) hext
  have hH' : holdings ctx.self w' + amt.raw = holdings ctx.self w := by
    rw [hhold', hhold]
  have hTA : holdings ctx.self w = hok.ta.raw :=
    viewBal?_some_holdings ctx.self hok.viewOk
  have hrate := rate_le_of_withdrawPost w.self ctx.sender a hok.ta sharesIn
    hneA hok.supply
  have hsub : holdings ctx.self w' =
      hok.ta.raw - redeemedAssets w.self.totalShares hok.ta sharesIn := by
    have : amt.raw = redeemedAssets w.self.totalShares hok.ta sharesIn :=
      Amount.raw_ofWord _
    rw [hTA] at hH'
    rw [this] at hH'
    exact Nat.eq_sub_of_add_eq hH'
  rw [claim_eq_rate, claim_eq_rate, hσ, hsub, hTA]
  exact hrate

private theorem claim_le_call (c : Call spec)
    (w : World) (a : Address)
    (hInvT : InvT self asset oracle w)
    (hs : c.sender ≠ self)
    (hna : ¬ Auth a c w) :
    claim self a w ≤ claim self a (step self (.call c) w) := by
  obtain ⟨hInv, ha, ho, hT⟩ := hInvT
  have hT' : IERC20.Spec (w.self.asset.impl : AssetImpl) := by
    simpa [IERC20.Ref.impl, ha] using hT
  rcases c with ⟨sender, value, ts, bn, fn, args⟩
  let ctx : Ctx :=
    { sender := sender, value := value, timestamp := ts,
      blockNumber := bn, self := self }
  have hself : ctx.self = self := rfl
  have hsne : ctx.sender ≠ self := hs
  have hp : spec.payable fn = false := rfl
  by_cases hv : value = 0
  · rw [step_eq_worldAfter_of_not_payable self
      ⟨sender, value, ts, bn, fn, args⟩ w hp hv]
    apply worldAfter_preserves (x := spec.exec fn args) (ctx := ctx)
      (P := fun w' => claim self a w ≤ claim self a w') (Nat.le_refl _)
    intro ret w' hrun
    match fn with
    | .deposit =>
      exact claim_le_deposit_run (self := self) args hself hsne hT' hrun
    | .withdraw =>
      have hneA : ctx.sender ≠ a := by
        intro heq
        exact hna (by simpa [Auth, AuthPred.ofSelf] using heq)
      exact claim_le_withdraw_run (self := self) args hself hsne hneA hT' hrun
    | .pause =>
      by_cases howner : ctx.sender = w.self.owner
      · have hok := pause_ok (ctx := ctx) (w := w) howner
        rw [hok] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact Nat.le_refl _
      · have herr := pause_only_owner (ctx := ctx) (w := w) howner
        rw [herr] at hrun
        cases hrun
    | .unpause =>
      by_cases howner : ctx.sender = w.self.owner
      · have hok := unpause_ok (ctx := ctx) (w := w) howner
        rw [hok] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact Nat.le_refl _
      · have herr := unpause_only_owner (ctx := ctx) (w := w) howner
        rw [herr] at hrun
        cases hrun
    | .isPaused =>
      have hok := isPaused_returns_stored (ctx := ctx) (w := w)
      rw [hok] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact Nat.le_refl _
    | .previewDeposit =>
      have hw := previewDeposit_success_world (ctx := ctx) (w := w)
        (assets := args) hrun
      subst hw; exact Nat.le_refl _
    | .previewRedeem =>
      have hw := previewRedeem_success_world (ctx := ctx) (w := w)
        (sharesIn := args) hrun
      subst hw; exact Nat.le_refl _
  · simp [step_reject_value (c :=
      ⟨sender, value, ts, bn, fn, args⟩) (w := w) hp hv]

end InvPreserve

namespace Proof

private theorem deployed_inv (self : Address) {w : World}
    (h : Deployed spec w) : Inv self w := by
  obtain ⟨_hpause, hts, hsh, _hT⟩ := h
  refine ⟨⟨∅, fun a _ => hsh a, ?_⟩, ?_⟩
  · simp [hts]
  · simp [hts]

private theorem deployed_invT (self : Address) {w : World}
    (h : Deployed spec w) :
    InvT self w.self.asset w.oracle w :=
  ⟨deployed_inv self h, rfl, rfl, h.2.2.2⟩

private theorem owed_le_of_inv (self : Address) (w : World)
    (h : Inv self w) : owedAt self w ≤ holdingsAt self w := by
  obtain ⟨_, hbd⟩ := h
  have hV : 0 < Word.scale offset.decimals :=
    Nat.pow_pos (by decide : 0 < 10)
  have hle := offset_claims_le (holdings self w) w.self.totalShares.raw
    (Word.scale offset.decimals) hV hbd
  simpa [owedAt, holdingsAt, holdings, Amount.le_iff, Shares.toAssetsRaw]
    using hle

theorem vault_inv_of_state (s : State) : Inv s.addr s.w := by
  obtain ⟨w0, tr, hDep, hW, hR, hw⟩ := s.reachable
  have hInvT :=
    inv_run_at (vault_preserves_inv s.addr w0.self.asset w0.oracle)
      (inv_rely s.addr w0.self.asset w0.oracle)
      (deployed_invT s.addr hDep) tr hW hR
  rw [hw]
  exact hInvT.1

theorem vault_solvent (s : State) : s.owed ≤ s.holdings :=
  owed_le_of_inv s.addr s.w (vault_inv_of_state s)

private theorem shares_withdrawPost (σ : Storage) (src : Address)
    (n : Amount vShare) (a : Address) (hn : n ≤ σ.shares src) :
    σ.shares a ≤ (withdrawPost σ src n).shares a +
      (if src = a then n else 0) := by
  have hn' : n.raw ≤ (σ.shares src).raw := (Amount.le_iff _ _).mp hn
  simp only [Amount.le_iff, Amount.raw_add, withdrawPost, Amount.raw_sub]
  by_cases h : a = src
  · subst h
    simp [Function.update]
    exact Nat.le_of_eq (Nat.sub_add_cancel hn').symm
  · simp [Function.update, h]

private theorem spent_covers_ok (self : Address) (c : Call spec)
    (w w' : World) (a : Address) {r : spec.Ret c.fn}
    (h : spec.exec c.fn c.args (c.toCtx self) w = .ok (r, w')) :
    w.self.shares a ≤ w'.self.shares a + spentCall a c := by
  revert r h
  rcases c with ⟨sender, value, ts, bn, fn, args⟩
  cases fn <;> intro r h
  case withdraw =>
    have hrun : Tx.run (withdraw args)
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_withdraw, Call.toCtx] using h
    have hok := withdraw_ok_of_run hrun
    have ⟨hn, hσ, _, _⟩ := withdraw_post args hok hrun
    subst hn
    simp [spentCall, hσ, Call.toCtx]
    exact shares_withdrawPost w.self sender args a hok.bal
  case deposit =>
    have hrun : Tx.run (deposit args)
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_deposit, Call.toCtx] using h
    have hok := deposit_ok_of_run hrun
    have ⟨hn, hσ, _, _⟩ := deposit_post args hok hrun
    subst hn
    simp [spentCall, hσ, depositPost]
    by_cases hwho : a = sender
    · subst hwho
      simp [Function.update, Amount.le_iff, Amount.raw_add]
    · simp [Function.update, hwho, Amount.le_iff]
  case pause =>
    have hrun : Tx.run pause
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_pause, Call.toCtx] using h
    by_cases howner : sender = w.self.owner
    · have hok := pause_ok
        (ctx := { sender, value, timestamp := ts, blockNumber := bn, self })
        (w := w) howner
      rw [hok] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      simp [spentCall]
    · have herr := pause_only_owner
        (ctx := { sender, value, timestamp := ts, blockNumber := bn, self })
        (w := w) howner
      rw [herr] at hrun
      cases hrun
  case unpause =>
    have hrun : Tx.run unpause
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_unpause, Call.toCtx] using h
    by_cases howner : sender = w.self.owner
    · have hok := unpause_ok
        (ctx := { sender, value, timestamp := ts, blockNumber := bn, self })
        (w := w) howner
      rw [hok] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      simp [spentCall]
    · have herr := unpause_only_owner
        (ctx := { sender, value, timestamp := ts, blockNumber := bn, self })
        (w := w) howner
      rw [herr] at hrun
      cases hrun
  case isPaused =>
    have hrun : Tx.run isPaused
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_isPaused, Call.toCtx] using h
    have hok := isPaused_returns_stored
      (ctx := { sender, value, timestamp := ts, blockNumber := bn, self })
      (w := w)
    rw [hok] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp [spentCall]
  case previewDeposit =>
    have hrun : Tx.run (previewDeposit args)
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_previewDeposit, Call.toCtx] using h
    have hw := previewDeposit_success_world (assets := args) hrun
    subst hw
    simp [spentCall]
  case previewRedeem =>
    have hrun : Tx.run (previewRedeem args)
        { sender, value, timestamp := ts, blockNumber := bn, self } w =
          .ok (r, w') := by
      simpa [Tx.run, spec_exec_previewRedeem, Call.toCtx] using h
    have hw := previewRedeem_success_world (sharesIn := args) hrun
    subst hw
    simp [spentCall]

private theorem spent_covers_accepted (self : Address) (c : Call spec)
    (w : World) (a : Address)
    (hacc : accepted self c w = true) :
    w.self.shares a ≤ (step self (.call c) w).self.shares a +
      spentCall a c := by
  obtain ⟨hvo, _, ⟨⟨r, w'⟩, hrun, hstep⟩⟩ := accepted_ok hacc
  have hv : c.value = 0 :=
    spec.value_eq_zero_of_valueOk (by cases c.fn <;> rfl) hvo
  rw [hv, World.creditValue_zero] at hrun
  rw [hstep]
  exact spent_covers_ok self c w w' a hrun

private theorem foldAccepted_raw_add {s : State} (t : Txs s) (a : Address)
    (x : Amount vShare) :
    (t.foldAccepted (fun acc c _ => acc + HasSpent.spentCall (C := spec) a c)
      x).raw =
      x.raw + (Txs.spent t a).raw := by
  induction t generalizing x with
  | nil => simp [Txs.foldAccepted, Txs.spent, Amount.raw_add]
  | @call s c hne rest ih =>
    simp [Txs.foldAccepted, Txs.spent]
    split_ifs
    · have hx := ih (x + HasSpent.spentCall (C := spec) a (c))
      have hsc := ih (HasSpent.spentCall (C := spec) a (c))
      rw [hx, hsc]
      simp [Amount.raw_add]
      ac_rfl
    · exact ih x
  | @env s x' hr rest ih =>
    simpa [Txs.spent, Txs.foldAccepted] using ih x

theorem vault_no_unauthorized_extraction (s : State) (t : Txs s)
    (a : Address) :
    s.self.shares a ≤ t.end.self.shares a + t.spent a := by
  induction t with
  | nil =>
    simp [Txs.end, Txs.spent, Amount.le_iff, Amount.raw_add]
  | @call s c hne rest ih =>
    by_cases hacc : accepted s.addr c s.w = true
    · have hcov := spent_covers_accepted s.addr c s.w a hacc
      have hstepEq : (s.afterCall c hne).w = step s.addr (.call c) s.w :=
        State.afterCall_w s c hne
      have hthis : s.self.shares a ≤
          (s.afterCall c hne).self.shares a + spentCall a c := by
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

end Vault
