import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Examples.Vault.Spec
import Examples.Vault.Proofs.Tx

set_option linter.unusedSimpArgs false

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-!
Security obligations for the vault. `InvT` locks the bound asset, the oracle,
and `IERC20.Spec`. Well-formed traces use `PreservesInvFnAt`
(`ctx.self = self`, `ctx.sender ≠ self`).
-/

/-- Invariant plus the callee promise, pinned to the starting asset/oracle. -/
def InvT (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (w : World Storage ExtState Event) : Prop :=
  Inv w ∧ w.self.asset = asset ∧ w.oracle = oracle ∧
    IERC20.Spec (asset.impl : AssetImpl)

/-! ### Environment -/

theorem inv_rely (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) :
    PreservesInvEnv spec (InvT asset oracle)
      (vaultRely self asset oracle) := by
  intro w x' ⟨hinv, ha, ho, hT⟩ ⟨_hbal, _hsup⟩
  exact ⟨hinv, ha, ho, by simpa [IERC20.Ref.impl] using hT⟩

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

/-- Pro-rata redeemable assets of `a` against holdings `TA`. -/
private def rate (σ : Storage) (TA : Nat) (a : Address) : Nat :=
  if σ.totalShares = 0 then 0
  else (σ.shares a).raw * TA / σ.totalShares.raw

private theorem claim_eq_rate (self a : Address)
    (w : World Storage ExtState Event) :
    claim self a w = rate w.self (holdings self w) a :=
  rfl

/-- Deposit never decreases a pro-rata claim when holdings rise by `assets`. -/
private theorem rate_le_of_depositPost (σ : Storage) (who a : Address)
    (ta assets : Amount vaultAsset)
    (hprod : σ.totalShares.raw = 0 ∨ ta.raw ≠ 0) :
    let m := mintedShares σ.totalShares ta assets
    rate σ ta.raw a ≤
      rate (depositPost σ who m) (ta.raw + assets.raw) a := by
  set m := mintedShares σ.totalShares ta assets
  by_cases hts : σ.totalShares = 0
  · simp [rate, hts]
  · have htsr : σ.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    have hTA : ta.raw ≠ 0 := by
      rcases hprod with h0 | hta
      · exact (htsr h0).elim
      · exact hta
    have hTS : 0 < σ.totalShares.raw := Nat.pos_of_ne_zero htsr
    have hm : m = σ.totalShares.raw * assets.raw / ta.raw := by
      simp [m, mintedShares, htsr]
    have hts' : (depositPost σ who m).totalShares ≠ 0 := by
      intro hz
      have hzraw : (depositPost σ who m).totalShares.raw = 0 :=
        (Amount.eq_iff _ _).mp hz
      simp [depositPost, Amount.raw_add, Amount.raw_ofWord, m, mintedShares] at hzraw
      exact htsr hzraw.1
    dsimp [rate]
    rw [if_neg hts, if_neg hts']
    have hm' : m = assets.raw * σ.totalShares.raw / ta.raw := by
      rw [hm, Nat.mul_comm]
    by_cases ha : a = who
    · subst ha
      simp only [depositPost, Function.update_self, Amount.raw_add, Amount.raw_ofWord, hm']
      refine Nat.le_trans
        (deposit_rate_nondecreasing ta.raw σ.totalShares.raw
          (σ.shares a).raw assets.raw hTS) ?_
      rw [Nat.add_comm σ.totalShares.raw]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _
        (Nat.le_add_right (σ.shares a).raw
          (assets.raw * σ.totalShares.raw / ta.raw)))
    · simp only [depositPost, Function.update_of_ne ha, Amount.raw_add,
        Amount.raw_ofWord, hm']
      convert deposit_rate_nondecreasing ta.raw σ.totalShares.raw
        (σ.shares a).raw assets.raw hTS using 2

/-- Another account's withdraw does not decrease a pro-rata claim. -/
private theorem rate_le_of_withdrawPost (σ : Storage) (who a : Address)
    (ta : Amount vaultAsset) (sharesIn : Amount vShare)
    (hInv : InvStorage σ) (hne : who ≠ a)
    (hbal : sharesIn ≤ σ.shares who)
    (hden : σ.totalShares.raw ≠ 0)
    (hsup : sharesIn ≤ σ.totalShares) :
    rate σ ta.raw a ≤
      rate (withdrawPost σ who sharesIn)
        (ta.raw - redeemedAssets σ.totalShares ta sharesIn) a := by
  have htsσ : σ.totalShares ≠ 0 := (Amount.ne_iff _ _).mpr hden
  by_cases hts' : (σ.totalShares - sharesIn).raw = 0
  · have hs_eq : sharesIn.raw = σ.totalShares.raw :=
      Nat.le_antisymm ((Amount.le_iff _ _).mp hsup)
        (Nat.sub_eq_zero_iff_le.mp hts')
    have hall : σ.totalShares ≤ σ.shares who :=
      (Amount.le_iff _ _).mpr (hs_eq ▸ (Amount.le_iff _ _).mp hbal)
    have ha0 := invStorage_bystander_zero σ who a hInv hne hall
    have hpost0 : (withdrawPost σ who sharesIn).totalShares = 0 :=
      Amount.ext (by simpa [withdrawPost, Amount.raw_sub] using hts')
    dsimp [rate]
    rw [if_neg htsσ, if_pos hpost0]
    simp [ha0, Amount.raw_zero]
  · have hs_ne : sharesIn.raw ≠ σ.totalShares.raw := by
      intro heq; exact hts' (by simp [Amount.raw_sub, heq])
    have hs_lt : sharesIn.raw < σ.totalShares.raw :=
      Nat.lt_of_le_of_ne ((Amount.le_iff _ _).mp hsup) hs_ne
    have hTS : 0 < σ.totalShares.raw := Nat.pos_of_ne_zero hden
    have hpost_ne : (withdrawPost σ who sharesIn).totalShares ≠ 0 :=
      (Amount.ne_iff _ _).mpr (by simpa [withdrawPost, Amount.raw_sub] using hts')
    dsimp [rate]
    rw [if_neg htsσ, if_neg hpost_ne]
    simp [withdrawPost, Function.update_of_ne hne.symm, Amount.raw_sub,
      redeemedAssets]
    convert withdraw_rate_nondecreasing ta.raw σ.totalShares.raw
      (σ.shares a).raw sharesIn.raw hTS hs_lt using 1
    simp [Nat.mul_comm]

theorem inv_solvent (self : Address) (w : World Storage ExtState Event)
    (h : Inv w) :
    Solvent (claim self) holdings self w := by
  obtain ⟨H, h0, hs⟩ := h
  by_cases hts : w.self.totalShares = 0
  · refine ⟨H, ?_, ?_⟩
    · intro a ha; simp [claim, hts]
    · simp [claim, hts]
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hs0 := h0 a ha
      simp [claim, hts, hs0, Amount.raw_zero]
    · have htsr : w.self.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
      have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero htsr
      have hcl :
          H.sum (fun a => claim self a w) =
            H.sum (fun a => (w.self.shares a).raw * holdings self w /
              w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl
        intro a _; simp [claim, hts]
      have hle :=
        sum_mul_div_le H (fun a => (w.self.shares a).raw) (holdings self w)
          w.self.totalShares.raw hs hpos
      rw [hcl]
      exact hle

private theorem holdings_add_of_transferFrom
    (self : Address) {ctx : Ctx} {w w1 : World Storage ExtState Event}
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
  simpa [holdings, IERC20.Ref.impl, Amount.raw_add, hframe.1, hframe.2.1,
    World.view] using
    congrArg Amount.raw hdst

private theorem holdings_sub_of_transfer
    (self : Address) {ctx : Ctx} {w wCall w1 : World Storage ExtState Event}
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
  simp [holdings, hs] at hsumr htor ⊢
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

private theorem claim_le_of_rely (self : Address)
    (asset : IERC20.Ref vaultAsset) (oracle : Oracle ExtState)
    (w : World Storage ExtState Event) (x' : ExtState) (a : Address)
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
  split_ifs
  · exact Nat.le_refl _
  · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hbal)

/-! ### Invariant preservation -/

variable (self : Address) (asset : IERC20.Ref vaultAsset) (oracle : Oracle ExtState)

theorem deposit_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .deposit :=
  PreservesInvFnAt_of_ok fun assets ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨hst, ha, ho, hT⟩ := hInvT
    have hok := deposit_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := deposit_post assets hok hrun
    obtain ⟨w1, htf, hself1, hor1, _, hext, _⟩ := deposit_call assets hok hrun
    have hT' : IERC20.Spec (w.self.asset.impl : AssetImpl) := by
      simpa [IERC20.Ref.impl, ha] using hT
    refine ⟨by
        simp [Inv, hσ]
        exact invStorage_of_depositPost w.self ctx.sender
          (mintedShares w.self.totalShares hok.ta assets) hst,
      ?_, ?_, ?_⟩
    · simpa [hσ, depositPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, depositPost, ha] using hT

theorem withdraw_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .withdraw :=
  PreservesInvFnAt_of_ok fun sharesIn ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨hst, ha, ho, hT⟩ := hInvT
    have hok := withdraw_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := withdraw_post sharesIn hok hrun
    refine ⟨by
        simp [Inv, hσ]
        exact invStorage_of_withdrawPost w.self ctx.sender sharesIn hst hok.bal,
      ?_, ?_, ?_⟩
    · simpa [hσ, withdrawPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, withdrawPost, ha] using hT

theorem pause_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .pause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := pause_ok howner
    simp [worldAfter, hrun]
    exact ⟨hInv, ha, ho, hT⟩
  · have hrun := pause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem unpause_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .unpause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := unpause_ok howner
    simp [worldAfter, hrun]
    exact ⟨hInv, ha, ho, hT⟩
  · have hrun := unpause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem isPaused_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .isPaused := by
  intro u ctx w _ _ hInvT
  unfold worldAfter
  rw [isPaused_returns_stored]
  exact hInvT

private theorem previewDeposit_worldAfter (assets : Amount vaultAsset)
    (ctx : Ctx) (w : World Storage ExtState Event) :
    worldAfter (previewDeposit assets) ctx w = w :=
  worldAfter_eq_self (fun _ _ h => previewDeposit_success_world h)

private theorem previewRedeem_worldAfter (sharesIn : Amount vShare)
    (ctx : Ctx) (w : World Storage ExtState Event) :
    worldAfter (previewRedeem sharesIn) ctx w = w :=
  worldAfter_eq_self (fun _ _ h => previewRedeem_success_world h)

theorem previewDeposit_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .previewDeposit := by
  intro assets ctx w _ _ hInvT
  rw [previewDeposit_worldAfter]
  exact hInvT

theorem previewRedeem_preserves_inv :
    PreservesInvFnAt spec (InvT asset oracle) self .previewRedeem := by
  intro sharesIn ctx w _ _ hInvT
  rw [previewRedeem_worldAfter]
  exact hInvT

theorem vault_preserves_inv :
    PreservesInvAt spec (InvT asset oracle) self :=
  PreservesInvAt.of_fns fun fn =>
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
    {ctx : Ctx} {w w' : World Storage ExtState Event} {n : Amount vShare}
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
  have hprod : w.self.totalShares.raw = 0 ∨ hok.ta.raw ≠ 0 := by
    rcases hok.prod with h0 | ⟨hta, _⟩
    · exact Or.inl h0
    · exact Or.inr hta
  have hrate := rate_le_of_depositPost w.self ctx.sender a hok.ta assets hprod
  rw [claim_eq_rate, claim_eq_rate, hσ, hH', hTA]
  exact hrate

private theorem claim_le_withdraw_run (sharesIn : Amount vShare)
    {ctx : Ctx} {w w' : World Storage ExtState Event} {n : Amount vaultAsset}
    {a : Address}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hneA : ctx.sender ≠ a)
    (hInv : Inv w)
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
    hInv hneA hok.bal hok.denom hok.supply
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
    (w : World Storage ExtState Event) (a : Address)
    (hInvT : InvT asset oracle w)
    (ht : c.target = self) (hs : c.sender ≠ self)
    (hna : ¬ Auth a c w) :
    claim self a w ≤ claim self a (step (.call c) w) := by
  obtain ⟨hInv, ha, ho, hT⟩ := hInvT
  have hT' : IERC20.Spec (w.self.asset.impl : AssetImpl) := by
    simpa [IERC20.Ref.impl, ha] using hT
  rcases c with ⟨sender, value, ts, bn, target, fn, args⟩
  let ctx : Ctx :=
    { sender := sender, value := value, timestamp := ts,
      blockNumber := bn, self := target }
  have hself : ctx.self = self := ht
  have hsne : ctx.sender ≠ self := hs
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
    exact claim_le_withdraw_run (self := self) args hself hsne hneA hInv hT' hrun
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

namespace Proof

theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage ExtState Event)
    (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (h : Inv w) :
    Solvent (claim self) holdings self (run tr w) :=
  solvent_run_at
    (vault_preserves_inv self w.self.asset w.oracle)
    (inv_rely self w.self.asset w.oracle)
    (fun w' hw' => inv_solvent self w' hw'.1)
    ⟨h, rfl, rfl, hT⟩ tr hW hR

theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hA : NoAuthAlong Auth a tr w) :
    claim self a w ≤ claim self a (run tr w) := by
  let asset := w.self.asset
  let oracle := w.oracle
  have go : ∀ (tr : List (Step spec)) (w' : World Storage ExtState Event),
      InvT asset oracle w' →
      Wf self tr →
      RelyAlong (vaultRely self asset oracle) tr w' →
      NoAuthAlong Auth a tr w' →
      claim self a w' ≤ claim self a (run tr w') := by
    intro tr w'
    induction tr generalizing w' with
    | nil =>
      intro _ _ _ _
      simp [run]
    | cons s rest ih =>
      intro hw' hW hR hA
      match s with
      | .env x' =>
        obtain ⟨hr, htl⟩ := hR
        have hle := claim_le_of_rely self asset oracle w' x' a hw'.2.1 hw'.2.2.1 hr
        have hw'' := inv_rely self asset oracle w' x' hw' hr
        exact Nat.le_trans hle (ih { w' with ext := x' } hw'' hW htl hA)
      | .call c =>
        obtain ⟨hna, htl⟩ := hA
        obtain ⟨ht, hs, hWtl⟩ := hW
        have hw'' := vault_preserves_inv self asset oracle c w' ht hs hw'
        have hle := claim_le_call self asset oracle c w' a hw' ht hs hna
        exact Nat.le_trans hle (ih (step (.call c) w') hw'' hWtl hR htl)
  exact go tr w ⟨hw, rfl, rfl, hT⟩ hW hR hA

end Proof

end Vault
