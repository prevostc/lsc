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
def InvT (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (w : World Storage ExtState Event) : Prop :=
  Inv self w ∧ w.self.asset = asset ∧ w.oracle = oracle ∧
    IERC20.Spec (asset.impl w :
      IERC20.Impl vaultAsset (World Storage ExtState Event) Error)

/-! ### Environment -/

theorem inv_rely (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) :
    PreservesInvEnv spec (InvT self asset oracle)
      (vaultRely self asset oracle) := by
  intro w x' ⟨⟨hta, hinv⟩, ha, ho, hT⟩ ⟨hbal, _hsup⟩
  refine ⟨⟨?_, hinv⟩, ha, ho, ?_⟩
  · rw [holdings_view, ha, ho] at hta ⊢
    exact Nat.le_trans hta hbal
  · simpa [IERC20.Ref.impl] using hT

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
    (assets : Amount vaultAsset) (hInv : InvStorage σ) :
    InvStorage (depositPost σ who assets) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  by_cases ht : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ who := by intro h; subst h; exact ha ht
      simp [depositPost, Function.update_of_ne hne]
      exact h0 a ha
    · have hsum' :
          H.sum (rawShares (depositPost σ who assets).shares) =
            H.sum (rawShares σ.shares) + mintedShares σ assets := by
        simp only [depositPost, rawShares_update, Amount.raw_add, Amount.raw_ofWord]
        exact nat_sum_update_add H (rawShares σ.shares) ht
          (mintedShares σ assets)
      change H.sum (rawShares (depositPost σ who assets).shares) =
        (depositPost σ who assets).totalShares.raw
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
              (σ.shares who + Amount.ofWord (mintedShares σ assets)) x).raw) =
            Function.update (rawShares σ.shares) who
              ((σ.shares who).raw + mintedShares σ assets) := by
        funext x
        by_cases hx : x = who <;>
          simp [rawShares, Function.update, hx, Amount.raw_add, Amount.raw_ofWord]
      have hframe :=
        sum_update_not_mem H (rawShares σ.shares) ht
          ((σ.shares who).raw + mintedShares σ assets)
      have hframe' :
          H.sum (Function.update (rawShares σ.shares) who (mintedShares σ assets)) =
            H.sum (rawShares σ.shares) := by
        simpa [hwho0] using hframe
      have hsum' :
          (∑ a ∈ insert who H, rawShares (depositPost σ who assets).shares a) =
            H.sum (rawShares σ.shares) + mintedShares σ assets := by
        rw [Finset.sum_insert ht]
        simp only [depositPost, Function.update_self, rawShares, Amount.raw_add,
          Amount.raw_ofWord]
        simp [hupd, hframe', hwho0, Nat.add_comm]
      change (∑ a ∈ insert who H, ((depositPost σ who assets).shares a).raw) =
        (depositPost σ who assets).totalShares.raw
      rw [hsum', hsumr]
      simp [depositPost, Amount.raw_add, Amount.raw_ofWord, Nat.add_comm]

private theorem invStorage_of_withdrawPost (σ : Storage) (who : Address)
    (sharesIn : Amount vShare) (assetsOut : Nat)
    (hInv : InvStorage σ) (hn : sharesIn ≤ σ.shares who) :
    InvStorage (withdrawPost σ who sharesIn assetsOut) := by
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
          H.sum (rawShares (withdrawPost σ who sharesIn assetsOut).shares) =
            H.sum (rawShares σ.shares) - sharesIn.raw := by
        simp only [withdrawPost, rawShares_update, Amount.raw_sub]
        exact nat_sum_update_sub H (rawShares σ.shares) hs hn'
      change H.sum (rawShares (withdrawPost σ who sharesIn assetsOut).shares) =
        (withdrawPost σ who sharesIn assetsOut).totalShares.raw
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

/-- Deposit never decreases `claim`, even for the depositor: minting rounds against them,
so the exchange rate does not fall, and their share count does not fall. -/
private theorem claim_le_of_depositPost (σ : Storage) (who a : Address)
    (assets : Amount vaultAsset) :
    claim a σ ≤ claim a (depositPost σ who assets) := by
  by_cases hts : σ.totalShares = 0
  · simp [claim, hts]
  · have htsr : σ.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    have hTS : 0 < σ.totalShares.raw := Nat.pos_of_ne_zero htsr
    have hm :
        mintedShares σ assets =
          assets.raw * σ.totalShares.raw / σ.totalAssets.raw := by
      simp [mintedShares, htsr, Nat.mul_comm]
    have hts' : (depositPost σ who assets).totalShares ≠ 0 := by
      intro hz
      have hzraw : (depositPost σ who assets).totalShares.raw = 0 :=
        (Amount.eq_iff _ _).mp hz
      simp [depositPost, Amount.raw_add, Amount.raw_ofWord, mintedShares] at hzraw
      exact htsr hzraw.1
    rw [claim, if_neg hts, claim, if_neg hts']
    by_cases ha : a = who
    · subst ha
      simp only [depositPost, Function.update_self, Amount.raw_add, Amount.raw_ofWord, hm]
      refine Nat.le_trans
        (deposit_rate_nondecreasing σ.totalAssets.raw σ.totalShares.raw
          (σ.shares a).raw assets.raw hTS) ?_
      rw [Nat.add_comm σ.totalShares.raw]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _
        (Nat.le_add_right (σ.shares a).raw
          (assets.raw * σ.totalShares.raw / σ.totalAssets.raw)))
    · simp only [depositPost, Function.update_of_ne ha, Amount.raw_add, Amount.raw_ofWord, hm]
      convert deposit_rate_nondecreasing σ.totalAssets.raw σ.totalShares.raw
        (σ.shares a).raw assets.raw hTS using 2

/-- Another account's withdraw does not decrease `claim a`. The `TS' = 0` case uses
`InvStorage` to force `shares a = 0`. -/
private theorem claim_le_of_withdrawPost (σ : Storage) (who a : Address)
    (sharesIn : Amount vShare)
    (hInv : InvStorage σ) (hne : who ≠ a)
    (hbal : sharesIn ≤ σ.shares who)
    (hden : σ.totalShares.raw ≠ 0)
    (hsup : sharesIn ≤ σ.totalShares) :
    claim a σ ≤
      claim a (withdrawPost σ who sharesIn (redeemedAssets σ sharesIn)) := by
  have htsσ : σ.totalShares ≠ 0 := (Amount.ne_iff _ _).mpr hden
  by_cases hts' : (σ.totalShares - sharesIn).raw = 0
  · have hs_eq : sharesIn.raw = σ.totalShares.raw :=
      Nat.le_antisymm ((Amount.le_iff _ _).mp hsup)
        (Nat.sub_eq_zero_iff_le.mp hts')
    have hall : σ.totalShares ≤ σ.shares who :=
      (Amount.le_iff _ _).mpr (hs_eq ▸ (Amount.le_iff _ _).mp hbal)
    have ha0 := invStorage_bystander_zero σ who a hInv hne hall
    have hpost0 :
        (withdrawPost σ who sharesIn (redeemedAssets σ sharesIn)).totalShares = 0 :=
      Amount.ext (by simpa [withdrawPost, Amount.raw_sub] using hts')
    rw [claim, if_neg htsσ, claim, if_pos hpost0]
    simp [ha0, Amount.raw_zero]
  · have hs_ne : sharesIn.raw ≠ σ.totalShares.raw := by
      intro heq; exact hts' (by simp [Amount.raw_sub, heq])
    have hs_lt : sharesIn.raw < σ.totalShares.raw :=
      Nat.lt_of_le_of_ne ((Amount.le_iff _ _).mp hsup) hs_ne
    have hTS : 0 < σ.totalShares.raw := Nat.pos_of_ne_zero hden
    have hpost_ne :
        (withdrawPost σ who sharesIn (redeemedAssets σ sharesIn)).totalShares ≠ 0 :=
      (Amount.ne_iff _ _).mpr (by simpa [withdrawPost, Amount.raw_sub] using hts')
    rw [claim, if_neg htsσ, claim, if_neg hpost_ne]
    simp [withdrawPost, Function.update_of_ne hne.symm, Amount.raw_sub, redeemedAssets]
    convert withdraw_rate_nondecreasing σ.totalAssets.raw σ.totalShares.raw
      (σ.shares a).raw sharesIn.raw hTS hs_lt using 1
    simp [Nat.mul_comm]


theorem inv_solvent (self : Address) (w : World Storage ExtState Event)
    (h : Inv self w) :
    Solvent claim holdings self w := by
  obtain ⟨hta, H, h0, hs⟩ := h
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
          H.sum (fun a => claim a w.self) =
            H.sum (fun a => (w.self.shares a).raw * w.self.totalAssets.raw /
              w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl
        intro a _; simp [claim, hts]
      have hle :=
        sum_mul_div_le H (fun a => (w.self.shares a).raw) w.self.totalAssets.raw
          w.self.totalShares.raw hs hpos
      rw [hcl]
      exact Nat.le_trans hle hta

private theorem holdings_add_of_transferFrom
    (self : Address) {ctx : Ctx} {w w1 : World Storage ExtState Event}
    {assets : Amount vaultAsset}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.asset.impl w :
      IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (hcall : Tx.run (tfCall w.self.asset ctx.sender ctx.self assets) ctx w =
      .ok (true, w1)) :
    holdings self w1 = holdings self w + assets.raw := by
  subst hself
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w) (w' := w1)
    (by simpa [impl_transferFrom] using hcall)
  have hdst := hmoves.2.1 hsne
  have hframe := transferFrom_frame (by simpa [tfCall] using hcall)
  simpa [holdings, IERC20.Ref.impl, Amount.raw_add, hframe.1, hframe.2.1] using
    congrArg Amount.raw hdst

private theorem holdings_sub_of_transfer
    (self : Address) {ctx : Ctx} {w wCall w1 : World Storage ExtState Event}
    {amt : Amount vaultAsset}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.asset.impl w :
      IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (ha : wCall.self.asset = w.self.asset) (ho : wCall.oracle = w.oracle)
    (hx : wCall.ext = w.ext)
    (hcall : Tx.run (trCall w.self.asset ctx.sender amt) ctx wCall =
      .ok (true, w1)) :
    holdings self w1 + amt.raw = holdings self w := by
  subst hself
  have hTcall : IERC20.Spec
      (wCall.self.asset.impl wCall :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error) := by
    simpa [IERC20.Ref.impl, ha] using hT
  have hrunT :
      (wCall.self.asset.impl wCall :
          IERC20.Impl vaultAsset (World Storage ExtState Event) Error).transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall =
        .ok (true, w1) := by
    have htr' :
        Tx.run (trCall w.self.asset ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := w.self.asset) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      simpa using hcall
    simpa [impl_transfer, ha] using htr'
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
  unfold holdings
  rw [hs]
  dsimp only
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

/-! ### Invariant preservation -/

variable (self : Address) (asset : IERC20.Ref vaultAsset) (oracle : Oracle ExtState)

theorem deposit_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .deposit :=
  PreservesInvFnAt_of_ok fun assets ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨hta, hst⟩, ha, ho, hT⟩ := hInvT
    have hok := deposit_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := deposit_post assets hok hrun
    obtain ⟨w1, htf, hself1, hor1, _, hext, _⟩ := deposit_call assets hok hrun
    have hT' : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error) := by
      simpa [IERC20.Ref.impl, ha] using hT
    have hhold := holdings_add_of_transferFrom self hself hsne hT' htf
    have hhold' : holdings self w' = holdings self w1 :=
      holdings_congr self (by simp [hσ, depositPost, hself1])
        (hor.trans hor1.symm) hext
    refine ⟨⟨?_, hσ ▸ invStorage_of_depositPost w.self ctx.sender assets hst⟩,
        ?_, ?_, ?_⟩
    · rw [hσ]
      change (w.self.totalAssets + assets).raw ≤ holdings self w'
      rw [Amount.raw_add, hhold', hhold]
      exact Nat.add_le_add_right hta _
    · simpa [hσ, depositPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, depositPost, ha] using hT

theorem withdraw_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .withdraw :=
  PreservesInvFnAt_of_ok fun sharesIn ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨hta, hst⟩, ha, ho, hT⟩ := hInvT
    have hok := withdraw_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := withdraw_post sharesIn hok hrun
    obtain ⟨w1, htr, hself1, hor1, hext, _, _⟩ := withdraw_call sharesIn hok hrun
    have hT' : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error) := by
      simpa [IERC20.Ref.impl, ha] using hT
    set σ' := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
    set amt := Amount.ofWord (redeemedAssets w.self sharesIn)
    have hhold := holdings_sub_of_transfer self hself hsne hT'
      (wCall := { w with self := σ' })
      (by simp [σ', withdrawPost]) rfl rfl (by simpa [σ', amt] using htr)
    have hhold' : holdings self w' = holdings self w1 :=
      holdings_congr self (by simp [hσ, σ', hself1])
        (hor.trans hor1.symm) hext
    refine ⟨⟨?_, hσ ▸ invStorage_of_withdrawPost w.self ctx.sender sharesIn
        (redeemedAssets w.self sharesIn) hst hok.bal⟩, ?_, ?_, ?_⟩
    · have hle : amt.raw ≤ w.self.totalAssets.raw := hok.assetsFit
      rw [hσ]
      change (w.self.totalAssets - amt).raw ≤ holdings self w'
      rw [Amount.raw_sub, hhold']
      have hholdN : holdings self w1 = holdings self w - amt.raw :=
        Nat.eq_sub_of_add_eq hhold
      rw [hholdN]
      exact Nat.sub_le_sub_right hta _
    · simpa [hσ, σ', withdrawPost] using ha
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, σ', withdrawPost, ha] using hT

theorem pause_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .pause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := pause_ok howner
    simp [worldAfter, hrun]
    obtain ⟨hta, H, h0, hs⟩ := hInv
    exact ⟨⟨hta, ⟨H, h0, hs⟩⟩, ha, ho, hT⟩
  · have hrun := pause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem unpause_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .unpause := by
  intro u ctx w _ _ hInvT
  by_cases howner : ctx.sender = w.self.owner
  · obtain ⟨hInv, ha, ho, hT⟩ := hInvT
    have hrun := unpause_ok howner
    simp [worldAfter, hrun]
    obtain ⟨hta, H, h0, hs⟩ := hInv
    exact ⟨⟨hta, ⟨H, h0, hs⟩⟩, ha, ho, hT⟩
  · have hrun := unpause_only_owner howner
    simp [worldAfter, hrun]; exact hInvT

theorem isPaused_preserves_inv :
    PreservesInvFnAt spec (InvT self asset oracle) self .isPaused := by
  intro u ctx w _ _ hInvT
  unfold worldAfter
  rw [isPaused_returns_stored]
  exact hInvT

private theorem previewDeposit_worldAfter (assets : Amount vaultAsset)
    (ctx : Ctx) (w : World Storage ExtState Event) :
    worldAfter (previewDeposit assets) ctx w = w := by
  apply worldAfter_eq_self
  intro _ w' hrun
  simp [previewDeposit, Amount.hMulDivDown_def, Amount.run_mulDivDown] at hrun
  by_cases hts : w.self.totalShares = 0
  · simp [hts] at hrun
    split_ifs at hrun
    all_goals try cases hrun
    all_goals try rfl
  · simp [hts] at hrun
    split_ifs at hrun
    all_goals try cases hrun
    all_goals try rfl

private theorem previewRedeem_worldAfter (sharesIn : Amount vShare)
    (ctx : Ctx) (w : World Storage ExtState Event) :
    worldAfter (previewRedeem sharesIn) ctx w = w := by
  apply worldAfter_eq_self
  intro _ w' hrun
  simp [previewRedeem, Amount.hMulDivDown_def, Amount.run_mulDivDown] at hrun
  split_ifs at hrun
  all_goals try cases hrun
  all_goals try rfl

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
  PreservesInvAt.of_fns fun fn =>
    match fn with
    | .deposit => deposit_preserves_inv self asset oracle
    | .withdraw => withdraw_preserves_inv self asset oracle
    | .previewDeposit => previewDeposit_preserves_inv self asset oracle
    | .previewRedeem => previewRedeem_preserves_inv self asset oracle
    | .pause => pause_preserves_inv self asset oracle
    | .unpause => unpause_preserves_inv self asset oracle
    | .isPaused => isPaused_preserves_inv self asset oracle

/-! ### Authorization -/

theorem deposit_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .deposit :=
  NoUnauthorizedDecreaseFn_of_ok fun assets ctx w a n w' _hInvT hrun hdec => by
    have hok := deposit_ok_of_run hrun
    obtain ⟨_, hσ, _, _⟩ := deposit_post assets hok hrun
    exact Nat.not_lt.mpr (hσ ▸ claim_le_of_depositPost w.self ctx.sender a assets) hdec

theorem withdraw_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .withdraw :=
  NoUnauthorizedDecreaseFn_of_ok fun sharesIn ctx w a n w' hInvT hrun hdec => by
    change ctx.sender = a
    by_cases hs : ctx.sender = a
    · exact hs
    · obtain ⟨⟨_, hst⟩, _, _, _⟩ := hInvT
      have hok := withdraw_ok_of_run hrun
      obtain ⟨_, hσ, _, _⟩ := withdraw_post sharesIn hok hrun
      exact (Nat.not_lt.mpr (hσ ▸ claim_le_of_withdrawPost w.self ctx.sender a
        sharesIn hst hs hok.bal hok.denom hok.supply) hdec).elim

theorem pause_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .pause := by
  intro u ctx w a _hInvT hdec
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := pause_ok howner
    simp [worldAfter, hrun] at hdec
    simp [claim] at hdec
  · have hrun := pause_only_owner howner
    simp [worldAfter, hrun] at hdec

theorem unpause_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .unpause := by
  intro u ctx w a _hInvT hdec
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := unpause_ok howner
    simp [worldAfter, hrun] at hdec
    simp [claim] at hdec
  · have hrun := unpause_only_owner howner
    simp [worldAfter, hrun] at hdec

theorem isPaused_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .isPaused := by
  intro u ctx w a _hInvT hdec
  unfold worldAfter at hdec
  rw [isPaused_returns_stored] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem previewDeposit_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .previewDeposit := by
  intro assets ctx w a _hInvT hdec
  rw [previewDeposit_worldAfter] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem previewRedeem_auth :
    NoUnauthorizedDecreaseFn spec (InvT self asset oracle) claim Auth .previewRedeem := by
  intro sharesIn ctx w a _hInvT hdec
  rw [previewRedeem_worldAfter] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem vault_no_unauth :
    NoUnauthorizedDecrease spec (InvT self asset oracle) claim Auth :=
  NoUnauthorizedDecrease.of_fns fun fn =>
    match fn with
    | .deposit => deposit_auth self asset oracle
    | .withdraw => withdraw_auth self asset oracle
    | .previewDeposit => previewDeposit_auth self asset oracle
    | .previewRedeem => previewRedeem_auth self asset oracle
    | .pause => pause_auth self asset oracle
    | .unpause => unpause_auth self asset oracle
    | .isPaused => isPaused_auth self asset oracle

namespace Proof

theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage ExtState Event)
    (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  solvent_run_at
    (vault_preserves_inv self w.self.asset w.oracle)
    (inv_rely self w.self.asset w.oracle)
    (fun w' hw' => inv_solvent self w' hw'.1)
    ⟨h, rfl, rfl, hT⟩ tr hW hR

theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at
    (vault_no_unauth self w.self.asset w.oracle)
    (vault_preserves_inv self w.self.asset w.oracle)
    (inv_rely self w.self.asset w.oracle)
    tr w a ⟨hw, rfl, rfl, hT⟩ hW hR hA

end Proof

end Vault
