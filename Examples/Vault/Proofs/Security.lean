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
Security obligations for the vault. `Inv` is indexed by the vault address because
`holdings` reads `ext.asset.balances self`. Well-formed traces use
`PreservesInvFnAt` (`ctx.self = self`, `ctx.sender ≠ self`).
-/

/-! ### Environment -/

theorem inv_rely (self : Address) :
    PreservesInvEnv spec (Inv self) (vaultRely self) := by
  intro w x' ⟨hta, hinv⟩ ⟨hbal, _hdec⟩
  refine ⟨?_, hinv⟩
  simp [holdings] at hta ⊢
  exact Nat.le_trans hta hbal

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
        convert nat_sum_update_add H (rawShares σ.shares) ht (mintedShares σ assets) using 1
        simp [rawShares, Nat.add_comm]
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
              (Amount.ofWord (mintedShares σ assets) + σ.shares who) x).raw) =
            Function.update (rawShares σ.shares) who
              (mintedShares σ assets + (σ.shares who).raw) := by
        funext x
        by_cases hx : x = who <;>
          simp [rawShares, Function.update, hx, Amount.raw_add, Amount.raw_ofWord]
      have hframe :=
        sum_update_not_mem H (rawShares σ.shares) ht
          (mintedShares σ assets + (σ.shares who).raw)
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
  · have hle := Finset.single_le_sum (f := fun a => (σ.shares a).raw)
      (fun _ _ => Nat.zero_le _) hx
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
      have hle := Finset.single_le_sum (f := fun x => (σ.shares x).raw)
        (fun _ _ => Nat.zero_le _) hae
      exact Amount.ext (Nat.eq_zero_of_le_zero (hle.trans_eq herase))
    · exact h0 a ha
  · have hwho0 : σ.shares who = 0 := h0 who hw
    have hts0 : σ.totalShares.raw = 0 :=
      Nat.eq_zero_of_le_zero (by
        have hwho0r : (σ.shares who).raw = 0 := by
          simpa [Amount.raw_zero] using congrArg Amount.raw hwho0
        exact ((Amount.le_iff _ _).mp hall).trans_eq hwho0r)
    by_cases ha : a ∈ H
    · have hle := Finset.single_le_sum (f := fun x => (σ.shares x).raw)
        (fun _ _ => Nat.zero_le _) ha
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
      exact htsr hzraw.2
    rw [claim, if_neg hts, claim, if_neg hts']
    by_cases ha : a = who
    · subst ha
      simp only [depositPost, Function.update_self, Amount.raw_add, Amount.raw_ofWord, hm]
      refine Nat.le_trans
        (deposit_rate_nondecreasing σ.totalAssets.raw σ.totalShares.raw
          (σ.shares a).raw assets.raw hTS) ?_
      rw [Nat.add_comm σ.totalShares.raw]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _
        (Nat.le_add_left (σ.shares a).raw
          (assets.raw * σ.totalShares.raw / σ.totalAssets.raw)))
    · simp only [depositPost, Function.update_of_ne ha, Amount.raw_add, Amount.raw_ofWord, hm]
      convert deposit_rate_nondecreasing σ.totalAssets.raw σ.totalShares.raw
        (σ.shares a).raw assets.raw hTS using 2
      simp [Nat.add_comm]

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


theorem inv_solvent (self : Address) (w : World Storage Ext Event) (h : Inv self w) :
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

private theorem deposit_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {assets : Amount vaultAsset}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : DepositOk ctx w assets) :
    Inv self (worldAfter (deposit assets) ctx w) := by
  have hrun := deposit_ok ctx w assets h
  simp [worldAfter, hrun]
  obtain ⟨hta, hst⟩ := hInv
  refine ⟨?hold, invStorage_of_depositPost w.self ctx.sender assets hst⟩
  subst hself
  have hb := move_dst (g := w.ext.asset) (amt := assets.raw) hsne
  simp [holdings, extAfterMove, depositPost, hb, Amount.raw_add] at hta ⊢
  omega

private theorem withdraw_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {sharesIn : Amount vShare}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : WithdrawOk ctx w sharesIn) :
    Inv self (worldAfter (withdraw sharesIn) ctx w) := by
  have hrun := withdraw_ok ctx w sharesIn h
  simp [worldAfter, hrun]
  obtain ⟨hta, hst⟩ := hInv
  refine ⟨?hold, invStorage_of_withdrawPost w.self ctx.sender sharesIn
    (redeemedAssets w.self sharesIn) hst h.bal⟩
  subst hself
  have hb := move_src (g := w.ext.asset)
    (amt := redeemedAssets w.self sharesIn) hsne.symm
  change (w.self.totalAssets - Amount.ofWord (redeemedAssets w.self sharesIn)).raw ≤
    (move w.ext.asset ctx.self ctx.sender (redeemedAssets w.self sharesIn)).balances
      ctx.self
  rw [Amount.raw_sub, Amount.raw_ofWord, hb]
  exact Nat.sub_le_sub_right hta _

/-! ### Invariant preservation -/

theorem deposit_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .deposit :=
  PreservesInvFnAt_of_ok fun assets ctx w _n _w' hself hsne hInv hrun => by
    have hI := deposit_ok_inv self hself hsne hInv (deposit_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem withdraw_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .withdraw :=
  PreservesInvFnAt_of_ok fun sharesIn ctx w _n _w' hself hsne hInv hrun => by
    have hI := withdraw_ok_inv self hself hsne hInv (withdraw_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem pause_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .pause := by
  intro u ctx w _ _ hInv
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := pause_ok ctx w howner
    simp [worldAfter, hrun]
    obtain ⟨hta, H, h0, hs⟩ := hInv
    exact ⟨hta, ⟨H, h0, hs⟩⟩
  · have hrun := pause_only_owner ctx w howner
    simp [worldAfter, hrun]; exact hInv

theorem unpause_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .unpause := by
  intro u ctx w _ _ hInv
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := unpause_ok ctx w howner
    simp [worldAfter, hrun]
    obtain ⟨hta, H, h0, hs⟩ := hInv
    exact ⟨hta, ⟨H, h0, hs⟩⟩
  · have hrun := unpause_only_owner ctx w howner
    simp [worldAfter, hrun]; exact hInv

theorem paused?_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .paused? := by
  intro u ctx w _ _ hInv
  unfold worldAfter
  rw [paused?_returns_stored]
  exact hInv

private theorem previewDeposit_worldAfter (assets : Amount vaultAsset)
    (ctx : Ctx) (w : World Storage Ext Event) :
    worldAfter (previewDeposit assets) ctx w = w := by
  apply worldAfter_eq_self
  intro _ w' hrun
  simp [previewDeposit] at hrun
  by_cases hts : w.self.totalShares = 0
  · simp [hts] at hrun
    exact hrun.2.symm
  · simp [hts, Amount.mulDivDown, Tx.run_map, Tx.run_mulDivDown] at hrun
    split_ifs at hrun; cases hrun
    rfl

private theorem previewRedeem_worldAfter (sharesIn : Amount vShare)
    (ctx : Ctx) (w : World Storage Ext Event) :
    worldAfter (previewRedeem sharesIn) ctx w = w := by
  apply worldAfter_eq_self
  intro _ w' hrun
  simp [previewRedeem, Amount.mulDivDown, Tx.run_map, Tx.run_mulDivDown] at hrun
  split_ifs at hrun <;> cases hrun
  rfl

theorem previewDeposit_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .previewDeposit := by
  intro assets ctx w _ _ hInv
  rw [previewDeposit_worldAfter]
  exact hInv

theorem previewRedeem_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .previewRedeem := by
  intro sharesIn ctx w _ _ hInv
  rw [previewRedeem_worldAfter]
  exact hInv

theorem vault_preserves_inv (self : Address) :
    PreservesInvAt spec (Inv self) self :=
  PreservesInvAt.of_fns fun fn =>
    match fn with
    | .deposit => deposit_preserves_inv self
    | .withdraw => withdraw_preserves_inv self
    | .previewDeposit => previewDeposit_preserves_inv self
    | .previewRedeem => previewRedeem_preserves_inv self
    | .pause => pause_preserves_inv self
    | .unpause => unpause_preserves_inv self
    | .paused? => paused?_preserves_inv self

/-! ### Authorization -/

theorem deposit_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .deposit :=
  NoUnauthorizedDecreaseFn_of_ok fun assets ctx w a n w' _hInv hrun hdec => by
    have hok := deposit_ok_of_run ctx w hrun
    cases hrun.symm.trans (deposit_ok ctx w assets hok)
    exact Nat.not_lt.mpr (claim_le_of_depositPost w.self ctx.sender a assets) hdec

theorem withdraw_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .withdraw :=
  NoUnauthorizedDecreaseFn_of_ok fun sharesIn ctx w a n w' hInv hrun hdec => by
    change ctx.sender = a
    by_cases hs : ctx.sender = a
    · exact hs
    · obtain ⟨_, hst⟩ := hInv
      have hok := withdraw_ok_of_run ctx w hrun
      cases hrun.symm.trans (withdraw_ok ctx w sharesIn hok)
      exact (Nat.not_lt.mpr (claim_le_of_withdrawPost w.self ctx.sender a
        sharesIn hst hs hok.bal hok.denom hok.supply) hdec).elim

theorem pause_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .pause := by
  intro u ctx w a _hInv hdec
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := pause_ok ctx w howner
    simp [worldAfter, hrun] at hdec
    simp [claim] at hdec
  · have hrun := pause_only_owner ctx w howner
    simp [worldAfter, hrun] at hdec

theorem unpause_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .unpause := by
  intro u ctx w a _hInv hdec
  by_cases howner : ctx.sender = w.self.owner
  · have hrun := unpause_ok ctx w howner
    simp [worldAfter, hrun] at hdec
    simp [claim] at hdec
  · have hrun := unpause_only_owner ctx w howner
    simp [worldAfter, hrun] at hdec

theorem paused?_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .paused? := by
  intro u ctx w a _hInv hdec
  unfold worldAfter at hdec
  rw [paused?_returns_stored ctx w] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem previewDeposit_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .previewDeposit := by
  intro assets ctx w a _hInv hdec
  rw [previewDeposit_worldAfter] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem previewRedeem_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .previewRedeem := by
  intro sharesIn ctx w a _hInv hdec
  rw [previewRedeem_worldAfter] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem vault_no_unauth (self : Address) :
    NoUnauthorizedDecrease spec (Inv self) claim Auth :=
  NoUnauthorizedDecrease.of_fns fun fn =>
    match fn with
    | .deposit => deposit_auth self
    | .withdraw => withdraw_auth self
    | .previewDeposit => previewDeposit_auth self
    | .previewRedeem => previewRedeem_auth self
    | .pause => pause_auth self
    | .unpause => unpause_auth self
    | .paused? => paused?_auth self

namespace Proof

theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w) (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  solvent_run_at (vault_preserves_inv self) (inv_rely self) (inv_solvent self) h tr hW hR

theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (vault_no_unauth self) (vault_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Proof

end Vault
