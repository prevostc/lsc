import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Examples.VaultProofs
import Lsc.Compiler.Bytecode

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-!
Security obligations for the vault. `Inv` is indexed by the vault address because
`holdings` reads `ext.asset.balances self`. Well-formed traces use
`PreservesInvFnAt` (`ctx.self = self`, `ctx.sender ≠ self`).
-/

/-- Redeemable assets of `a`. Zero when the supply is empty. -/
def claim (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.totalAssets / σ.totalShares

/-- Only a `withdraw` by `a` itself may decrease `claim a`. -/
def Auth (a : Address) (c : Call spec) (_s : Storage) : Prop :=
  match c.fn, c.args with
  | .withdraw, _ => c.sender = a
  | _, _ => False

/-- Deposit is the only inflow of claim-units; it is `0` on revert. -/
def inflow (c : Call spec) (w : World Storage Ext Event) : Nat :=
  match c.fn, c.args with
  | .deposit, assets =>
    match Tx.run (deposit assets) c.toCtx w with
    | .ok _ => assets.toNat
    | .error _ => 0
  | _, _ => 0

/-- Underlying-token balance of the vault. -/
def holdings (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.asset.balances self

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => σ.shares a) = σ.totalShares

/-- `totalAssets ≤` ghost balance of `self`, and share balances have finite support. -/
def Inv (self : Address) (w : World Storage Ext Event) : Prop :=
  w.self.totalAssets ≤ holdings self w ∧ InvStorage w.self

/-- Between our calls: vault token balance is non-decreasing and `decimals` is fixed. -/
def vaultRely (self : Address) (x x' : Ext) : Prop :=
  Rely self x.asset x'.asset

/-! ### Environment -/

theorem inv_rely (self : Address) :
    PreservesInvEnv spec (Inv self) (vaultRely self) := by
  intro w x' ⟨hta, hinv⟩ ⟨hbal, _hdec⟩
  refine ⟨?_, hinv⟩
  simp [holdings] at hta ⊢
  exact Nat.le_trans hta hbal

/-! ### Share-support preservation -/

private theorem invStorage_of_depositPost (σ : Storage) (who : Address)
    (assets : Amount ASSET assetScale) (hInv : InvStorage σ) :
    InvStorage (depositPost σ who assets) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  let n := mintedShares σ assets
  by_cases ht : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ who := by intro h; subst h; exact ha ht
      simp [depositPost, Function.update_of_ne hne]
      exact h0 a ha
    · have hupd := sum_update_mem H σ.shares ht (n + σ.shares who)
      have hcancel :
          H.sum (Function.update σ.shares who (n + σ.shares who)) =
            H.sum σ.shares + n := by
        revert hupd
        generalize hS' : H.sum (Function.update σ.shares who (n + σ.shares who)) = S'
        generalize hS : H.sum σ.shares = S
        generalize hd : σ.shares who = d
        intro hupd
        omega
      change (∑ a ∈ H, (depositPost σ who assets).shares a) =
        (depositPost σ who assets).totalShares
      simp only [depositPost]
      have hn : n + σ.shares who = mintedShares σ assets + σ.shares who := by
        simp [n]
      simp [← hn, hcancel, hsum, n]
      omega
  · refine ⟨insert who H, ?_, ?_⟩
    · intro a ha
      have hat : a ≠ who := by
        intro h; subst h; exact ha (Finset.mem_insert_self _ _)
      have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
      simp [depositPost, Function.update_of_ne hat]
      exact h0 a haH
    · have hframe := sum_update_not_mem H σ.shares ht (n + σ.shares who)
      have hb0 : σ.shares who = 0 := h0 who ht
      have hsum' :
          (∑ a ∈ insert who H, (depositPost σ who assets).shares a) =
            H.sum σ.shares + n := by
        rw [Finset.sum_insert ht]
        simp only [depositPost, Function.update_self]
        rw [show mintedShares σ assets + σ.shares who = n + σ.shares who by simp [n]]
        rw [hframe, hb0]
        omega
      change (∑ a ∈ insert who H, (depositPost σ who assets).shares a) =
        (depositPost σ who assets).totalShares
      simpa [depositPost, n] using (hsum'.trans (by rw [hsum])).trans (Nat.add_comm _ _)

private theorem invStorage_of_withdrawPost (σ : Storage) (who : Address)
    (sharesIn : Amount SHARE shareScale) (assetsOut : Nat)
    (hInv : InvStorage σ) (hn : sharesIn.toNat ≤ σ.shares who) :
    InvStorage (withdrawPost σ who sharesIn assetsOut) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  let n := sharesIn.toNat
  by_cases hs : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ who := by intro h; subst h; exact ha hs
      simp [withdrawPost, Function.update_of_ne ha_src]
      exact h0 a ha
    · have hs1 := sum_update_mem H σ.shares hs (σ.shares who - n)
      have hsumd :
          H.sum (Function.update σ.shares who (σ.shares who - n)) =
            H.sum σ.shares - n := by
        omega
      change (∑ a ∈ H, (withdrawPost σ who sharesIn assetsOut).shares a) =
        (withdrawPost σ who sharesIn assetsOut).totalShares
      simpa [withdrawPost, n] using hsumd.trans (by rw [hsum])
  · have hb0 : σ.shares who = 0 := h0 who hs
    have hn0 : sharesIn.toNat = 0 := Nat.eq_zero_of_le_zero (hn.trans_eq hb0)
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp [withdrawPost, hn0, Function.update_eq_self]
      exact h0 a ha
    · simp [withdrawPost, hn0, Function.update_eq_self, hsum]

private theorem invStorage_shares_le (σ : Storage) (hInv : InvStorage σ) (x : Address) :
    σ.shares x ≤ σ.totalShares := by
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hx : x ∈ H
  · have := Finset.single_le_sum (f := fun a => σ.shares a) (fun _ _ => Nat.zero_le _) hx
    simpa [hsum] using this
  · simp [h0 x hx]

private theorem invStorage_bystander_zero (σ : Storage) (who a : Address)
    (hInv : InvStorage σ) (hne : who ≠ a) (hall : σ.totalShares ≤ σ.shares who) :
    σ.shares a = 0 := by
  have hwho := invStorage_shares_le σ hInv who
  have heq : σ.shares who = σ.totalShares := Nat.le_antisymm hwho hall
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hw : who ∈ H
  · have herase : (H.erase who).sum (fun x => σ.shares x) = 0 := by
      have hsplit := Finset.sum_erase_add (s := H) (f := fun x => σ.shares x) hw
      rw [hsum, heq] at hsplit
      exact Nat.add_eq_right.mp hsplit
    by_cases ha : a ∈ H
    · have hae : a ∈ H.erase who := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
      have hle := Finset.single_le_sum (f := fun x => σ.shares x)
        (fun _ _ => Nat.zero_le _) hae
      omega
    · exact h0 a ha
  · have hwho0 : σ.shares who = 0 := h0 who hw
    have hts0 : σ.totalShares = 0 := Nat.eq_zero_of_le_zero (hall.trans_eq hwho0)
    by_cases ha : a ∈ H
    · have hle := Finset.single_le_sum (f := fun x => σ.shares x)
        (fun _ _ => Nat.zero_le _) ha
      simpa [hsum, hts0] using hle
    · exact h0 a ha

/-- Deposit never decreases `claim`, even for the depositor: minting rounds against them,
so the exchange rate does not fall, and their share count does not fall. -/
private theorem claim_le_of_depositPost (σ : Storage) (who a : Address)
    (assets : Amount ASSET assetScale) :
    claim a σ ≤ claim a (depositPost σ who assets) := by
  by_cases hts : σ.totalShares = 0
  · simp [claim, hts]
  · have hTS : 0 < σ.totalShares := Nat.pos_of_ne_zero hts
    by_cases ha : a = who
    · rw [ha]
      simp [claim, hts, depositPost, Function.update_self]
      simp [mintedShares, hts]
      rw [Nat.add_comm (σ.totalShares * assets.toNat / σ.totalAssets) σ.totalShares]
      refine Nat.le_trans
        (deposit_rate_nondecreasing σ.totalAssets σ.totalShares (σ.shares who)
          assets.toNat hTS) ?_
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _
        (Nat.le_add_left (σ.shares who) (σ.totalShares * assets.toNat / σ.totalAssets)))
    · simp [claim, hts, depositPost, Function.update_of_ne ha]
      simp [mintedShares, hts]
      rw [Nat.add_comm (σ.totalShares * assets.toNat / σ.totalAssets) σ.totalShares]
      exact deposit_rate_nondecreasing σ.totalAssets σ.totalShares (σ.shares a)
        assets.toNat hTS

/-- Another account's withdraw does not decrease `claim a`. The `TS' = 0` case uses
`InvStorage` to force `shares a = 0`. -/
private theorem claim_le_of_withdrawPost (σ : Storage) (who a : Address)
    (sharesIn : Amount SHARE shareScale)
    (hInv : InvStorage σ) (hne : who ≠ a)
    (hbal : sharesIn.toNat ≤ σ.shares who)
    (hden : σ.totalShares ≠ 0)
    (hsup : sharesIn.toNat ≤ σ.totalShares) :
    claim a σ ≤
      claim a (withdrawPost σ who sharesIn (redeemedAssets σ sharesIn)) := by
  by_cases hts' : σ.totalShares - sharesIn.toNat = 0
  · have hs_eq : sharesIn.toNat = σ.totalShares :=
      Nat.le_antisymm hsup (Nat.sub_eq_zero_iff_le.mp hts')
    have hall : σ.totalShares ≤ σ.shares who := by omega
    have ha0 := invStorage_bystander_zero σ who a hInv hne hall
    have hpost0 :
        (withdrawPost σ who sharesIn (redeemedAssets σ sharesIn)).totalShares = 0 := by
      simpa [withdrawPost] using hts'
    simp [claim, hden, ha0, hpost0]
  · have hs_ne : sharesIn.toNat ≠ σ.totalShares := by
      intro heq; exact hts' (by simp [heq])
    have hs_lt : sharesIn.toNat < σ.totalShares := Nat.lt_of_le_of_ne hsup hs_ne
    have hTS : 0 < σ.totalShares := Nat.pos_of_ne_zero hden
    simp [claim, hden, withdrawPost, Function.update_of_ne hne.symm, redeemedAssets, hts']
    exact withdraw_rate_nondecreasing σ.totalAssets σ.totalShares (σ.shares a)
      sharesIn.toNat hTS hs_lt

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
      simp [claim, hts, hs0]
    · have hpos : 0 < w.self.totalShares := Nat.pos_of_ne_zero hts
      have hcl :
          H.sum (fun a => claim a w.self) =
            H.sum (fun a => w.self.shares a * w.self.totalAssets / w.self.totalShares) := by
        apply Finset.sum_congr rfl
        intro a _; simp [claim, hts]
      have hle :=
        sum_mul_div_le H (fun a => w.self.shares a) w.self.totalAssets
          w.self.totalShares hs hpos
      rw [hcl]
      exact Nat.le_trans hle hta

/-! ### Invariant preservation -/

theorem deposit_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .deposit := by
  intro assets ctx w hself hsne hInv
  by_cases hp : w.self.paused = Flag.off
  · by_cases hpos : 0 < assets.toNat
    · by_cases hprod :
          w.self.totalShares = 0 ∨
            (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound)
      · by_cases hminted : 0 < mintedShares w.self assets
        · by_cases hf : w.faults w.ncalls = true
          · have hrun := deposit_reverts_on_fault ctx w assets hp hpos hprod hminted hf
            simp [worldAfter, hrun]; exact hInv
          · have hf' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf
            by_cases hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender
            · by_cases haddA : w.self.totalAssets + assets.toNat < wordBound
              · by_cases haddS : mintedShares w.self assets + w.self.totalShares < wordBound
                · by_cases haddB : mintedShares w.self assets + w.self.shares ctx.sender < wordBound
                  · have hok : DepositOk ctx w assets :=
                      ⟨hp, hpos, hminted, hf', hcov, hprod, haddA, haddS, haddB⟩
                    have hrun := deposit_ok ctx w assets hok
                    simp [worldAfter, hrun]
                    obtain ⟨hta, hst⟩ := hInv
                    refine ⟨?hold, invStorage_of_depositPost w.self ctx.sender assets hst⟩
                    subst hself
                    have hb := move_dst (g := w.ext.asset) (amt := assets.toNat) hsne
                    simp [holdings, extAfterMove, depositPost, hb] at hta ⊢
                    omega
                  · have hrun := deposit_reverts_on_add_bal ctx w assets hp hpos hprod hminted
                      hf' hcov haddA haddS haddB
                    simp [worldAfter, hrun]; exact hInv
                · have hrun := deposit_reverts_on_add_shares ctx w assets hp hpos hprod hminted
                    hf' hcov haddA haddS
                  simp [worldAfter, hrun]; exact hInv
              · have hrun := deposit_reverts_on_add_assets ctx w assets hp hpos hprod hminted
                  hf' hcov haddA
                simp [worldAfter, hrun]; exact hInv
            · have hrun := deposit_reverts_on_no_cover ctx w assets hp hpos hprod hminted hf' hcov
              simp [worldAfter, hrun]; exact hInv
        · have hrun := deposit_reverts_on_zero_shares ctx w assets hp hpos hprod hminted
          simp [worldAfter, hrun]; exact hInv
      · by_cases hts : w.self.totalShares = 0
        · exact (hprod (Or.inl hts)).elim
        · by_cases hta0 : w.self.totalAssets = 0
          · have hrun := deposit_reverts_on_divByZero ctx w assets hp hpos hts hta0
            simp [worldAfter, hrun]; exact hInv
          · have hmul : ¬ w.self.totalShares * assets.toNat < wordBound := by
              intro hm; exact hprod (Or.inr ⟨hta0, hm⟩)
            have hrun := deposit_reverts_on_mul_overflow ctx w assets hp hpos hts hta0 hmul
            simp [worldAfter, hrun]; exact hInv
    · have hrun := deposit_reverts_on_nonpos ctx w assets hp hpos
      simp [worldAfter, hrun]; exact hInv
  · have hrun := deposit_reverts_when_paused ctx w assets hp
    simp [worldAfter, hrun]; exact hInv

theorem withdraw_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .withdraw := by
  intro sharesIn ctx w hself hsne hInv
  by_cases hp : w.self.paused = Flag.off
  · by_cases hpos : 0 < sharesIn.toNat
    · by_cases hbal : sharesIn.toNat ≤ w.self.shares ctx.sender
      · by_cases hden : w.self.totalShares = 0
        · have hrun := withdraw_reverts_on_divByZero ctx w sharesIn hp hpos hbal hden
          simp [worldAfter, hrun]; exact hInv
        · have hden' : w.self.totalShares ≠ 0 := hden
          by_cases hmul : w.self.totalAssets * sharesIn.toNat < wordBound
          · by_cases hassets : 0 < redeemedAssets w.self sharesIn
            · by_cases hsup : sharesIn.toNat ≤ w.self.totalShares
              · by_cases hfit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets
                · by_cases hf : w.faults w.ncalls = true
                  · have hrun := withdraw_reverts_on_fault ctx w sharesIn hp hpos hbal hsup
                      hden' hmul hassets hfit hf
                    simp [worldAfter, hrun]; exact hInv
                  · have hf' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf
                    by_cases hcov : redeemedAssets w.self sharesIn ≤ w.ext.asset.balances ctx.self
                    · have hok : WithdrawOk ctx w sharesIn :=
                        ⟨hp, hpos, hbal, hsup, hden', hmul, hassets, hfit, hf', hcov⟩
                      have hrun := withdraw_ok ctx w sharesIn hok
                      simp [worldAfter, hrun]
                      obtain ⟨hta, hst⟩ := hInv
                      refine ⟨?hold, invStorage_of_withdrawPost w.self ctx.sender sharesIn
                        (redeemedAssets w.self sharesIn) hst hbal⟩
                      subst hself
                      have hb := move_src (g := w.ext.asset)
                        (amt := redeemedAssets w.self sharesIn) hsne.symm
                      simp [holdings, extAfterMove, withdrawPost, hb] at hta hcov ⊢
                      omega
                    · have hrun := withdraw_reverts_on_no_cover ctx w sharesIn hp hpos hbal
                        hsup hden' hmul hassets hfit hf' hcov
                      simp [worldAfter, hrun]; exact hInv
                · have hrun := withdraw_reverts_on_assets_underflow ctx w sharesIn hp hpos
                    hbal hsup hden' hmul hassets hfit
                  simp [worldAfter, hrun]; exact hInv
              · have hrun := withdraw_reverts_on_insufficient_supply ctx w sharesIn hp hpos
                  hbal hden' hmul hassets (Nat.not_le.mp hsup)
                simp [worldAfter, hrun]; exact hInv
            · have hrun := withdraw_reverts_on_zero_assets ctx w sharesIn hp hpos hbal
                hden' hmul hassets
              simp [worldAfter, hrun]; exact hInv
          · have hrun := withdraw_reverts_on_mul_overflow ctx w sharesIn hp hpos hbal hden' hmul
            simp [worldAfter, hrun]; exact hInv
      · have hrun := withdraw_reverts_on_insufficient_shares ctx w sharesIn hp hpos
          (Nat.not_le.mp hbal)
        simp [worldAfter, hrun]; exact hInv
    · have hrun := withdraw_reverts_on_nonpos ctx w sharesIn hp hpos
      simp [worldAfter, hrun]; exact hInv
  · have hrun := withdraw_reverts_when_paused ctx w sharesIn hp
    simp [worldAfter, hrun]; exact hInv

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

theorem decimals_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .decimals := by
  intro u ctx w _ _ hInv
  unfold worldAfter
  rw [decimals_returns_stored]
  exact hInv

theorem previewDeposit_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .previewDeposit := by
  intro assets ctx w _ _ hInv
  unfold worldAfter
  simp [previewDeposit]
  by_cases hts : w.self.totalShares = 0
  · simp [hts]; exact hInv
  · simp [hts]
    unfold Tx.mulDivDown
    dsimp only [Tx.run]
    split_ifs <;> simp [hInv]

theorem previewRedeem_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .previewRedeem := by
  intro sharesIn ctx w _ _ hInv
  unfold worldAfter
  simp [previewRedeem]
  unfold Tx.mulDivDown
  dsimp only [Tx.run]
  split_ifs <;> simp [hInv]

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
    | .decimals => decimals_preserves_inv self

theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w) (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  solvent_run_at (vault_preserves_inv self) (inv_rely self) (inv_solvent self) h tr hW hR

/-! ### Authorization -/

theorem deposit_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .deposit := by
  intro assets ctx w a _hInv hdec
  by_cases hp : w.self.paused = Flag.off
  · by_cases hpos : 0 < assets.toNat
    · by_cases hprod :
          w.self.totalShares = 0 ∨
            (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound)
      · by_cases hminted : 0 < mintedShares w.self assets
        · by_cases hf : w.faults w.ncalls = true
          · have hrun := deposit_reverts_on_fault ctx w assets hp hpos hprod hminted hf
            simp [worldAfter, hrun] at hdec
          · have hf' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf
            by_cases hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender
            · by_cases haddA : w.self.totalAssets + assets.toNat < wordBound
              · by_cases haddS : mintedShares w.self assets + w.self.totalShares < wordBound
                · by_cases haddB : mintedShares w.self assets + w.self.shares ctx.sender < wordBound
                  · have hok : DepositOk ctx w assets :=
                      ⟨hp, hpos, hminted, hf', hcov, hprod, haddA, haddS, haddB⟩
                    have hrun := deposit_ok ctx w assets hok
                    simp [worldAfter, hrun] at hdec
                    exact Nat.not_lt.mpr (claim_le_of_depositPost w.self ctx.sender a assets) hdec
                  · have hrun := deposit_reverts_on_add_bal ctx w assets hp hpos hprod hminted
                      hf' hcov haddA haddS haddB
                    simp [worldAfter, hrun] at hdec
                · have hrun := deposit_reverts_on_add_shares ctx w assets hp hpos hprod hminted
                    hf' hcov haddA haddS
                  simp [worldAfter, hrun] at hdec
              · have hrun := deposit_reverts_on_add_assets ctx w assets hp hpos hprod hminted
                  hf' hcov haddA
                simp [worldAfter, hrun] at hdec
            · have hrun := deposit_reverts_on_no_cover ctx w assets hp hpos hprod hminted hf' hcov
              simp [worldAfter, hrun] at hdec
        · have hrun := deposit_reverts_on_zero_shares ctx w assets hp hpos hprod hminted
          simp [worldAfter, hrun] at hdec
      · by_cases hts : w.self.totalShares = 0
        · exact (hprod (Or.inl hts)).elim
        · by_cases hta0 : w.self.totalAssets = 0
          · have hrun := deposit_reverts_on_divByZero ctx w assets hp hpos hts hta0
            simp [worldAfter, hrun] at hdec
          · have hmul : ¬ w.self.totalShares * assets.toNat < wordBound := by
              intro hm; exact hprod (Or.inr ⟨hta0, hm⟩)
            have hrun := deposit_reverts_on_mul_overflow ctx w assets hp hpos hts hta0 hmul
            simp [worldAfter, hrun] at hdec
    · have hrun := deposit_reverts_on_nonpos ctx w assets hp hpos
      simp [worldAfter, hrun] at hdec
  · have hrun := deposit_reverts_when_paused ctx w assets hp
    simp [worldAfter, hrun] at hdec

theorem withdraw_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .withdraw := by
  intro sharesIn ctx w a hInv hdec
  change ctx.sender = a
  by_cases hs : ctx.sender = a
  · exact hs
  · obtain ⟨_, hst⟩ := hInv
    by_cases hp : w.self.paused = Flag.off
    · by_cases hpos : 0 < sharesIn.toNat
      · by_cases hbal : sharesIn.toNat ≤ w.self.shares ctx.sender
        · by_cases hden : w.self.totalShares = 0
          · have hrun := withdraw_reverts_on_divByZero ctx w sharesIn hp hpos hbal hden
            simp [worldAfter, hrun] at hdec
          · have hden' : w.self.totalShares ≠ 0 := hden
            by_cases hmul : w.self.totalAssets * sharesIn.toNat < wordBound
            · by_cases hassets : 0 < redeemedAssets w.self sharesIn
              · by_cases hsup : sharesIn.toNat ≤ w.self.totalShares
                · by_cases hfit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets
                  · by_cases hf : w.faults w.ncalls = true
                    · have hrun := withdraw_reverts_on_fault ctx w sharesIn hp hpos hbal hsup
                        hden' hmul hassets hfit hf
                      simp [worldAfter, hrun] at hdec
                    · have hf' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf
                      by_cases hcov : redeemedAssets w.self sharesIn ≤ w.ext.asset.balances ctx.self
                      · have hok : WithdrawOk ctx w sharesIn :=
                          ⟨hp, hpos, hbal, hsup, hden', hmul, hassets, hfit, hf', hcov⟩
                        have hrun := withdraw_ok ctx w sharesIn hok
                        simp [worldAfter, hrun] at hdec
                        exact (Nat.not_lt.mpr (claim_le_of_withdrawPost w.self ctx.sender a
                          sharesIn hst hs hbal hden' hsup) hdec).elim
                      · have hrun := withdraw_reverts_on_no_cover ctx w sharesIn hp hpos hbal
                          hsup hden' hmul hassets hfit hf' hcov
                        simp [worldAfter, hrun] at hdec
                  · have hrun := withdraw_reverts_on_assets_underflow ctx w sharesIn hp hpos
                      hbal hsup hden' hmul hassets hfit
                    simp [worldAfter, hrun] at hdec
                · have hrun := withdraw_reverts_on_insufficient_supply ctx w sharesIn hp hpos
                    hbal hden' hmul hassets (Nat.not_le.mp hsup)
                  simp [worldAfter, hrun] at hdec
              · have hrun := withdraw_reverts_on_zero_assets ctx w sharesIn hp hpos hbal
                  hden' hmul hassets
                simp [worldAfter, hrun] at hdec
            · have hrun := withdraw_reverts_on_mul_overflow ctx w sharesIn hp hpos hbal hden' hmul
              simp [worldAfter, hrun] at hdec
        · have hrun := withdraw_reverts_on_insufficient_shares ctx w sharesIn hp hpos
            (Nat.not_le.mp hbal)
          simp [worldAfter, hrun] at hdec
      · have hrun := withdraw_reverts_on_nonpos ctx w sharesIn hp hpos
        simp [worldAfter, hrun] at hdec
    · have hrun := withdraw_reverts_when_paused ctx w sharesIn hp
      simp [worldAfter, hrun] at hdec

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

theorem decimals_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .decimals := by
  intro u ctx w a _hInv hdec
  unfold worldAfter at hdec
  rw [decimals_returns_stored ctx w] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem previewDeposit_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .previewDeposit := by
  intro assets ctx w a _hInv hdec
  unfold worldAfter at hdec
  simp [previewDeposit] at hdec
  by_cases hts : w.self.totalShares = 0
  · simp [hts] at hdec
  · simp [hts] at hdec
    unfold Tx.mulDivDown at hdec
    dsimp only [Tx.run] at hdec
    split_ifs at hdec <;> simp [claim] at hdec

theorem previewRedeem_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .previewRedeem := by
  intro sharesIn ctx w a _hInv hdec
  unfold worldAfter at hdec
  simp [previewRedeem] at hdec
  unfold Tx.mulDivDown at hdec
  dsimp only [Tx.run] at hdec
  split_ifs at hdec <;> simp [claim] at hdec

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
    | .decimals => decimals_auth self

theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (vault_no_unauth self) (vault_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Vault

set_option maxHeartbeats 8000000
open Lsc.Compiler

/-- Runtime bytecode exists (`Op.call` is handled by the reifier and compiler). -/
def vault_runtime_some : Bool := (compileRuntime Vault.contract).isSome

#guard vault_runtime_some

#eval (compileRuntime Vault.contract).map List.length
