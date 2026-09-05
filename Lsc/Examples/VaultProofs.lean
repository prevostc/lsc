import Mathlib.Tactic.SplitIfs
import Lsc.Examples.Vault

/-!
# Vault — theorems

Statements are about `Tx.run (Vault.f args) ctx w`. Storage words are `Nat`;
ABI amounts are `Amount` at the boundary (`toNat` / `ofNat`).
-/

open Lsc Lsc.Stdlib Vault

namespace Vault

variable (ctx : Ctx) (w : World Storage Ext Event)

/-- Shares that `deposit` mints from `σ` (the floor; 1:1 when empty). -/
def mintedShares (σ : Storage) (assets : Amount ASSET assetScale) : Nat :=
  if σ.totalShares = 0 then assets.toNat
  else σ.totalShares * assets.toNat / σ.totalAssets

/-- Storage after a successful `deposit` by `who`. -/
def depositPost (σ : Storage) (who : Address) (assets : Amount ASSET assetScale) : Storage :=
  let minted := mintedShares σ assets
  { σ with
    totalAssets := σ.totalAssets + assets.toNat
    totalShares := minted + σ.totalShares
    shares := Function.update σ.shares who (minted + σ.shares who) }

/-- Assets `withdraw` pays. -/
def redeemedAssets (σ : Storage) (sharesIn : Amount SHARE shareScale) : Nat :=
  σ.totalAssets * sharesIn.toNat / σ.totalShares

/-- Storage after a successful `withdraw` by `who`. -/
def withdrawPost (σ : Storage) (who : Address) (sharesIn : Amount SHARE shareScale)
    (assetsOut : Nat) : Storage :=
  { σ with
    totalAssets := σ.totalAssets - assetsOut
    totalShares := σ.totalShares - sharesIn.toNat
    shares := Function.update σ.shares who (σ.shares who - sharesIn.toNat) }

/-- Ghost after pulling `amt` from `src` to `dst`. -/
def extAfterMove (x : Ext) (src dst : Address) (amt : Nat) : Ext :=
  { x with asset := move x.asset src dst amt }

private theorem toNat_zero_asset : (0 : Amount ASSET assetScale).toNat = 0 := rfl
private theorem toNat_zero_share : (0 : Amount SHARE shareScale).toNat = 0 := rfl

/-! ### Views -/

theorem paused?_returns_stored :
    Tx.run paused? ctx w = .ok (w.self.paused, w) := by
  simp [paused?]

theorem decimals_returns_stored :
    Tx.run decimals ctx w = .ok (w.self.assetDecimals, w) := by
  simp [decimals]

/-! ### pause -/

theorem pause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run pause ctx w =
      .ok ((), World.mk { w.self with paused := Flag.on } w.ext
        (w.log ++ [.Paused]) w.faults w.ncalls) := by
  simp [pause, howner]

theorem pause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run pause ctx w = .error (.user .NotOwner) := by
  simp [pause, h]

theorem unpause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run unpause ctx w =
      .ok ((), World.mk { w.self with paused := Flag.off } w.ext
        (w.log ++ [.Unpaused]) w.faults w.ncalls) := by
  simp [unpause, howner]

theorem unpause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run unpause ctx w = .error (.user .NotOwner) := by
  simp [unpause, h]

/-! ### deposit -/

theorem deposit_reverts_when_paused (assets : Amount ASSET assetScale)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (deposit assets) ctx w = .error (.user .Paused) := by
  simp [deposit, hp]

theorem deposit_reverts_on_nonpos (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : ¬ 0 < assets.toNat) :
    Tx.run (deposit assets) ctx w = .error (.user .Zero) := by
  simp [deposit, hp, hpos]

theorem deposit_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (deposit (0 : Amount ASSET assetScale)) ctx w = .error (.user .Zero) :=
  deposit_reverts_on_nonpos ctx w (0 : Amount ASSET assetScale) hp (by simp [toNat_zero_asset])

/-- Success hypotheses for `deposit`. -/
structure DepositOk (w : World Storage Ext Event) (assets : Amount ASSET assetScale) : Prop where
  paused : w.self.paused = Flag.off
  pos : 0 < assets.toNat
  noFault : w.faults w.ncalls = false
  cover : assets.toNat ≤ w.ext.asset.balances ctx.sender
  prod :
    w.self.totalShares = 0 ∨
      (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound)
  addAssets : w.self.totalAssets + assets.toNat < wordBound
  addShares : mintedShares w.self assets + w.self.totalShares < wordBound
  addBal : mintedShares w.self assets + w.self.shares ctx.sender < wordBound

theorem deposit_reverts_on_fault (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = true) :
    Tx.run (deposit assets) ctx w = .error .callFailed := by
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [hf]

theorem deposit_reverts_on_no_cover (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : ¬ assets.toNat ≤ w.ext.asset.balances ctx.sender) :
    Tx.run (deposit assets) ctx w = .error .callFailed := by
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, model, hcov]

/-- Exact post-state of a successful `deposit`. -/
theorem deposit_ok (assets : Amount ASSET assetScale) (h : DepositOk ctx w assets) :
    Tx.run (deposit assets) ctx w =
      .ok (mintedShares w.self assets,
        World.mk (depositPost w.self ctx.sender assets)
          (extAfterMove w.ext ctx.sender ctx.self assets.toNat)
          (w.log ++ [.Deposit ctx.sender assets (Amount.ofNat (mintedShares w.self assets))])
          w.faults (w.ncalls + 1)) := by
  rcases h with ⟨hp, hpos, hf, hcov, hprod, haddA, haddS, haddB⟩
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer, extAfterMove, depositPost]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB
    simp [hts, haddA, haddS, haddB, mintedShares]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp [hts, mintedShares] at haddS haddB
      simp [hts, hta, hmul, haddA, haddS, haddB, mintedShares]

theorem deposit_reverts_on_divByZero (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender)
    (hts : w.self.totalShares ≠ 0) (hta : w.self.totalAssets = 0) :
    Tx.run (deposit assets) ctx w = .error (.arith .divByZero) := by
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer, hts, hta]

theorem deposit_reverts_on_mul_overflow (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender)
    (hts : w.self.totalShares ≠ 0) (hta : w.self.totalAssets ≠ 0)
    (hmul : ¬ w.self.totalShares * assets.toNat < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer, hts, hta, hmul]

theorem deposit_reverts_on_add_assets (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender)
    (hprod :
      w.self.totalShares = 0 ∨
        (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound))
    (haddA : ¬ w.self.totalAssets + assets.toNat < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, haddA]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp [hts, hta, hmul, haddA]

theorem deposit_reverts_on_add_shares (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender)
    (hprod :
      w.self.totalShares = 0 ∨
        (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound))
    (haddA : w.self.totalAssets + assets.toNat < wordBound)
    (haddS : ¬ mintedShares w.self assets + w.self.totalShares < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS
    have hS : ¬ assets.toNat < wordBound := Nat.not_lt.mpr haddS
    simp [hts, haddA, hS]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp [hts, mintedShares] at haddS
      have hS :
          ¬ w.self.totalShares * assets.toNat / w.self.totalAssets + w.self.totalShares
              < wordBound :=
        Nat.not_lt.mpr haddS
      simp [hts, hta, hmul, haddA, hS]

theorem deposit_reverts_on_add_bal (assets : Amount ASSET assetScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets.toNat)
    (hf : w.faults w.ncalls = false)
    (hcov : assets.toNat ≤ w.ext.asset.balances ctx.sender)
    (hprod :
      w.self.totalShares = 0 ∨
        (w.self.totalAssets ≠ 0 ∧ w.self.totalShares * assets.toNat < wordBound))
    (haddA : w.self.totalAssets + assets.toNat < wordBound)
    (haddS : mintedShares w.self assets + w.self.totalShares < wordBound)
    (haddB : ¬ mintedShares w.self assets + w.self.shares ctx.sender < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  have hxfer : model .transferFrom ctx.self [ctx.sender, ctx.self, assets.toNat] w.ext.asset =
      some (1, move w.ext.asset ctx.sender ctx.self assets.toNat) :=
    model_transferFrom hcov
  simp [deposit, hp, hpos, Binding.transferFrom]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB
    have hB : ¬ assets.toNat + w.self.shares ctx.sender < wordBound := Nat.not_lt.mpr haddB
    simp [hts, haddA, haddS, hB]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp [hts, mintedShares] at haddS haddB
      have hB :
          ¬ w.self.totalShares * assets.toNat / w.self.totalAssets + w.self.shares ctx.sender
              < wordBound :=
        Nat.not_lt.mpr haddB
      simp [hts, hta, hmul, haddA, haddS, hB]

theorem deposit_shares_le_assets_when_rate_ge_one (assets : Amount ASSET assetScale)
    (hrate : w.self.totalShares ≤ w.self.totalAssets) :
    mintedShares w.self assets ≤ assets.toNat := by
  by_cases hts : w.self.totalShares = 0
  · simp [mintedShares, hts]
  · simp [mintedShares, hts]
    have hta : 0 < w.self.totalAssets :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hts) hrate
    have hle :
        w.self.totalShares * assets.toNat / w.self.totalAssets
          ≤ w.self.totalAssets * assets.toNat / w.self.totalAssets :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ hrate)
    have hdiv : w.self.totalAssets * assets.toNat / w.self.totalAssets = assets.toNat :=
      Nat.mul_div_right assets.toNat hta
    exact Nat.le_trans hle (Nat.le_of_eq hdiv)

/-! ### withdraw -/

theorem withdraw_reverts_when_paused (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Paused) := by
  simp [withdraw, hp]

theorem withdraw_reverts_on_nonpos (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : ¬ 0 < sharesIn.toNat) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Zero) := by
  simp [withdraw, hp, hpos]

theorem withdraw_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (withdraw (0 : Amount SHARE shareScale)) ctx w = .error (.user .Zero) :=
  withdraw_reverts_on_nonpos ctx w (0 : Amount SHARE shareScale) hp (by simp [toNat_zero_share])

theorem withdraw_reverts_on_insufficient_shares (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : w.self.shares ctx.sender < sharesIn.toNat) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .InsufficientShares) := by
  simp [withdraw, hp, hpos, Nat.not_le.mpr hbal]

theorem withdraw_reverts_on_divByZero (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares = 0) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .divByZero) := by
  simp [withdraw, hp, hpos, hbal, hden]

theorem withdraw_reverts_on_mul_overflow (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares ≠ 0)
    (hmul : ¬ w.self.totalAssets * sharesIn.toNat < wordBound) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .overflow) := by
  simp [withdraw, hp, hpos, hbal, hden, hmul]

theorem withdraw_reverts_on_insufficient_supply (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares ≠ 0)
    (hmul : w.self.totalAssets * sharesIn.toNat < wordBound)
    (hsup : w.self.totalShares < sharesIn.toNat) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .underflow) := by
  simp [withdraw, hp, hpos, hbal, hden, hmul, Nat.not_le.mpr hsup]

theorem withdraw_reverts_on_assets_underflow (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hsup : sharesIn.toNat ≤ w.self.totalShares) (hden : w.self.totalShares ≠ 0)
    (hmul : w.self.totalAssets * sharesIn.toNat < wordBound)
    (hfit : ¬ redeemedAssets w.self sharesIn ≤ w.self.totalAssets) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .underflow) := by
  simp only [redeemedAssets] at hfit
  simp [withdraw, hp, hpos, hbal, hden, hmul, hsup, hfit]

/-- Success hypotheses for `withdraw` up to the external call. -/
structure WithdrawOk (w : World Storage Ext Event) (sharesIn : Amount SHARE shareScale) : Prop where
  paused : w.self.paused = Flag.off
  pos : 0 < sharesIn.toNat
  bal : sharesIn.toNat ≤ w.self.shares ctx.sender
  supply : sharesIn.toNat ≤ w.self.totalShares
  denom : w.self.totalShares ≠ 0
  prod : w.self.totalAssets * sharesIn.toNat < wordBound
  assetsFit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets
  noFault : w.faults w.ncalls = false
  cover : redeemedAssets w.self sharesIn ≤ w.ext.asset.balances ctx.self

theorem withdraw_reverts_on_fault (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hsup : sharesIn.toNat ≤ w.self.totalShares) (hden : w.self.totalShares ≠ 0)
    (hmul : w.self.totalAssets * sharesIn.toNat < wordBound)
    (hfit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets)
    (hf : w.faults w.ncalls = true) :
    Tx.run (withdraw sharesIn) ctx w = .error .callFailed := by
  simp only [redeemedAssets] at hfit
  simp [withdraw, hp, hpos, hbal, hden, hmul, hsup, hfit, Binding.transfer]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [hf]

theorem withdraw_reverts_on_no_cover (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn.toNat)
    (hbal : sharesIn.toNat ≤ w.self.shares ctx.sender)
    (hsup : sharesIn.toNat ≤ w.self.totalShares) (hden : w.self.totalShares ≠ 0)
    (hmul : w.self.totalAssets * sharesIn.toNat < wordBound)
    (hfit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets)
    (hf : w.faults w.ncalls = false)
    (hcov : ¬ redeemedAssets w.self sharesIn ≤ w.ext.asset.balances ctx.self) :
    Tx.run (withdraw sharesIn) ctx w = .error .callFailed := by
  simp only [redeemedAssets] at hfit hcov
  simp [withdraw, hp, hpos, hbal, hden, hmul, hsup, hfit, Binding.transfer]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, model, hcov]

theorem withdraw_ok (sharesIn : Amount SHARE shareScale) (h : WithdrawOk ctx w sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      .ok (redeemedAssets w.self sharesIn,
        World.mk (withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn))
          (extAfterMove w.ext ctx.self ctx.sender (redeemedAssets w.self sharesIn))
          (w.log ++ [.Withdraw ctx.sender (Amount.ofNat (redeemedAssets w.self sharesIn)) sharesIn])
          w.faults (w.ncalls + 1)) := by
  rcases h with ⟨hp, hpos, hbal, hsup, hden, hmul, hfit, hf, hcov⟩
  have hxfer :
      model .transfer ctx.self [ctx.sender, redeemedAssets w.self sharesIn] w.ext.asset =
        some (1, move w.ext.asset ctx.self ctx.sender (redeemedAssets w.self sharesIn)) :=
    model_transfer hcov
  simp only [redeemedAssets] at hfit hxfer hcov
  simp [withdraw, hp, hpos, hbal, hden, hmul, hsup, hfit, Binding.transfer]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [assetB]
  simp [hf, hxfer, extAfterMove, withdrawPost, redeemedAssets, hp]

theorem withdraw_assets_le_proportional (sharesIn : Amount SHARE shareScale)
    (_h : WithdrawOk ctx w sharesIn) :
    redeemedAssets w.self sharesIn * w.self.totalShares ≤
      w.self.totalAssets * sharesIn.toNat := by
  simp [redeemedAssets]
  exact Nat.div_mul_le_self _ _

/-! ### Exchange-rate monotonicity (floor mint / redeem) -/

/-- `⌊x / c⌋ ≤ ⌊y / d⌋` when `x * d ≤ y * c`. -/
private theorem div_le_div_of_mul_le {x y c d : Nat}
    (hc : 0 < c) (hd : 0 < d) (h : x * d ≤ y * c) : x / c ≤ y / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hx : x / c * c ≤ x := Nat.div_mul_le_self x c
  have h1 : x / c * c * d ≤ y * c := Nat.le_trans (Nat.mul_le_mul_right d hx) h
  rw [Nat.mul_assoc, Nat.mul_comm c d, ← Nat.mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_right h1 hc

/-- Redeeming `s` shares for `a = ⌊s · TA / TS⌋` assets does not decrease the exchange
rate: `a * TS ≤ s * TA` gives `TA / TS ≤ (TA − a) / (TS − s)` as floors of `sa` shares. -/
theorem withdraw_rate_nondecreasing (TA TS sa s : Nat)
    (hTS : 0 < TS) (hs : s < TS) :
    sa * TA / TS ≤ sa * (TA - TA * s / TS) / (TS - s) := by
  set a := TA * s / TS
  have hTS' : 0 < TS - s := Nat.sub_pos_of_lt hs
  have hrate : TA * (TS - s) ≤ (TA - a) * TS := by
    have h1 : TA * (TS - s) = TA * TS - TA * s := Nat.mul_sub TA TS s
    have h2 : (TA - a) * TS = TA * TS - a * TS := Nat.sub_mul TA a TS
    have h3 : a * TS ≤ TA * s := Nat.div_mul_le_self (TA * s) TS
    rw [h1, h2]
    exact Nat.sub_le_sub_left h3 _
  have hprod : sa * TA * (TS - s) ≤ sa * (TA - a) * TS := by
    calc
      sa * TA * (TS - s) = sa * (TA * (TS - s)) := Nat.mul_assoc _ _ _
      _ ≤ sa * ((TA - a) * TS) := Nat.mul_le_mul_left sa hrate
      _ = sa * (TA - a) * TS := (Nat.mul_assoc _ _ _).symm
  exact div_le_div_of_mul_le hTS hTS' hprod

/-- Minting `m = ⌊assets · TS / TA⌋` shares against `assets` does not decrease the
exchange rate: `m * TA ≤ assets * TS` gives `TA / TS ≤ (TA + assets) / (TS + m)`. -/
theorem deposit_rate_nondecreasing (TA TS sa assets : Nat)
    (hTS : 0 < TS) :
    sa * TA / TS ≤ sa * (TA + assets) / (TS + TS * assets / TA) := by
  set m := TS * assets / TA
  have hTS' : 0 < TS + m := Nat.lt_of_lt_of_le hTS (Nat.le_add_right _ _)
  have hrate : TA * (TS + m) ≤ (TA + assets) * TS := by
    have h1 : TA * (TS + m) = TA * TS + TA * m := Nat.mul_add TA TS m
    have h2 : (TA + assets) * TS = TA * TS + assets * TS := Nat.add_mul TA assets TS
    have h3 : TA * m ≤ assets * TS := by
      calc
        TA * m = m * TA := Nat.mul_comm _ _
        _ ≤ TS * assets := Nat.div_mul_le_self (TS * assets) TA
        _ = assets * TS := Nat.mul_comm _ _
    rw [h1, h2]
    exact Nat.add_le_add_left h3 _
  have hprod : sa * TA * (TS + m) ≤ sa * (TA + assets) * TS := by
    calc
      sa * TA * (TS + m) = sa * (TA * (TS + m)) := Nat.mul_assoc _ _ _
      _ ≤ sa * ((TA + assets) * TS) := Nat.mul_le_mul_left sa hrate
      _ = sa * (TA + assets) * TS := (Nat.mul_assoc _ _ _).symm
  exact div_le_div_of_mul_le hTS hTS' hprod

end Vault
