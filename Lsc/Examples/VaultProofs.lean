import Lsc.Examples.Vault

/-!
# Vault — theorems

`Amount.toNat` / `Amount.ofNat` are the identity; helpers use them so `+` / `*`
typecheck (there is no `HAdd` on `Amount`, by design). Because `Amount τ s` is
definitionally `Nat`, mixed-token `Amount.add` is accepted by the elaborator —
unit safety is a surface discipline. An irreducible wrapper would break `rfl`
certificates.
-/

open Lsc Vault

namespace Vault

variable (ctx : Ctx) (w : World Storage Event)

/-- Shares that `deposit` mints from `σ` (the floor; 1:1 when empty). -/
def mintedShares (σ : Storage) (assets : Amount ASSET assetScale) : Amount SHARE shareScale :=
  if σ.totalShares = (0 : Amount SHARE shareScale) then assets
  else assets * σ.totalShares / σ.totalAssets

/-- Storage after a successful `deposit` by `who`. -/
def depositPost (σ : Storage) (who : Address) (assets : Amount ASSET assetScale) : Storage :=
  let minted := mintedShares σ assets
  { σ with
    totalAssets := assets + σ.totalAssets
    totalShares := minted + σ.totalShares
    shares := Function.update σ.shares who (minted + σ.shares who) }

/-- Assets `withdraw` pays. -/
def redeemedAssets (σ : Storage) (sharesIn : Amount SHARE shareScale) : Amount ASSET assetScale :=
  sharesIn * σ.totalAssets / σ.totalShares

/-- Storage after a successful `withdraw` by `who`. -/
def withdrawPost (σ : Storage) (who : Address) (sharesIn : Amount SHARE shareScale)
    (assetsOut : Amount ASSET assetScale) : Storage :=
  { σ with
    totalAssets := σ.totalAssets - assetsOut
    totalShares := σ.totalShares - sharesIn
    shares := Function.update σ.shares who (σ.shares who - sharesIn) }

/-! ### Views -/

theorem paused?_returns_stored :
    Tx.run paused? ctx w = .ok (w.self.paused, w) := by
  simp [paused?]

/-! ### pause -/

theorem pause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run pause ctx w =
      .ok ((), { w with self := { w.self with paused := Flag.on }, log := w.log ++ [.Paused] }) := by
  simp [pause, howner]

/-- `pause` reverts unless the caller is the owner. -/
theorem pause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run pause ctx w = .error (.user .NotOwner) := by
  simp [pause, h]

theorem unpause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run unpause ctx w = .error (.user .NotOwner) := by
  simp [unpause, h]

/-! ### deposit -/

/-- A paused vault rejects every deposit. -/
theorem deposit_reverts_when_paused (assets : Amount ASSET assetScale)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (deposit assets) ctx w = .error (.user .Paused) := by
  simp [deposit, hp]

/-- Zero-asset deposits revert (even when the vault is live). -/
theorem deposit_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (deposit (0 : Amount ASSET assetScale)) ctx w = .error (.user .Zero) := by
  have hz : ¬ (0 : Amount ASSET assetScale) < 0 := Nat.lt_irrefl 0
  simp [deposit, hp, hz]

/-- Success hypotheses for `deposit`. -/
structure DepositOk (w : World Storage Event) (assets : Amount ASSET assetScale) : Prop where
  paused : w.self.paused = Flag.off
  pos : (0 : Amount ASSET assetScale) < assets
  xfer : ∀ t sel args, w.ext t sel args = some [1]
  prod :
    w.self.totalShares = (0 : Amount SHARE shareScale) ∨
      (w.self.totalAssets ≠ (0 : Amount ASSET assetScale) ∧
        Amount.toNat assets * Amount.toNat w.self.totalShares < wordBound)
  addAssets : Amount.toNat assets + Amount.toNat w.self.totalAssets < wordBound
  addShares :
    Amount.toNat (mintedShares w.self assets) + Amount.toNat w.self.totalShares < wordBound
  addBal :
    Amount.toNat (mintedShares w.self assets) + Amount.toNat (w.self.shares ctx.sender) <
      wordBound

/-- Exact post-state of a successful `deposit`. -/
theorem deposit_ok (assets : Amount ASSET assetScale) (h : DepositOk ctx w assets) :
    Tx.run (deposit assets) ctx w =
      .ok (mintedShares w.self assets,
        { w with self := depositPost w.self ctx.sender assets, log := w.log ++ [.Deposit ctx.sender assets (mintedShares w.self assets)] }) := by
  rcases h with ⟨hp, hpos, hxfer, hprod, haddA, haddS, haddB⟩
  simp only [Amount.toNat] at haddA haddS haddB
  simp [deposit, hp, hpos, IERC20.run_transferFrom, hxfer]
  by_cases hts : w.self.totalShares = (0 : Amount SHARE shareScale)
  · simp [hts, mintedShares] at haddS haddB
    simp [hts, haddA, haddS, haddB, depositPost, mintedShares]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp only [Amount.toNat] at hmul
      simp [hts, mintedShares] at haddS haddB
      simp [hts, hta, hmul, haddA, haddS, haddB, depositPost, mintedShares]

/-- If the vault is solvent (`totalShares ≤ totalAssets`), minted shares never exceed assets. -/
theorem deposit_shares_le_assets_when_rate_ge_one (assets : Amount ASSET assetScale)
    (hrate : w.self.totalShares ≤ w.self.totalAssets) :
    mintedShares w.self assets ≤ assets := by
  by_cases hts : w.self.totalShares = (0 : Amount SHARE shareScale)
  · simp [mintedShares, hts]
  · simp [mintedShares, hts]
    have hta : 0 < w.self.totalAssets :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hts) hrate
    have hle : assets * w.self.totalShares / w.self.totalAssets
        ≤ assets * w.self.totalAssets / w.self.totalAssets :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ hrate)
    have hdiv : assets * w.self.totalAssets / w.self.totalAssets = assets := by
      simpa [Nat.mul_comm] using Nat.mul_div_right assets hta
    exact Nat.le_trans hle (Nat.le_of_eq hdiv)

/-- A successful deposit preserves `totalShares ≤ totalAssets` when it held before. -/
theorem deposit_preserves_rate_lower_bound (assets : Amount ASSET assetScale)
    (h : DepositOk ctx w assets)
    (hrate : w.self.totalShares ≤ w.self.totalAssets) :
    ∃ minted w', Tx.run (deposit assets) ctx w = .ok (minted, w') ∧
      w'.self.totalShares ≤ w'.self.totalAssets := by
  refine ⟨_, _, deposit_ok ctx w assets h, ?_⟩
  simp [depositPost]
  exact Nat.add_le_add
    (deposit_shares_le_assets_when_rate_ge_one w assets hrate) hrate

/-! ### withdraw -/

/-- A paused vault rejects every withdraw. -/
theorem withdraw_reverts_when_paused (sharesIn : Amount SHARE shareScale)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Paused) := by
  simp [withdraw, hp]

/-- Success hypotheses for `withdraw`. -/
structure WithdrawOk (w : World Storage Event) (sharesIn : Amount SHARE shareScale) : Prop where
  paused : w.self.paused = Flag.off
  pos : (0 : Amount SHARE shareScale) < sharesIn
  bal : sharesIn ≤ w.self.shares ctx.sender
  supply : sharesIn ≤ w.self.totalShares
  denom : w.self.totalShares ≠ (0 : Amount SHARE shareScale)
  prod : Amount.toNat sharesIn * Amount.toNat w.self.totalAssets < wordBound
  assetsFit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets
  xfer : ∀ t sel args, w.ext t sel args = some [1]

/-- Exact post-state of a successful `withdraw`. -/
theorem withdraw_ok (sharesIn : Amount SHARE shareScale) (h : WithdrawOk ctx w sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      .ok (redeemedAssets w.self sharesIn,
        { w with self := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn), log := w.log ++ [.Withdraw ctx.sender (redeemedAssets w.self sharesIn) sharesIn] }) := by
  rcases h with ⟨hp, hpos, hbal, hsup, hden, hmul, hfit, hxfer⟩
  simp only [Amount.toNat, redeemedAssets] at hden hmul hfit
  -- Reduce accounting first; `run_transfer` must wait until `w'.ext` is definitionally `w.ext`.
  simp [withdraw, hp, hpos, hbal, hden, hmul, hsup, hfit, redeemedAssets]
  simp [IERC20.run_transfer, hxfer, withdrawPost, hp]

/-- The floor never overpays: `assetsOut * totalShares ≤ sharesIn * totalAssets`. -/
theorem withdraw_assets_le_proportional (sharesIn : Amount SHARE shareScale)
    (_h : WithdrawOk ctx w sharesIn) :
    Amount.toNat (redeemedAssets w.self sharesIn) * Amount.toNat w.self.totalShares ≤
      Amount.toNat sharesIn * Amount.toNat w.self.totalAssets := by
  simp [redeemedAssets]
  exact Nat.div_mul_le_self (Nat.mul sharesIn w.self.totalAssets) w.self.totalShares

end Vault
