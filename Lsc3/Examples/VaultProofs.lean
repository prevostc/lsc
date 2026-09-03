import Mathlib.Tactic.SplitIfs
import Lsc3.Examples.Vault

/-!
# Vault — theorems

`Amount.toNat` / `Amount.ofNat` are the identity; helpers use them so `+` / `*`
typecheck (there is no `HAdd` on `Amount`, by design). Because `Amount τ s` is
definitionally `Nat`, mixed-token `Amount.add` is accepted by the elaborator —
unit safety is a surface discipline. An irreducible wrapper would break `rfl`
certificates.
-/

open Lsc3 Vault

namespace Vault

variable (ctx : Ctx) (w : World Storage Event)

/-- Shares that `deposit` mints from `σ` (the floor; 1:1 when empty). -/
def mintedShares (σ : Storage) (assets : Amount ASSET WAD) : Amount SHARE WAD :=
  if σ.totalShares = (0 : Amount SHARE WAD) then assets
  else Amount.ofNat ((Amount.toNat assets * Amount.toNat σ.totalShares).div (Amount.toNat σ.totalAssets))

/-- Storage after a successful `deposit` by `who`. -/
def depositPost (σ : Storage) (who : Address) (assets : Amount ASSET WAD) : Storage :=
  let minted := mintedShares σ assets
  { σ with
    totalAssets := Amount.ofNat (Amount.toNat assets + Amount.toNat σ.totalAssets)
    totalShares := Amount.ofNat (Amount.toNat minted + Amount.toNat σ.totalShares)
    shares := Function.update σ.shares who
      (Amount.ofNat (Amount.toNat minted + Amount.toNat (σ.shares who))) }

/-- Assets `withdraw` pays. -/
def redeemedAssets (σ : Storage) (sharesIn : Amount SHARE WAD) : Amount ASSET WAD :=
  Amount.ofNat ((Amount.toNat sharesIn * Amount.toNat σ.totalAssets).div (Amount.toNat σ.totalShares))

/-- Storage after a successful `withdraw` by `who`. -/
def withdrawPost (σ : Storage) (who : Address) (sharesIn : Amount SHARE WAD)
    (assetsOut : Amount ASSET WAD) : Storage :=
  { σ with
    totalAssets := Amount.ofNat (Amount.toNat σ.totalAssets - Amount.toNat assetsOut)
    totalShares := Amount.ofNat (Amount.toNat σ.totalShares - Amount.toNat sharesIn)
    shares := Function.update σ.shares who
      (Amount.ofNat (Amount.toNat (σ.shares who) - Amount.toNat sharesIn)) }

/-! ### Views -/

theorem paused?_returns_stored :
    Tx.run paused? ctx w = .ok (w.self.paused, w) := by
  simp [paused?]

/-! ### pause -/

theorem pause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run pause ctx w =
      .ok ((), { self := { w.self with paused := Flag.on }, log := w.log ++ [.Paused] }) := by
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
theorem deposit_reverts_when_paused (assets : Amount ASSET WAD)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (deposit assets) ctx w = .error (.user .Paused) := by
  simp [deposit, hp]

/-- Zero-asset deposits revert (even when the vault is live). -/
theorem deposit_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (deposit (0 : Amount ASSET WAD)) ctx w = .error (.user .Zero) := by
  have hz : ¬ (0 : Amount ASSET WAD) < 0 := Nat.lt_irrefl 0
  simp [deposit, hp, hz]

/-- Success hypotheses for `deposit`. -/
structure DepositOk (w : World Storage Event) (assets : Amount ASSET WAD) : Prop where
  paused : w.self.paused = Flag.off
  pos : (0 : Amount ASSET WAD) < assets
  prod :
    w.self.totalShares = (0 : Amount SHARE WAD) ∨
      (w.self.totalAssets ≠ (0 : Amount ASSET WAD) ∧
        Amount.toNat assets * Amount.toNat w.self.totalShares < wordBound)
  addAssets : Amount.toNat assets + Amount.toNat w.self.totalAssets < wordBound
  addShares :
    Amount.toNat (mintedShares w.self assets) + Amount.toNat w.self.totalShares < wordBound
  addBal :
    Amount.toNat (mintedShares w.self assets) + Amount.toNat (w.self.shares ctx.sender) <
      wordBound

/-- Exact post-state of a successful `deposit`. -/
theorem deposit_ok (assets : Amount ASSET WAD) (h : DepositOk ctx w assets) :
    Tx.run (deposit assets) ctx w =
      .ok (mintedShares w.self assets,
        { self := depositPost w.self ctx.sender assets
          log := w.log ++ [.Deposit ctx.sender assets (mintedShares w.self assets)] }) := by
  rcases h with ⟨hp, hpos, hprod, haddA, haddS, haddB⟩
  simp [Amount.toNat] at haddA haddS haddB hprod
  simp [deposit, hp, hpos]
  by_cases hts : w.self.totalShares = (0 : Amount SHARE WAD)
  · simp [hts, mintedShares] at haddS haddB
    simp [hts, haddA, haddS, haddB, depositPost, mintedShares, Amount.toNat, Amount.ofNat]
  · rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (hts h0).elim
    · simp [hts, mintedShares, Amount.toNat, Amount.ofNat] at haddS haddB
      simp [hts]
      split_ifs with hta0
      · exact (hta hta0).elim
      · simp
        split_ifs
        · simp
          split_ifs
          · simp [hts, depositPost, mintedShares, Amount.toNat, Amount.ofNat]
          · contradiction
        · contradiction

/-- If the vault is solvent (`totalShares ≤ totalAssets`), minted shares never exceed assets. -/
theorem deposit_shares_le_assets_when_rate_ge_one (assets : Amount ASSET WAD)
    (hrate : w.self.totalShares ≤ w.self.totalAssets) :
    mintedShares w.self assets ≤ assets := by
  dsimp [mintedShares, Amount.toNat, Amount.ofNat]
  split_ifs with hts
  · exact Nat.le_refl _
  · have hta : 0 < Amount.toNat w.self.totalAssets := by
      have : 0 < Amount.toNat w.self.totalShares := Nat.pos_of_ne_zero hts
      exact Nat.lt_of_lt_of_le this hrate
    have hdiv : Amount.toNat assets * Amount.toNat w.self.totalAssets
        / Amount.toNat w.self.totalAssets = Amount.toNat assets := by
      simpa [Nat.mul_comm] using Nat.mul_div_right (Amount.toNat assets) hta
    exact Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hrate)) (Nat.le_of_eq hdiv)

/-- A successful deposit preserves `totalShares ≤ totalAssets` when it held before. -/
theorem deposit_preserves_rate_lower_bound (assets : Amount ASSET WAD)
    (h : DepositOk ctx w assets)
    (hrate : w.self.totalShares ≤ w.self.totalAssets) :
    ∃ minted w', Tx.run (deposit assets) ctx w = .ok (minted, w') ∧
      w'.self.totalShares ≤ w'.self.totalAssets := by
  refine ⟨_, _, deposit_ok ctx w assets h, ?_⟩
  simp [depositPost, Amount.toNat, Amount.ofNat]
  exact Nat.add_le_add
    (deposit_shares_le_assets_when_rate_ge_one w assets hrate) hrate

/-! ### withdraw -/

/-- A paused vault rejects every withdraw. -/
theorem withdraw_reverts_when_paused (sharesIn : Amount SHARE WAD)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Paused) := by
  simp [withdraw, hp]

/-- Success hypotheses for `withdraw`. -/
structure WithdrawOk (w : World Storage Event) (sharesIn : Amount SHARE WAD) : Prop where
  paused : w.self.paused = Flag.off
  pos : (0 : Amount SHARE WAD) < sharesIn
  bal : sharesIn ≤ w.self.shares ctx.sender
  supply : sharesIn ≤ w.self.totalShares
  denom : w.self.totalShares ≠ (0 : Amount SHARE WAD)
  prod : Amount.toNat sharesIn * Amount.toNat w.self.totalAssets < wordBound
  assetsFit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets

/-- Exact post-state of a successful `withdraw`. -/
theorem withdraw_ok (sharesIn : Amount SHARE WAD) (h : WithdrawOk ctx w sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      .ok (redeemedAssets w.self sharesIn,
        { self := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
          log := w.log ++ [.Withdraw ctx.sender (redeemedAssets w.self sharesIn) sharesIn] }) := by
  rcases h with ⟨hp, hpos, hbal, hsup, hden, hmul, hfit⟩
  simp [Amount.toNat] at hmul
  simp [withdraw, hp, hpos, hbal]
  split_ifs with h0
  · exact (hden h0).elim
  · simp [withdrawPost, redeemedAssets, Amount.toNat, Amount.ofNat]
    split_ifs with hle
    · rfl
    · exact (hle hfit).elim

/-- The floor never overpays: `assetsOut * totalShares ≤ sharesIn * totalAssets`. -/
theorem withdraw_assets_le_proportional (sharesIn : Amount SHARE WAD)
    (_h : WithdrawOk ctx w sharesIn) :
    Amount.toNat (redeemedAssets w.self sharesIn) * Amount.toNat w.self.totalShares ≤
      Amount.toNat sharesIn * Amount.toNat w.self.totalAssets := by
  simpa [redeemedAssets, Amount.toNat, Amount.ofNat] using
    Nat.div_mul_le_self (Amount.toNat sharesIn * Amount.toNat w.self.totalAssets)
      (Amount.toNat w.self.totalShares)

end Vault
