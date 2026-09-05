import Lsc.Lang.Amount
import Lsc.Lang.Reify

/-!
# Vault — single-asset ERC4626-style vault

`ASSET` and `SHARE` are phantom markers: mixing them, or mixing scales, is a type error.
The underlying token is an `IERC20 ASSET assetScale` stored in `Storage.asset` — scale is a
type index (the injection), not a `decimals()` call. Share issuance and redemption always
round **down** (`shareDown`), so leftover wei stays in the vault.
-/

open Lsc Lsc.Syntax

namespace Vault

/-- Phantom marker for the underlying asset. -/
structure ASSET where
/-- Phantom marker for vault shares. -/
structure SHARE where

/-- Asset scale knob: change this (e.g. to `USDC_SCALE`) to inject a 6-decimal ERC-20. -/
def assetScale : Nat := WAD
/-- Share scale; ERC-4626 convention is 18 decimals. -/
def shareScale : Nat := WAD

structure Storage where
  totalAssets : Amount ASSET assetScale
  totalShares : Amount SHARE shareScale
  shares : Mapping Address (Amount SHARE shareScale)
  paused : Flag
  owner : Address
  asset : Address

inductive Event
  | Deposit (who : Address) (assets : Amount ASSET assetScale)
      (sharesOut : Amount SHARE shareScale)
  | Withdraw (who : Address) (assets : Amount ASSET assetScale)
      (sharesIn : Amount SHARE shareScale)
  | Paused
  | Unpaused
  deriving DecidableEq, Repr

inductive Error
  | Paused
  | InsufficientShares
  | NotOwner
  | Zero
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage Event Error

/-- Deposit `assets`; mint shares 1:1 if empty, otherwise `⌊assets * supply / assets⌋`.
Pulls the asset via `IERC20.transferFrom` before updating accounting. -/
def deposit (assets : Amount ASSET assetScale) : M (Amount SHARE shareScale) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require ((0 : Amount ASSET assetScale) < assets) .Zero
  let tok ← read asset
  let who ← Tx.sender
  let self ← Tx.selfAddress
  let ok ← IERC20.transferFrom (tok : IERC20 ASSET assetScale) who self assets
  Tx.require (ok = Flag.on) .TransferFailed
  let ta ← read totalAssets
  let ts ← read totalShares
  let minted ←
    if ts = (0 : Amount SHARE shareScale) then
      pure assets
    else
      assets.shareDown ts ta
  write totalAssets (← assets +ₐ ta)
  write totalShares (← minted +ₐ ts)
  let bal ← read shares[who]
  write shares[who] (← minted +ₐ bal)
  Tx.emit (.Deposit who assets minted)
  pure minted

/-- Burn `sharesIn` and return `⌊sharesIn * totalAssets / totalShares⌋` assets.
Pushes the asset via `IERC20.transfer` after updating accounting. -/
def withdraw (sharesIn : Amount SHARE shareScale) : M (Amount ASSET assetScale) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require ((0 : Amount SHARE shareScale) < sharesIn) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (sharesIn ≤ bal) .InsufficientShares
  let ta ← read totalAssets
  let ts ← read totalShares
  let assetsOut ← sharesIn.shareDown ta ts
  write shares[who] (← bal -ₐ sharesIn)
  write totalShares (← ts -ₐ sharesIn)
  write totalAssets (← ta -ₐ assetsOut)
  let tok ← read asset
  let ok ← IERC20.transfer (tok : IERC20 ASSET assetScale) who assetsOut
  Tx.require (ok = Flag.on) .TransferFailed
  Tx.emit (.Withdraw who assetsOut sharesIn)
  pure assetsOut

/-- View: shares `deposit` would mint (no state change, no pause check, no token pull). -/
def previewDeposit (assets : Amount ASSET assetScale) : M (Amount SHARE shareScale) := do
  let ta ← read totalAssets
  let ts ← read totalShares
  if ts = (0 : Amount SHARE shareScale) then
    pure assets
  else
    assets.shareDown ts ta

/-- View: assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount SHARE shareScale) : M (Amount ASSET assetScale) := do
  let ta ← read totalAssets
  let ts ← read totalShares
  sharesIn.shareDown ta ts

/-- Owner-only: set the pause flag. -/
def pause : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  write paused Flag.on
  Tx.emit .Paused

/-- Owner-only: clear the pause flag. -/
def unpause : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  write paused Flag.off
  Tx.emit .Unpaused

/-- Current pause flag. -/
def paused? : M Flag := read paused

/-- Out-of-fragment: `Rounding` is a parameter, not a literal. Used by `#guard_msgs` below. -/
def badRescale (r : Rounding) (a : Amount ASSET assetScale) : M (Amount ASSET USDC_SCALE) :=
  Amount.rescale USDC_SCALE r a

/-- Out-of-fragment: pure `Nat` addition is not an atom. -/
def badAtom (n : Nat) : M Nat := do
  let x := n + 1
  pure x

end Vault

lsc_schema Vault
lsc_reify Vault.deposit Vault.withdraw Vault.previewDeposit Vault.previewRedeem
lsc_reify Vault.pause Vault.unpause Vault.paused?
lsc_contract Vault deposit withdraw previewDeposit previewRedeem pause unpause paused?

/--
error: reify: rounding `r` must be a literal `.down` or `.up`
-/
#guard_msgs in
lsc_reify Vault.badRescale

/--
error: reify: `n +
  1` is not an atom; bind it first with `let x ← …` (pure Nat arithmetic is not part of the language, use `+?` or `+↻`)
-/
#guard_msgs in
lsc_reify Vault.badAtom
