import Lsc3.Amount
import Lsc3.Reify

/-!
# Vault — single-asset ERC4626-style vault

`ASSET` and `SHARE` are phantom markers: mixing them, or mixing WAD with USDC, is a type
error. Share issuance and redemption always round **down** (`shareDown`), so leftover wei
stays in the vault.
-/

open Lsc3 Lsc3.Syntax

namespace Vault

/-- Phantom marker for the underlying asset (WAD-scaled). -/
structure ASSET where
/-- Phantom marker for vault shares (WAD-scaled). -/
structure SHARE where

structure Storage where
  totalAssets : Amount ASSET WAD
  totalShares : Amount SHARE WAD
  shares : Mapping Address (Amount SHARE WAD)
  paused : Flag
  owner : Address

inductive Event
  | Deposit (who : Address) (assets : Amount ASSET WAD) (sharesOut : Amount SHARE WAD)
  | Withdraw (who : Address) (assets : Amount ASSET WAD) (sharesIn : Amount SHARE WAD)
  | Paused
  | Unpaused
  deriving DecidableEq, Repr

inductive Error
  | Paused
  | InsufficientShares
  | NotOwner
  | Zero
  deriving DecidableEq, Repr

abbrev M := Tx Storage Event Error

/-- Deposit `assets`; mint shares 1:1 if empty, otherwise `⌊assets * supply / assets⌋`. -/
def deposit (assets : Amount ASSET WAD) : M (Amount SHARE WAD) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require ((0 : Amount ASSET WAD) < assets) .Zero
  let ta ← read totalAssets
  let ts ← read totalShares
  let minted ←
    if ts = (0 : Amount SHARE WAD) then
      pure assets
    else
      assets.shareDown ts ta
  write totalAssets (← assets +ₐ ta)
  write totalShares (← minted +ₐ ts)
  let who ← Tx.sender
  let bal ← read shares[who]
  write shares[who] (← minted +ₐ bal)
  Tx.emit (.Deposit who assets minted)
  pure minted

/-- Burn `sharesIn` and return `⌊sharesIn * totalAssets / totalShares⌋` assets. -/
def withdraw (sharesIn : Amount SHARE WAD) : M (Amount ASSET WAD) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require ((0 : Amount SHARE WAD) < sharesIn) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (sharesIn ≤ bal) .InsufficientShares
  let ta ← read totalAssets
  let ts ← read totalShares
  let assetsOut ← sharesIn.shareDown ta ts
  write shares[who] (← bal -ₐ sharesIn)
  write totalShares (← ts -ₐ sharesIn)
  write totalAssets (← ta -ₐ assetsOut)
  Tx.emit (.Withdraw who assetsOut sharesIn)
  pure assetsOut

/-- View: shares `deposit` would mint (no state change, no pause check). -/
def previewDeposit (assets : Amount ASSET WAD) : M (Amount SHARE WAD) := do
  let ta ← read totalAssets
  let ts ← read totalShares
  if ts = (0 : Amount SHARE WAD) then
    pure assets
  else
    assets.shareDown ts ta

/-- View: assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount SHARE WAD) : M (Amount ASSET WAD) := do
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
def badRescale (r : Rounding) (a : Amount ASSET WAD) : M (Amount ASSET USDC_SCALE) :=
  Amount.rescale USDC_SCALE r a

/-- Out-of-fragment: pure `Nat` addition is not an atom. -/
def badAtom (n : Nat) : M Nat := do
  let x := n + 1
  pure x

end Vault

lsc_schema Vault
lsc_reify Vault.deposit Vault.withdraw Vault.previewDeposit Vault.previewRedeem
lsc_reify Vault.pause Vault.unpause Vault.paused?

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
