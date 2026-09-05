import Lsc.Lang.Amount
import Lsc.Lang.Reify
import Lsc.Stdlib.ERC20

/-!
# Vault — single-asset ERC4626-style vault

`ASSET` and `SHARE` are phantom markers. The underlying token is a bound `IERC20`
(`assetB`); its scale is an opaque type index, not a Core literal. Share issuance
and redemption always round **down** (`shareDown`), so leftover wei stays in the vault.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Vault

/-- Phantom marker for the underlying asset. -/
structure ASSET where
/-- Phantom marker for vault shares. -/
structure SHARE where

/-- Opaque scale of the underlying asset (not `WAD` by unfolding). -/
opaque assetScale : Nat
/-- Share scale; ERC-4626 convention is 18 decimals. -/
def shareScale : Nat := WAD

structure Storage where
  totalAssets : Nat
  totalShares : Nat
  shares : Mapping Address Nat
  paused : Flag
  owner : Address
  asset : IERC20.Ref
  assetDecimals : Nat

structure Ext where
  asset : Ghost

instance : Inhabited Ext := ⟨⟨{}⟩⟩

/-- Binding of the underlying token: address in storage, ghost in `Ext`. -/
def assetB : Binding IERC20 Storage Ext :=
  ⟨(·.asset), (·.asset), fun x g => { x with asset := g }⟩

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
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

/-- Deployment: set owner, bind the asset, cache `decimals`, start unpaused. -/
def constructor (owner tok : Address) : M Unit := do
  write owner owner
  write asset tok
  write paused Flag.off
  let d ← Binding.decimals assetB
  write assetDecimals d

/-- Deposit `assets`; mint shares 1:1 if empty, otherwise `⌊supply * assets / totalAssets⌋`.
Pulls the asset via `transferFrom` before updating accounting. Storage words are `Nat`
(`Amount` fields make multi-step `rfl` certificates time out). -/
def deposit (assets : Amount ASSET assetScale) : M Nat := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < assets.toNat) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let _ ← Binding.transferFrom assetB who me assets.toNat
  let ta ← read totalAssets
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      pure assets.toNat
    else
      Tx.mulDivDown ts assets.toNat ta
  let ta' ← ta +? assets.toNat
  write totalAssets ta'
  let ts' ← minted +? ts
  write totalShares ts'
  let bal ← read shares[who]
  let bal' ← minted +? bal
  write shares[who] bal'
  Tx.emit (.Deposit who assets (Amount.ofNat minted))
  pure minted

/-- Burn `sharesIn` and return `⌊totalAssets * sharesIn / totalShares⌋` as a word.
Pushes the asset via `transfer` after updating accounting. -/
def withdraw (sharesIn : Amount SHARE shareScale) : M Nat := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < sharesIn.toNat) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (sharesIn.toNat ≤ bal) .InsufficientShares
  let ta ← read totalAssets
  let ts ← read totalShares
  let assetsOut ← Tx.mulDivDown ta sharesIn.toNat ts
  let bal' ← bal -? sharesIn.toNat
  write shares[who] bal'
  let ts' ← ts -? sharesIn.toNat
  write totalShares ts'
  let ta' ← ta -? assetsOut
  write totalAssets ta'
  let _ ← Binding.transfer assetB who assetsOut
  Tx.emit (.Withdraw who (Amount.ofNat assetsOut) sharesIn)
  pure assetsOut

/-- View: shares `deposit` would mint (no state change, no pause check, no token pull). -/
def previewDeposit (assets : Amount ASSET assetScale) : M Nat := do
  let ta ← read totalAssets
  let ts ← read totalShares
  if ts = 0 then
    pure assets.toNat
  else
    Tx.mulDivDown ts assets.toNat ta

/-- View: assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount SHARE shareScale) : M Nat := do
  let ta ← read totalAssets
  let ts ← read totalShares
  Tx.mulDivDown ta sharesIn.toNat ts

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

/-- Cached asset `decimals` (set at construction). -/
def decimals : M Nat := read assetDecimals

/-- Out-of-fragment: `Rounding` is a parameter, not a literal. Used by `#guard_msgs` below. -/
def badRescale (r : Rounding) (a : Amount ASSET assetScale) : M (Amount ASSET USDC_SCALE) :=
  Amount.rescale assetScale USDC_SCALE r a

/-- Out-of-fragment: pure `Nat` addition is not an atom. -/
def badAtom (n : Nat) : M Nat := do
  let x := n + 1
  pure x

end Vault

set_option maxHeartbeats 800000

lsc_schema Vault
lsc_reify Vault.constructor Vault.deposit Vault.withdraw Vault.previewDeposit Vault.previewRedeem
lsc_reify Vault.pause Vault.unpause Vault.paused? Vault.decimals
lsc_contract Vault constructor deposit withdraw previewDeposit previewRedeem pause unpause paused? decimals

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
