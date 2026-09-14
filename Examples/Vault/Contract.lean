import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20

/-!
# Vault — single-asset ERC-4626-style vault

Binds one underlying ERC-20, mints shares on deposit and burns on withdraw.
The first mint is 1:1; later mints and redeems round down. Pause is
owner-only. External calls run after storage writes; reentrancy is not
modelled.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Vault

/-- Underlying ERC-20. Decimals are only known on chain. -/
def vaultAsset : Asset := ⟨`vaultAsset, none⟩
/-- Vault share unit. Static 18 decimals. -/
def vShare : Asset := ⟨`vShare, some 18⟩

structure Storage where
  asset : Ref (IERC20 vaultAsset)
  owner : Address
  paused : Flag
  totalShares : Amount vShare
  shares : Mapping Address (Amount vShare)

inductive Event
  | Deposit (who : Address) (assets : Amount vaultAsset)
      (sharesOut : Amount vShare)
  | Withdraw (who : Address) (assets : Amount vaultAsset)
      (sharesIn : Amount vShare)
  | Paused
  | Unpaused
  deriving DecidableEq, Repr

inductive Error
  | Paused
  | InsufficientShares
  | NotOwner
  | Zero
  | ZeroShares
  | ZeroAssets
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

/-- Deployment: set owner, bind the asset, start unpaused. -/
def constructor (owner tok : Address) : M Unit := do
  write owner owner
  write asset { addr := tok }
  write paused Flag.off

/-- Deposit `assets` and mint floor-pro-rata shares against the live token
balance (1:1 if empty). -/
def deposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < assets) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      assets.as vShare
    else
      ts mulDiv↓ assets / ta
  Tx.require (0 < minted) .ZeroShares
  let ts' ← ts +? minted
  write totalShares ts'
  let bal ← read shares[who]
  let bal' ← bal +? minted
  write shares[who] bal'
  safeTransferFrom tok who me assets .TransferFailed
  Tx.emit (.Deposit who assets minted)
  return minted

/-- Burn `sharesIn` and pay the floor-pro-rata of the live token balance. -/
def withdraw (sharesIn : Amount vShare) : M (Amount vaultAsset) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < sharesIn) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (sharesIn ≤ bal) .InsufficientShares
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  let assetsOut ← ta mulDiv↓ sharesIn / ts
  Tx.require (0 < assetsOut) .ZeroAssets
  let bal' ← bal -? sharesIn
  write shares[who] bal'
  let ts' ← ts -? sharesIn
  write totalShares ts'
  safeTransfer tok who assetsOut .TransferFailed
  Tx.emit (.Withdraw who assetsOut sharesIn)
  return assetsOut

/-- Shares `deposit` would mint (no state change, no token pull). -/
def previewDeposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  if ts = 0 then
    assets.as vShare
  else
    ts mulDiv↓ assets / ta

/-- Assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount vShare) : M (Amount vaultAsset) := do
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  ta mulDiv↓ sharesIn / ts

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

/-- Whether the vault is paused. -/
def isPaused : M Flag := read paused

end Vault

set_option maxHeartbeats 20000000

lsc_schema Vault
lsc_contract Vault constructor deposit withdraw previewDeposit previewRedeem
  pause unpause isPaused
