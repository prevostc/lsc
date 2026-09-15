import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20
import Stdlib.Shares

/-!
# Vault — single-asset ERC-4626-style vault

Binds one underlying ERC-20, mints shares on deposit and burns on withdraw.
Share conversion uses a virtual offset of `10^6` shares and 1 virtual asset
so a donation inflation attack costs on the order of `10^6` wei per wei
stolen. Pause is owner-only. External calls run after storage writes;
reentrancy is not modelled.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Vault

/-- Underlying ERC-20. Decimals are only known on chain. -/
def vaultAsset : Asset := ⟨`vaultAsset, none⟩
/-- Vault share unit. Static 18 decimals. -/
def vShare : Asset := ⟨`vShare, some 18⟩

/-- Virtual offset: `10^6` virtual shares and 1 virtual asset. -/
def offset : Shares.Offset := ⟨6⟩

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

/-- Deposit `assets` and mint floor shares against the live token balance,
using the virtual-offset conversion. -/
def deposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < assets) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  let minted ← Shares.toShares offset assets ta ts
  Tx.require (0 < minted) .ZeroShares
  write totalShares (ts +? minted)
  let bal ← read shares[who]
  write shares[who] (bal +? minted)
  safeTransferFrom tok who me assets .TransferFailed
  Tx.emit (.Deposit who assets minted)
  return minted

/-- Burn `sharesIn` and pay the floor virtual-offset conversion of the live
token balance. -/
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
  let assetsOut ← Shares.toAssets offset sharesIn ta ts
  Tx.require (0 < assetsOut) .ZeroAssets
  write shares[who] (bal -? sharesIn)
  write totalShares (ts -? sharesIn)
  safeTransfer tok who assetsOut .TransferFailed
  Tx.emit (.Withdraw who assetsOut sharesIn)
  return assetsOut

/-- Shares `deposit` would mint (no state change, no token pull). -/
def previewDeposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  Shares.toShares offset assets ta ts

/-- Assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount vShare) : M (Amount vaultAsset) := do
  let me ← Tx.selfAddress
  let tok ← read asset
  let ta ← tok.balanceOf me
  let ts ← read totalShares
  Shares.toAssets offset sharesIn ta ts

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
