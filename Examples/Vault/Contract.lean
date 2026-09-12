import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20

/-!
# Vault — single-asset ERC4626-style vault

The underlying token is a bound `IERC20` (`assetB`). Share issuance and
redemption always round **down**, so leftover wei stays in the vault.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Vault

/-- Underlying ERC20. Decimals are only known on chain. -/
def vaultAsset : Asset := ⟨`vaultAsset, none⟩
/-- Vault share unit. Static 18 decimals. -/
def vShare : Asset := ⟨`vShare, some 18⟩

structure Storage where
  totalAssets : Amount vaultAsset
  totalShares : Amount vShare
  shares : Mapping Address (Amount vShare)
  paused : Flag
  owner : Address
  assetRef : Ref IERC20 vaultAsset

structure Ext where
  asset : Ghost

instance : Inhabited Ext := ⟨⟨{}⟩⟩

/-- Binding of the underlying token: address in storage, ghost in `Ext`. -/
def assetB : Binding IERC20 Storage Ext :=
  ⟨(·.assetRef.addr), (·.asset), fun x g => { x with asset := g }⟩

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

abbrev M := Tx Storage Ext Event Error

/-- Deployment: set owner, bind the asset, start unpaused. -/
def constructor (owner tok : Address) : M Unit := do
  write owner owner
  write assetRef { addr := tok }
  write paused Flag.off

/-- Deposit `assets`; mint shares 1:1 if empty, otherwise
`⌊supply · assets / totalAssets⌋`. Computes minted from pre-state `TA`/`TS`
and reverts with `ZeroShares` if that floor is 0, then pulls the asset via
`safeTransferFrom`, then updates accounting. -/
def deposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < assets) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let ta ← read totalAssets
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      pure (Amount.ofWord assets.raw)
    else
      Amount.mulDivDown ts assets ta
  Tx.require (0 < minted) .ZeroShares
  Binding.safeTransferFrom assetB who me assets .TransferFailed
  let ta' ← ta +? assets
  write totalAssets ta'
  let ts' ← minted +? ts
  write totalShares ts'
  let bal ← read shares[who]
  let bal' ← minted +? bal
  write shares[who] bal'
  Tx.emit (.Deposit who assets minted)
  pure minted

/-- Burn `sharesIn` and return `⌊totalAssets · sharesIn / totalShares⌋`.
Reverts with `ZeroAssets` if that floor is 0. Pushes the asset via
`safeTransfer` after updating accounting. -/
def withdraw (sharesIn : Amount vShare) : M (Amount vaultAsset) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  Tx.require (0 < sharesIn) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (sharesIn ≤ bal) .InsufficientShares
  let ta ← read totalAssets
  let ts ← read totalShares
  let assetsOut ← Amount.mulDivDown ta sharesIn ts
  Tx.require (0 < assetsOut) .ZeroAssets
  let bal' ← bal -? sharesIn
  write shares[who] bal'
  let ts' ← ts -? sharesIn
  write totalShares ts'
  let ta' ← ta -? assetsOut
  write totalAssets ta'
  Binding.safeTransfer assetB who assetsOut .TransferFailed
  Tx.emit (.Withdraw who assetsOut sharesIn)
  pure assetsOut

/-- View: shares `deposit` would mint (no state change, no pause check, no token pull). -/
def previewDeposit (assets : Amount vaultAsset) : M (Amount vShare) := do
  let ta ← read totalAssets
  let ts ← read totalShares
  if ts = 0 then
    pure (Amount.ofWord assets.raw)
  else
    Amount.mulDivDown ts assets ta

/-- View: assets `withdraw` would return. -/
def previewRedeem (sharesIn : Amount vShare) : M (Amount vaultAsset) := do
  let ta ← read totalAssets
  let ts ← read totalShares
  Amount.mulDivDown ta sharesIn ts

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
def badRescale (r : Rounding) (a : Word) : M Word :=
  Tx.rescale 18 6 r a

/-- Out-of-fragment: pure `Nat` addition is not an atom. -/
def badAtom (n : Nat) : M Nat := do
  let x := n + 1
  pure x

end Vault

set_option maxHeartbeats 4000000

lsc_schema Vault
lsc_reify Vault.constructor Vault.deposit Vault.withdraw Vault.previewDeposit Vault.previewRedeem
lsc_reify Vault.pause Vault.unpause Vault.paused?
lsc_contract Vault constructor deposit withdraw previewDeposit previewRedeem pause unpause paused?

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
