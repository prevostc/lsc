import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Examples.Vault.Contract
import Stdlib.ERC20

/-!
Vault spec: `claim` is floor-rounded redeemable assets against the vault's
live token balance (`holdings`); `Auth` is the victim's own `withdraw`.
`Inv` is finite share-support. Between our transactions, `vaultRely` lets
`ext` change arbitrarily except that the vault's token balance does not fall
and the token's `totalSupply` view stays the same — that is `ClaimMonoEnv`.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-- Underlying-token balance of the vault, from the bound token's view. -/
def holdings (self : Address) (w : World Storage ExtState Event) : Nat :=
  ((w.self.asset.impl w).balanceOf self w).raw

/-- Redeemable assets of `a`. Zero when the supply is empty. Pro-rata of the
live token balance at this world. -/
def claim (self : Address) : Claim Storage ExtState Event :=
  fun a w =>
    if w.self.totalShares = 0 then 0
    else (w.self.shares a).raw * holdings self w / w.self.totalShares.raw

/-- Only a `withdraw` by `a` itself may decrease `claim a`. -/
def Auth : AuthPred spec :=
  AuthPred.ofSelf fun a c _s =>
    match c.fn, c.args with
    | .withdraw, _ => c.sender = a
    | _, _ => False

/-- Deposit is the only inflow of claim-units; it is `0` on revert. -/
def inflow (c : Call spec) (w : World Storage ExtState Event) : Nat :=
  match c.fn, c.args with
  | .deposit, assets =>
    match Tx.run (deposit assets) c.toCtx w with
    | .ok _ => assets.raw
    | .error _ => 0
  | _, _ => 0

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => (σ.shares a).raw) = σ.totalShares.raw

/-- Share balances have finite support summing to `totalShares`. -/
def Inv (w : World Storage ExtState Event) : Prop :=
  InvStorage w.self

/-- `balanceOf` / `totalSupply` selectors of the vault asset (IERC20 ABI). -/
def balSel : Nat := 0x70a08231
def supplySel : Nat := 0x18160ddd

/-- Oracle `balanceOf` of `who` at the bound token. -/
def viewBal (asset : IERC20.Ref vaultAsset) (who : Address)
    (oracle : Oracle ExtState) (x : ExtState) : Amount vaultAsset :=
  decodeOrDefault (oracle.view asset.addr balSel [AbiType.encode who] x)

/-- Oracle `totalSupply` of the bound token. -/
def viewSupply (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (x : ExtState) : Word :=
  decodeOrDefault (oracle.view asset.addr supplySel [] x)

/-- Between our transactions the outside world may change `ext` arbitrarily,
except that this vault's token balance does not decrease and the token's
`totalSupply` view stays consistent. -/
def vaultRely (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (x x' : ExtState) : Prop :=
  (viewBal asset self oracle x).raw ≤ (viewBal asset self oracle x').raw ∧
  viewSupply asset oracle x = viewSupply asset oracle x'

end Vault
