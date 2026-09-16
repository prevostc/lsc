import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Security.State
import Examples.Vault.Contract
import Stdlib.ERC20
import Stdlib.Shares

/-!
Vault spec: `claim` is the virtual-offset redeemable assets against the
vault's live token balance (`holdings`); `Auth` is the victim's own
`withdraw`. `Inv` is finite share-support plus
`totalShares ≤ holdings · 10^offset`. Between our transactions, `vaultRely`
lets `ext` change arbitrarily except that the vault's token balance does
not fall and the token's `totalSupply` view stays the same — that is
`ClaimMonoEnv`. Honest-counterparty (`IERC20.Spec` of the bound asset)
lives in `HasDeploy` / `HasRely` / `State`.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

abbrev AssetImpl := IERC20.Impl vaultAsset (WorldView ExtState)

/-- Live token balance of the vault at `self`, from the bound token's view. -/
def holdingsAt (self : Address) (w : World) : Amount vaultAsset :=
  w.self.asset.impl.balanceOf self w.view

/-- Nat projection of `holdingsAt`, used by internal `Inv` / `claim`. -/
def holdings (self : Address) (w : World) : Nat :=
  (holdingsAt self w).raw

/-- Assets redeemable if every outstanding share were redeemed as one blob:
`⌊totalShares · (holdings + 1) / (totalShares + 10^offset)⌋`. -/
def owedAt (self : Address) (w : World) : Amount vaultAsset :=
  ⟨Shares.toAssetsRaw offset w.self.totalShares.raw (holdings self w)
    w.self.totalShares.raw⟩

/-- Redeemable assets of `a`:
`⌊shares[a] · (holdings + 1) / (totalShares + 10^offset)⌋`. -/
def claim (self : Address) : Claim Storage ExtState Event :=
  fun a w =>
    Shares.toAssetsRaw offset (w.self.shares a).raw (holdings self w)
      w.self.totalShares.raw

/-- Only a `withdraw` by `a` itself may decrease `claim a`. -/
def Auth : AuthPred spec :=
  AuthPred.ofSelf fun a c _s =>
    match c.fn, c.args with
    | .withdraw, _ => c.sender = a
    | _, _ => False

/-- Deposit is the only inflow of claim-units; it is `0` on revert. -/
def inflow (c : Call spec) (w : World) : Nat :=
  match c.fn, c.args with
  | .deposit, assets =>
    match Tx.run (deposit assets) (c.toCtx 0) w with
    | .ok _ => assets.raw
    | .error _ => 0
  | _, _ => 0

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => (σ.shares a).raw) = σ.totalShares.raw

/-- Share balances have finite support summing to `totalShares`, and
`totalShares ≤ holdings · 10^offset` so offset claims stay covered by
holdings. -/
def Inv (self : Address) (w : World) : Prop :=
  InvStorage w.self ∧
    w.self.totalShares.raw ≤ holdings self w * Word.scale offset.decimals

/-- `balanceOf` / `totalSupply` selectors of the vault asset (IERC20 ABI). -/
def balSel : Nat := Interface.selector (I := IERC20 vaultAsset) "balanceOf"
def supplySel : Nat := Interface.selector (I := IERC20 vaultAsset) "totalSupply"

/-- Live `balanceOf` of `who` at the bound token, through `IERC20.Impl`. -/
def viewBal (asset : IERC20.Ref vaultAsset) (who : Address)
    (oracle : Oracle ExtState) (x : ExtState) : Amount vaultAsset :=
  asset.impl.balanceOf who { oracle, ext := x }

/-- Live `totalSupply` of the bound token, through `IERC20.Impl`. -/
def viewSupply (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (x : ExtState) : Word :=
  (asset.impl.totalSupply { oracle, ext := x }).raw

/-- Between our transactions the outside world may change `ext` arbitrarily,
except that this vault's token balance does not decrease and the token's
`totalSupply` view stays consistent. -/
def vaultRely (self : Address) (asset : IERC20.Ref vaultAsset)
    (oracle : Oracle ExtState) (x x' : ExtState) : Prop :=
  (viewBal asset self oracle x).raw ≤ (viewBal asset self oracle x').raw ∧
  viewSupply asset oracle x = viewSupply asset oracle x'

/-- A deployed Vault whose bound asset behaves as an ERC-20: empty shares,
unpaused, and `IERC20.Spec` of the concrete impl. -/
instance : HasDeploy spec where
  pred w :=
    w.self.paused = Flag.off ∧
    w.self.totalShares = 0 ∧
    (∀ a, w.self.shares a = 0) ∧
    IERC20.Spec (w.self.asset.impl : AssetImpl)

/-- Honest-counterparty: the declared asset ref behaves as `IERC20.Spec`
and this vault's token balance does not fall between our calls. -/
instance : HasRely spec where
  rely self w x' := vaultRely self w.self.asset w.oracle w.ext x'

/-- Amount this accepted call burned on `a`'s authority. -/
def spentCall (a : Address) (c : Call spec) : Amount vShare :=
  match c.fn, c.args with
  | .withdraw, n => if c.sender = a then n else 0
  | _, _ => 0

instance : HasSpent spec where
  asset := vShare
  spentCall := spentCall

/-- A state of a deployed Vault whose asset behaves as an ERC-20. -/
abbrev State := Lsc.Security.State spec

/-- Live token balance of this vault. -/
def State.holdings (s : State) : Amount vaultAsset :=
  holdingsAt s.addr s.w

/-- Assets redeemable by all outstanding shares, redeemed as one blob. -/
def State.owed (s : State) : Amount vaultAsset :=
  owedAt s.addr s.w

end Vault
