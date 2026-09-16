import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20.Base

/-!
# Token — a closed ERC-20

`transfer`, `approve`, `transferFrom`, owner-only `mint`, `burn`, and the
views `totalSupply` / `balanceOf` / `allowance`. No external calls. The six
IERC20 entrypoints are the ERC20 base. Self-spend still requires and
decrements allowance.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Token

/-- This contract's token. Decimals are not static. -/
def tokenAsset : Asset := ⟨`tokenAsset, none⟩

structure Storage extends ERC20.Storage tokenAsset where
  owner : Address
  deriving Fields, Inhabited

open Storage.Fields

inductive Event
  | Transfer (src to : Address) (amount : Amount tokenAsset)
  | Approval (owner spender : Address) (amount : Amount tokenAsset)
  deriving DecidableEq, Repr

inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | NotOwner
  deriving DecidableEq, Repr

instance : ERC20.Events Event tokenAsset := ⟨.Transfer, .Approval⟩
instance : ERC20.Errors Error := ⟨.InsufficientBalance, .InsufficientAllowance⟩

abbrev M := Tx Storage ExtState Event Error

@[reducible] def base : ERC20.Fields Storage tokenAsset := .ofParent toStorage

/-- Deployment: the deployer owns the whole initial supply. -/
def constructor (owner : Address) (supply : Amount tokenAsset) : M Unit := do
  write owner owner
  ERC20.mint base owner supply

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer (to : Address) (amount : Amount tokenAsset) : M Bool :=
  ERC20.transfer base to amount

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve (spender : Address) (amount : Amount tokenAsset) : M Bool :=
  ERC20.approve base spender amount

/-- Move `amount` from `src` to `to`, spending `allowances src sender`.
Self-spend still requires and decrements that allowance. -/
def transferFrom (src to : Address) (amount : Amount tokenAsset) : M Bool :=
  ERC20.transferFrom base src to amount

/-- Owner-only: mint `amount` to `to`. -/
def mint (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  ERC20.mint base to amount

/-- Burn `amount` from the sender. -/
def burn (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  ERC20.burn base src amount

/-- `who`'s token balance. -/
def balanceOf (who : Address) : M (Amount tokenAsset) :=
  ERC20.balanceOf base who

/-- Remaining allowance of `spender` over `owner`'s tokens. -/
def allowance (owner spender : Address) : M (Amount tokenAsset) :=
  ERC20.allowance base owner spender

/-- Recorded total supply. -/
def totalSupply : M (Amount tokenAsset) :=
  ERC20.totalSupply base

end Token

lsc_schema Token
lsc_contract Token constructor transfer transferFrom approve totalSupply
  balanceOf allowance mint burn
  implements IERC20 Token.tokenAsset
