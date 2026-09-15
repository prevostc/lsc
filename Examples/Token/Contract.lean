import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20

/-!
# Token — a closed ERC-20

`transfer`, `approve`, `transferFrom`, owner-only `mint`, `burn`, and the
views `totalSupply` / `balanceOf` / `allowance`. No external calls. Nested
`allowances` is a two-key mapping. Self-spend still requires and decrements
allowance.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Token

/-- This contract's token. Decimals are not static. -/
def tokenAsset : Asset := ⟨`tokenAsset, none⟩

structure Storage where
  owner : Address
  totalSupply : Amount tokenAsset
  balances : Mapping Address (Amount tokenAsset)
  allowances : Mapping Address (Mapping Address (Amount tokenAsset))

inductive Event
  | Transfer (src to : Address) (amount : Amount tokenAsset)
  | Approval (owner spender : Address) (amount : Amount tokenAsset)
  deriving DecidableEq, Repr

inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | NotOwner
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

/-- Deployment: the deployer owns the whole initial supply. -/
def constructor (owner : Address) (supply : Amount tokenAsset) : M Unit := do
  write owner owner
  write totalSupply supply
  write balances[owner] supply
  Tx.emit (.Transfer 0 owner supply)

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer (to : Address) (amount : Amount tokenAsset) : M Bool := do
  let src ← Tx.sender
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write balances[src] (b -? amount)
  write balances[to] (read balances[to] +? amount)
  Tx.emit (.Transfer src to amount)
  return true

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve (spender : Address) (amount : Amount tokenAsset) : M Bool := do
  let owner ← Tx.sender
  write allowances[owner, spender] amount
  Tx.emit (.Approval owner spender amount)
  return true

/-- Move `amount` from `src` to `to`, spending `allowances src sender`.
Self-spend still requires and decrements that allowance. -/
def transferFrom (src to : Address) (amount : Amount tokenAsset) : M Bool := do
  let spender ← Tx.sender
  let a ← read allowances[src, spender]
  Tx.require (amount ≤ a) .InsufficientAllowance
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write allowances[src, spender] (a -? amount)
  write balances[src] (b -? amount)
  write balances[to] (read balances[to] +? amount)
  Tx.emit (.Transfer src to amount)
  return true

/-- Owner-only: mint `amount` to `to`. -/
def mint (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  write totalSupply (read totalSupply +? amount)
  write balances[to] (read balances[to] +? amount)
  Tx.emit (.Transfer 0 to amount)

/-- Burn `amount` from the sender. -/
def burn (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  if amount ≤ b then
    write balances[src] (b -? amount)
    write totalSupply (read totalSupply -? amount)
  else
    Tx.revert .InsufficientBalance
  Tx.emit (.Transfer src 0 amount)

/-- `who`'s token balance. -/
def balanceOf (who : Address) : M (Amount tokenAsset) := read balances[who]

/-- Remaining allowance of `spender` over `owner`'s tokens. -/
def allowance (owner spender : Address) : M (Amount tokenAsset) :=
  read allowances[owner, spender]

/-- Recorded total supply. -/
def totalSupply : M (Amount tokenAsset) := read totalSupply

end Token

lsc_schema Token
lsc_contract Token constructor transfer transferFrom approve totalSupply
  balanceOf allowance mint burn
  implements IERC20 Token.tokenAsset
