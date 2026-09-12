import Lsc.Lang.Word
import Lsc.Lang.Reify

/-!
# Token — an ERC20-style token written as plain Lean

Every function is an ordinary definition in the `Tx` monad. There is no custom grammar:
`read`/`write` are macros over the storage primitives, `+?`/`-?` are the checked
arithmetic primitives, and control flow is Lean's own `let`/`if`/`do`.
-/

open Lsc Lsc.Syntax

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

abbrev M := Tx Storage Unit Event Error

/-- Deployment: the deployer owns the whole initial supply. -/
def constructor (owner : Address) (supply : Amount tokenAsset) : M Unit := do
  write owner owner
  write totalSupply supply
  write balances[owner] supply
  Tx.emit (.Transfer 0 owner supply)

def transfer (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write balances[src] (← b -? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer src to amount)

def approve (spender : Address) (amount : Amount tokenAsset) : M Unit := do
  let owner ← Tx.sender
  write allowances[owner, spender] amount
  Tx.emit (.Approval owner spender amount)

def transferFrom (src to : Address) (amount : Amount tokenAsset) : M Unit := do
  let spender ← Tx.sender
  let a ← read allowances[src, spender]
  Tx.require (amount ≤ a) .InsufficientAllowance
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write allowances[src, spender] (← a -? amount)
  write balances[src] (← b -? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer src to amount)

def mint (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  let supply ← read totalSupply
  write totalSupply (← supply +? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer 0 to amount)

/-- Burn with an `if` in statement position, to exercise join points. -/
def burn (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  if amount ≤ b then
    write balances[src] (← b -? amount)
    let supply ← read totalSupply
    write totalSupply (← supply -? amount)
  else
    Tx.revert .InsufficientBalance
  Tx.emit (.Transfer src 0 amount)

def balanceOf (who : Address) : M (Amount tokenAsset) := read balances[who]

def allowance (owner spender : Address) : M (Amount tokenAsset) :=
  read allowances[owner, spender]

def totalSupply : M (Amount tokenAsset) := read totalSupply

end Token

lsc_schema Token
lsc_reify Token.constructor Token.transfer Token.approve Token.transferFrom Token.mint Token.burn
lsc_reify Token.balanceOf Token.allowance Token.totalSupply
lsc_contract Token constructor transfer approve transferFrom mint burn balanceOf allowance totalSupply
