import Lsc3.Reify

/-!
# Token — an ERC20-style token written as plain Lean

Every function is an ordinary definition in the `Tx` monad. There is no custom grammar:
`read`/`write` are macros over the storage primitives, `+?`/`-?` are the checked
arithmetic primitives, and control flow is Lean's own `let`/`if`/`do`.
-/

open Lsc3 Lsc3.Syntax

namespace Token

structure Storage where
  owner : Address
  totalSupply : Nat
  balances : Mapping Address Nat
  allowances : Mapping Address (Mapping Address Nat)

inductive Event
  | Transfer (src to : Address) (amount : Nat)
  | Approval (owner spender : Address) (amount : Nat)
  deriving DecidableEq, Repr

inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | NotOwner
  deriving DecidableEq, Repr

abbrev M := Tx Storage Event Error

/-- Deployment: the deployer owns the whole initial supply. -/
def init (owner : Address) (supply : Nat) : M Unit := do
  write owner owner
  write totalSupply supply
  write balances[owner] supply
  Tx.emit (.Transfer 0 owner supply)

def transfer (to : Address) (amount : Nat) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write balances[src] (← b -? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer src to amount)

def approve (spender : Address) (amount : Nat) : M Unit := do
  let owner ← Tx.sender
  write allowances[owner, spender] amount
  Tx.emit (.Approval owner spender amount)

def transferFrom (src to : Address) (amount : Nat) : M Unit := do
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

def mint (to : Address) (amount : Nat) : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  let supply ← read totalSupply
  write totalSupply (← supply +? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer 0 to amount)

/-- Burn with an `if` in statement position, to exercise join points. -/
def burn (amount : Nat) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  if amount ≤ b then
    write balances[src] (← b -? amount)
    let supply ← read totalSupply
    write totalSupply (← supply -? amount)
  else
    Tx.revert .InsufficientBalance
  Tx.emit (.Transfer src 0 amount)

def balanceOf (who : Address) : M Nat := read balances[who]

def allowance (owner spender : Address) : M Nat := read allowances[owner, spender]

def totalSupply : M Nat := read totalSupply

end Token

lsc_schema Token
lsc_reify Token.init Token.transfer Token.approve Token.transferFrom Token.mint Token.burn
lsc_reify Token.balanceOf Token.allowance Token.totalSupply
