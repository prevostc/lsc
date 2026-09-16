import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20

/-!
# WNative — wrap / unwrap the chain's native asset as an ERC-20

`deposit` credits `msg.value` to the sender. `withdraw` burns and sends
native (`Native.send`). Transfers match Token. Compiled for Ethereum ETH.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace WNative

/-- Ethereum profile; `native` is 18-decimal ETH. -/
def chain : Chain := .ethereum
abbrev native : Asset := Chain.native chain

structure Storage where
  balances    : Mapping Address (Amount native)
  allowances  : Mapping Address (Mapping Address (Amount native))
  totalSupply : Amount native
  deriving Fields

open Storage.Fields

inductive Event
  | Deposit (who : Address) (amount : Amount native)
  | Withdrawal (who : Address) (amount : Amount native)
  | Transfer (src to : Address) (amount : Amount native)
  | Approval (owner spender : Address) (amount : Amount native)
  deriving DecidableEq, Repr

inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

/-- Wrap: credit `msg.value` to the sender. -/
def deposit [Payable] : M Unit := do
  let who ← Tx.sender
  let v : Amount native ← Tx.value
  write balances[who] (read balances[who] +? v)
  write totalSupply (read totalSupply +? v)
  Tx.emit (.Deposit who v)

/-- Unwrap: burn and send native. Reverts on a failed transfer. -/
def withdraw (amount : Amount native) : M Unit := do
  let who ← Tx.sender
  write balances[who] (read balances[who] -? amount)
  write totalSupply (read totalSupply -? amount)
  Native.send who amount .TransferFailed
  Tx.emit (.Withdrawal who amount)

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer (to : Address) (amount : Amount native) : M Bool := do
  let src ← Tx.sender
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write balances[src] (b -? amount)
  write balances[to] (read balances[to] +? amount)
  Tx.emit (.Transfer src to amount)
  return true

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve (spender : Address) (amount : Amount native) : M Bool := do
  let owner ← Tx.sender
  write allowances[owner, spender] amount
  Tx.emit (.Approval owner spender amount)
  return true

/-- Move `amount` from `src` to `to`, spending `allowances src sender`. -/
def transferFrom (src to : Address) (amount : Amount native) : M Bool := do
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

/-- `who`'s wrapped balance. -/
def balanceOf (who : Address) : M (Amount native) := read balances[who]

/-- Remaining allowance of `spender` over `owner`'s tokens. -/
def allowance (owner spender : Address) : M (Amount native) :=
  read allowances[owner, spender]

/-- Recorded total supply. -/
def totalSupply : M (Amount native) := read totalSupply

end WNative

lsc_schema WNative
lsc_reify WNative.deposit
lsc_reify WNative.withdraw
lsc_reify WNative.transfer
lsc_reify WNative.transferFrom
lsc_reify WNative.approve
lsc_reify WNative.totalSupply
lsc_reify WNative.balanceOf
lsc_reify WNative.allowance
lsc_contract WNative deposit withdraw transfer transferFrom approve
  totalSupply balanceOf allowance
  implements IERC20 WNative.native
