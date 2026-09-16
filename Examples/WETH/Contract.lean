import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20.Base

/-!
# WETH — wrap / unwrap the chain's native asset as an ERC-20

`deposit` mints `msg.value` to the sender. `withdraw` burns and sends
native (`Native.send`). The six IERC20 entrypoints are the ERC20 base.
The native asset comes from the `Chain` profile; this copy uses Ethereum ETH.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace WETH

/-- Ethereum profile; `native` is 18-decimal ETH. -/
def chain : Chain := .ethereum
abbrev native : Asset := Chain.native chain

structure Storage extends ERC20.Storage native
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

instance : ERC20.Events Event native := ⟨.Transfer, .Approval⟩
instance : ERC20.Errors Error := ⟨.InsufficientBalance, .InsufficientAllowance⟩

abbrev M := Tx Storage ExtState Event Error

@[reducible] def erc20 : ERC20.Fields Storage native := .ofParent toStorage

/-- Wrap: credit `msg.value` to the sender. -/
def deposit [Payable] : M Unit := do
  let who ← Tx.sender
  let v ← Tx.value
  ERC20.mint erc20 who v
  Tx.emit (.Deposit who v)

/-- Unwrap: burn and send native. Reverts on a failed transfer. -/
def withdraw (amount : Amount native) : M Unit := do
  let who ← Tx.sender
  ERC20.burn erc20 who amount
  Native.send who amount .TransferFailed
  Tx.emit (.Withdrawal who amount)

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer (to : Address) (amount : Amount native) : M Bool :=
  ERC20.transfer erc20 to amount

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve (spender : Address) (amount : Amount native) : M Bool :=
  ERC20.approve erc20 spender amount

/-- Move `amount` from `src` to `to`, spending `allowances src sender`. -/
def transferFrom (src to : Address) (amount : Amount native) : M Bool :=
  ERC20.transferFrom erc20 src to amount

/-- `who`'s wrapped balance. -/
def balanceOf (who : Address) : M (Amount native) :=
  ERC20.balanceOf erc20 who

/-- Remaining allowance of `spender` over `owner`'s tokens. -/
def allowance (owner spender : Address) : M (Amount native) :=
  ERC20.allowance erc20 owner spender

/-- Recorded total supply. -/
def totalSupply : M (Amount native) :=
  ERC20.totalSupply erc20

end WETH

lsc_schema WETH
lsc_contract WETH deposit withdraw transfer transferFrom approve
  totalSupply balanceOf allowance
  implements IERC20 WETH.native
