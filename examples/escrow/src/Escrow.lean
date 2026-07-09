import Lsc.Prelude
import Lsc.Core.ContractM
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lib.Wad.Eval
import Lsc.Lib.Interfaces.IERC20
import Lsc.Lang.Syntax

/-!
# `Escrow` — release via IERC20 interface

`release` transfers tokens held by this escrow via `exec σ.token.transfer(..);` where
`token : IERC20` holds the on-chain callee address. Proofs use `[HonestERC20 T]` — see
[`docs/reference/ESCROW.md`](../../../docs/reference/ESCROW.md). -/

namespace Escrow

open Lsc Lsc.Compile Lsc.Interfaces
open Lsc.ContractM (PairM)
open Lsc.Deriving

declare_token_amount EscrowAmount

structure EscrowStorage where
  owner : Address := 0
  released : EscrowAmount := ⟨0⟩
  token : IERC20 := default
  deriving Repr, ContractStorage

inductive EscrowError where
  | NotOwner
  | Overflow
  | Underflow
  | Reentrant
  | ExternalCallFailed
  deriving Repr, DecidableEq, ContractError

inductive EscrowEvent where
  | Released (amount : EscrowAmount)
  deriving Repr, DecidableEq, ContractEvent

@nonreentrant
tx release(recipient : Address, amount : EscrowAmount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec σ.token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}

derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent

end Escrow
