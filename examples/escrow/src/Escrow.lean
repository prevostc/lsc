import Lsc.Prelude
import Lsc.Core.ContractM
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lib.Wad.Eval
import Lsc.Lib.Interfaces.IERC20
import Lsc.Lib.Interfaces.SafeERC20
import Lsc.Lang.Syntax

/-!
# `Escrow` — release via SafeERC20-checked IERC20 transfer

`release` transfers tokens via inlined `SafeERC20.safeTransfer(σ.token, ..)` — spec-faithful
`IERC20.transfer` with `let ok` + `require`. Proofs use `[HonestERC20 T]` — see
[`docs/reference/ESCROW.md`](../../../docs/reference/ESCROW.md). -/

namespace Escrow

open Lsc Lsc.Compile Lsc.Interfaces
open Lsc.ContractM (PairM)
open Lsc.Deriving

declare_token_amount EscrowAmount

structure EscrowStorage where
  owner : Address
  released : EscrowAmount := ⟨0⟩
  token : IERC20
  deriving ContractStorage

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
  exec SafeERC20.safeTransfer(σ.token, recipient, amount);
  σ.released = σ.released +? amount;
  emit Released(amount);
}

constructor (token_ : IERC20, owner_ : Address) {
  σ.token = token_;
  σ.owner = owner_;
}

derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent

/-! ## Bytecode

`derive_contract` emits `bytecodeHex` (runtime) and `deployHex` (constructor + runtime).
Compile-time guarantees for `release` live in `test/EscrowCompileTest.lean` (IR/Yul properties).
After `lake build Escrow`, `#eval` the lines below to inspect emitted hex.
-/

example : Escrow.bytecodeHex.startsWith "0x" ∧ Escrow.bytecodeHex.length > 10 := by native_decide

#eval IO.println s!"Escrow.bytecodeHex ({Escrow.bytecodeHex.length} chars)"
#eval IO.println Escrow.bytecodeHex

end Escrow
