import Lsc.Prelude
import Lsc.Core.ContractM
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lib.Wad.Eval
import Lsc.Lang.Syntax
import Token

/-!
# `Escrow` — a cross-contract call into `Token`

`release` makes a real cross-contract call into `Token`, via `exec Token.transfer(..);`. The body
elaborates to visible `Stmt` nodes (`externalExec` inside `reentrancyGuard`) for codegen and
Checks; a separate `PairM` `def` is also emitted for the Escrow proof layer. See
[`docs/reference/ESCROW.md`](../../../docs/reference/ESCROW.md) and
[`docs/decisions/`](../../../docs/decisions/) for the full cross-contract model.

`Escrow.owner` is the one address allowed to call `release`; `Escrow.released` is a running total
of how much this `Escrow` has ever released back to the token holder (the actual balances live in
`Token`). -/

namespace Escrow

open Lsc Lsc.Compile
open Lsc.ContractM (PairM)
open Lsc.Deriving

structure EscrowStorage where
  owner : Address := 0
  /-- Denominated in `Token.Amount`, not the generic `Wad`, so passing a different token's
      amount here is a compile error rather than a silent unit mix-up. -/
  released : Token.Amount := ⟨0⟩
  deriving Repr, ContractStorage

inductive EscrowError where
  | NotOwner
  | Overflow
  | Underflow
  | Reentrant
  | ExternalCallFailed
  deriving Repr, DecidableEq, ContractError

inductive EscrowEvent where
  | Released (amount : Token.Amount)
  deriving Repr, DecidableEq, ContractEvent

-- `Escrow`'s owner releases `amount` of the token it holds back to `recipient`, by calling
-- `Token.transfer` via the cross-contract `exec` primitive. `@nonreentrant` is required on any
-- `tx` that uses `exec` (not on read-only `read` txs); it desugars to `Stmt.reentrancyGuard`.
@nonreentrant
tx release(recipient : Address, amount : Token.Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec Token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}

/-! ## DSL wiring + compilation: `ContractDSL` instance, `ContractDef` + Yul/bytecode emission -/

-- Public functions, event topics, deploy step, and the `EscrowM` monad abbreviation are all
-- inferred from the declarations above; see `derive_contract`'s docstring for defaults.
derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent

end Escrow
