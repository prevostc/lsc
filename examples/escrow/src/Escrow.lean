import Lsc.Prelude
import Lsc.Core.ContractM
import Lsc.Lib.Wad.Eval
import Lsc.Lang.Syntax
import Token

/-!
# `Escrow` — a real, black-box cross-contract call into `Token`

**Scope note (see `docs/reference/ESCROW.md`, and `Lsc/Core/ContractM.lean`'s `PairM` section
docstring for the full design):** `release` below is the one function in this codebase that
makes a genuine cross-contract call, using `Lsc.ContractM.PairM`/`PairM.exec`
(`Lsc/Core/ContractM.lean`) — authored through real `tx { .. }` surface syntax
(`exec Token.transfer(recipient, amount);`, below), not a hand-written `PairM` `do`-block.
Because `PairM` threads an explicit *pair* of concrete storage types (`EscrowStorage`,
`Token.TokenStorage`) rather than a single `S`, `release`'s whole `tx` body elaborates to a
`PairM EscrowStorage Token.TokenStorage EscrowEvent EscrowError Unit`-valued `def`, not the
usual `Lsc.Stmt`-valued one every other `tx` in this codebase produces — see `lscExec`'s
docstring for exactly how, and this codebase's compile pipeline (`Lsc/Compile/*`) still has no
representation for a second contract's storage type at all, so `release` is deliberately *not*
part of `Escrow`'s `ContractDef`/bytecode/Yul output — real EVM `CALL` codegen for this remains a
documented follow-up. Its Lean-level semantics/evaluation are real regardless: it genuinely
threads and updates *both* contracts' storage, is fully executable, and is proved correct below
(`examples/escrow/test/EscrowTheorem.lean`) — nothing about this is a stub.

**Fully decoupled from `Token`'s internals.** `exec`/`read` are black box (see `PairM.exec`'s
docstring): `Escrow` never needs to know `Token`'s real `TokenError`/`TokenEvent` types at all —
no `toErr`/`toEvent` conversion functions, no `TokenNotified` event wrapper folding `Token`'s
events into `Escrow`'s own log. `Escrow` is therefore a fully DSL-representable contract (every
field/constructor is one of `Ty`'s five kinds), needing no hand-written `ContractDSL` glue —
plain `deriving ContractStorage`/`ContractError`/`ContractEvent` are enough (see those handlers'
docstrings, `Lsc/Lang/Derive.lean`).

`Escrow.owner` is the one address allowed to call `release`; `Escrow.released` is a running
total of how much this `Escrow` has ever released back to the token holder (purely
informational bookkeeping on the `Escrow` side — the actual balances live in `Token`). -/

namespace Escrow

open Lsc
open Lsc.ContractM (PairM)
open Lsc.Deriving

structure EscrowStorage where
  owner : Address := 0
  /-- Typed `Token.Amount`, not the generic `Wad` — `Escrow` is specifically written to wrap
      `Token` (`T := Token.TokenStorage` throughout this file), so its own running total should
      be denominated in *that token's* declared unit. Since `Token.Amount` is currently `Fixed
      18` (same as `Wad`), this is today a documentation-only distinction — but it is what makes
      wiring `Escrow` against a hypothetical future, genuinely different-decimals token (e.g. a
      6-decimals one) a compile error instead of a silent unit mismatch: `released`'s type and
      `release`'s `amount` parameter (below) both come from `Token.Amount` directly, so they can
      never silently drift from whatever `Token` itself declares. -/
  released : Token.Amount := ⟨0⟩
  deriving Repr, ContractStorage

inductive EscrowError where
  | NotOwner
  | Overflow
  | Underflow
  | Reentrant
  | ExternalCallFailed
  deriving Repr, DecidableEq, ContractError

/-- Only `Released` — a plain, fully DSL-representable event (no foreign `Token.TokenEvent`
payload; see the module docstring on why the black-box `exec`/`read` model makes that
unnecessary). -/
inductive EscrowEvent where
  | Released (amount : Token.Amount)
  deriving Repr, DecidableEq, ContractEvent

abbrev EscrowM := ContractM EscrowStorage EscrowEvent EscrowError

derive_contract_dsl EscrowStorage EscrowError EscrowEvent

-- `release amount` — the real cross-contract call: `Escrow`'s owner asks it to release
-- `amount` of the token it holds in escrow back to the token holder, by actually invoking
-- `Token.transfer` on `Token`'s own storage via the black-box `exec` primitive.
--
-- Surface syntax: `exec Token.transfer(recipient, amount);` — names the target contract's
-- tx-derived function directly (dotted `Token.transfer`, lexed as one token exactly like
-- `σ.field`/`msg.sender`), with plain identifiers as its arguments (real Lean values — `tx`
-- parameters/locals, not `lscExpr` AST nodes; see `lscExec`'s docstring for why arguments are
-- bare names only). `T`/`ET`/`ErrT` (`Token`'s storage/event/error types) are never named in
-- the `tx` body at all — inferred purely by Lean unification. No `toErr`/`toEvent` conversion
-- functions are needed: on failure, `release` only ever observes the opaque
-- `EscrowError.ExternalCallFailed` (via `ContractErrors.fromFramework`), never `Token`'s real
-- error; `Token`'s events during the call are not folded into `Escrow`'s own log either.
--
-- Because this `tx`'s body contains `exec`, `Lsc.Syntax.stmtsUseExecOrRead`'s scan (run by
-- `tx`'s own elaborator, *before* any elaboration) detects it and (a) requires `@nonreentrant`
-- immediately, right there, since a cross-contract `tx` is never added to
-- `ContractDef.functions` at all (see `Lsc.Deriving.contractCrossCallExt`'s docstring), and (b)
-- elaborates the *whole* body directly to a `PairM EscrowStorage Token.TokenStorage EscrowEvent
-- EscrowError Unit`-valued `def`, not the usual `Lsc.Stmt`-valued one, via
-- `Lsc.Syntax.elabStmtListPairM`. The non-reentrancy property that matters most here — a
-- hostile `Token` cannot call back into `Escrow` — still holds *structurally*, by
-- `Token.transfer`'s type having no way to mention `EscrowStorage` or `PairM` at all (see
-- `Lsc.ContractM.PairM`'s docstring and `EscrowTheorem.lean`'s
-- `release_rejects_when_already_locked` for the one residual case `exec`'s `locked` guard
-- still covers).
@nonreentrant
tx release(recipient : Address, amount : Token.Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec Token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}

flush_contract_txs

end Escrow
