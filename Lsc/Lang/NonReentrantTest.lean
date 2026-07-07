import Lsc.Lang.Derive
import Lsc.Lang.TxM
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lsc.Lib.Wei.Eval

/-!
# End-to-end tests for `@nonreentrant` + the `exec`/`read` cross-contract-call surface syntax

Exercises the *surface syntax* end-to-end: real `tx { .. }` bodies (including real,
black-box cross-contract `exec`/`read` calls into a second, genuinely different contract),
parsed and elaborated through `Lang/Syntax.lean`, proving:

(i) a `tx` marked `@nonreentrant` that uses `exec`/`read` elaborates fine
    (`Caller.callBump`/`Caller.readBump`).
(iii) a `tx` with no `exec`/`read` at all elaborates fine whether or not it is `@nonreentrant`
      — `Caller.plainBump` (undecorated, no cross-call) and `Caller.decoratedButUnused`
      (decorated, but no cross-call) both compile, confirming the decorator is a one-way
      requirement (`usesExecOrRead → nonReentrant`), never a mandate that every
      `@nonreentrant`-decorated `tx` must actually contain one.

**(ii), the rejection case, is deliberately NOT exercised here as a compiling example:** a `tx`
using `exec`/`read` without `@nonreentrant` is rejected immediately at `tx`-elaboration time
itself (`Lang/Syntax.lean`'s `tx` elaborator) — there is no way to write such a `tx` in a file
that still compiles, so this codebase has no harness for asserting a *command* itself fails to
elaborate (unlike `Lang/ChecksTest.lean`'s "expect elaboration to fail" precedent, which works at
the term level). This omission is intentional, not an oversight. -/

open Lsc

namespace Lsc.NonReentrantTest

/-! ## The callee contract: a second, genuinely different `Lsc` contract to call into. -/

namespace Callee

structure CalleeStorage where
  n : Wei := Wei.mkNat 0
  deriving Repr, Lsc.Deriving.ContractStorage

inductive CalleeError where
  | Reentrant
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive CalleeEvent where
  | Bumped
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

derive_contract_dsl CalleeStorage CalleeError CalleeEvent

tx bump {
  let m = σ.n +? 1;
  σ.n = m;
  emit Bumped();
}

derive_contract_def "Callee" CalleeStorage CalleeError CalleeEvent

end Callee

/-! ## The caller contract: real `exec`/`read` calls into `Callee`. -/

namespace Caller

structure CallerStorage where
  n : Wei := Wei.mkNat 0
  deriving Repr, Lsc.Deriving.ContractStorage

inductive CallerError where
  | Reentrant
  | ExternalCallFailed
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive CallerEvent where
  | Bumped
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

derive_contract_dsl CallerStorage CallerError CallerEvent

-- (i) Marked `@nonreentrant`, and does use `exec` — the required pairing. An ordinary
-- statement (`emit`) is included alongside the cross-call: since `exec`/`read` are fully
-- black box (no `toErr`/`toEvent` pinning `E`/`Err` the way the old `externalCall2` did), at
-- least one ordinary segment is needed in the body for Lean to resolve the caller's own
-- `S`/`E`/`Err` via its `ContractDSL` instance (see `elabOrdinarySegment`'s `(S := ..)` pin) —
-- exactly how `Escrow.release` (`examples/escrow/src/Escrow.lean`) is shaped too.
@nonreentrant
tx callBump {
  exec Callee.bump();
  emit Bumped();
}

-- (i), the read-only counterpart.
@nonreentrant
tx readBump {
  read Callee.bump();
  emit Bumped();
}

-- (iii) No `exec`/`read` at all, and (deliberately) *not* decorated — proves the decorator is
-- required only when actually needed, not mandatory on every `tx`.
tx plainBump {
  let m = σ.n +? 1;
  σ.n = m;
  emit Bumped();
}

-- (iii), the other direction: `@nonreentrant` on a `tx` with no `exec`/`read` is harmless — the
-- decorator is a one-way requirement, never a mandate that every `@nonreentrant`-decorated `tx`
-- must actually contain a cross-contract call.
@nonreentrant
tx decoratedButUnused {
  let m = σ.n +? 1;
  σ.n = m;
}

derive_contract_def "Caller" CallerStorage CallerError CallerEvent

example : (Checks.validateAll contractDef).isOk := by native_decide

end Caller

end Lsc.NonReentrantTest
