import Lsc.Lang.Derive
import Lsc.Lang.TxM
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lsc.Lib.Wei.Eval

/-!
# End-to-end tests for `@nonreentrant` + the `exec`/`read` cross-contract-call surface syntax

Exercises the surface syntax end-to-end: real `tx { .. }` bodies parsed and elaborated through
`Lang/Syntax.lean` into visible `Stmt` nodes (`externalExec`/`externalRead`/`reentrancyGuard`).

- `callBump`: `@nonreentrant` + `exec` (required pairing) → `reentrancyGuard` + `externalCall`
- `readBump`: `read` only, no `@nonreentrant` (read-only txs are exempt)
- `plainBump` / `decoratedButUnused`: decorator is one-way (`usesExec → nonReentrant`)
-/

open Lsc

namespace Lsc.NonReentrantTest

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

tx bump {
  let m = σ.n +? 1;
  σ.n = m;
  emit Bumped();
}

view getN : Wei {
  return σ.n;
}

derive_contract "Callee" CalleeStorage CalleeError CalleeEvent

end Callee

namespace Caller

structure CallerStorage where
  n : Wei := Wei.mkNat 0
  callee : Address := default
  deriving Repr, Lsc.Deriving.ContractStorage

inductive CallerError where
  | Reentrant
  | ExternalCallFailed
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive CallerEvent where
  | Bumped
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

@nonreentrant
tx callBump {
  exec Callee.bump();
  emit Bumped();
}

-- `read` is exempt from `@nonreentrant` and from `reentrancyGuard`.
tx readBump {
  read Callee.getN();
  emit Bumped();
}

tx plainBump {
  let m = σ.n +? 1;
  σ.n = m;
  emit Bumped();
}

@nonreentrant
tx decoratedButUnused {
  let m = σ.n +? 1;
  σ.n = m;
}

derive_contract "Caller" CallerStorage CallerError CallerEvent

example : (Checks.validateAll contractDef).isOk := by native_decide

end Caller

end Lsc.NonReentrantTest
