import Lsc.Lang.Derive
import Lsc.Lang.TxM
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lib.Wei.Eval

/-!
# Smoke test for the `ContractStorage`/`ContractEvent`/`ContractError`
deriving handlers + `derive_contract`

A miniature Counter-shaped contract: declares storage/error/event types
using the three `deriving` clauses from `Derive.lean`, wires them together
with `derive_contract`, and writes a small `TxM`-based function body
against the result, then evaluates it via `Stmt.eval`/`runS` to confirm
the whole pipeline (introspection-derived glue + step 1's builder monad)
actually works end-to-end.
-/

open Lsc

namespace DeriveTest

structure TStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner : Address := 0
  deriving Repr, Lsc.Deriving.ContractStorage

inductive TError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive TEvent where
  | Incremented (n : Wei)
  | Paused
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

-- ── Sanity checks on the `deriving`-generated glue (no `ContractDSL` yet) ─

#check (TStorage.getField : (t : Ty) → Ident → TStorage → Option (Val t))
#check (TStorage.setField : (t : Ty) → Ident → Val t → TStorage → TStorage)
#check (TError.resolveError : String → Option TError)
#check (TEvent.buildEvent : String → List (Sigma Val) → Option TEvent)

example (s : TStorage) : TStorage.getField Ty.wei "number" s = some (.wei s.number) := rfl
example (s : TStorage) : TStorage.getField Ty.bool "paused" s = some (.bool s.paused) := rfl
example (s : TStorage) : TStorage.getField Ty.address "owner" s = some (.addr s.owner) := rfl
example (s : TStorage) : TStorage.getField Ty.uint256 "owner" s = none := rfl

example (s : TStorage) (w : Wei) :
    TStorage.setField Ty.wei "number" (.wei w) s = { s with number := w } := rfl

example : TError.resolveError "Paused" = some .Paused := rfl
example : TError.resolveError "NotOwner" = some .NotOwner := rfl
example : TError.resolveError "Overflow" = some .Overflow := rfl
example : TError.resolveError "Bogus" = (none : Option TError) := rfl

example (n : Wei) :
    TEvent.buildEvent "Incremented" [⟨Ty.wei, .wei n⟩] = some (.Incremented n) := rfl
example : TEvent.buildEvent "Paused" [] = some .Paused := rfl

-- ── A `Syntax`-built function body against the derived storage ────────

tx incrementTx {
  require(!σ.paused) else revert Paused();
  let n = σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

-- `tx` no longer elaborates its body immediately (see `Syntax.lean`'s `tx` docstring); flush
-- the buffered body into a real `incrementTx : Stmt` def before referencing it below. This also
-- derives the `TM` abbreviation (`ContractM TStorage TEvent TError`) used just below.
derive_contract "T" TStorage TError TEvent

#check (inferInstance : ContractDSL TStorage TEvent TError)

-- `ArithError.Overflow` maps to the same-named `TError.Overflow` constructor.
example : (ContractErrors.arith (Err := TError) ArithError.Overflow) = TError.Overflow := rfl

def increment : TM Unit := Stmt.eval incrementTx

-- End-to-end check: running `increment` (a `tx { ... }`-built function body)
-- through the fully *derived* `getField`/`setField`/`resolveErr`/
-- `buildEvent`/`ContractDSL` instance on a concrete starting state
-- produces a storage update and event — confirming the whole derived
-- pipeline actually executes correctly, not just type-checks. Printed via
-- `#eval` rather than asserted via `rfl`/`decide` since `ContractState`/
-- `Except` here have no `DecidableEq` instance (not needed by the compile
-- pipeline, so none is derived).
--
-- `number` correctly ends up `1` and the emitted event carries `1` too (not
-- `2`): `n` is bound once via `Stmt.letBind` (`Syntax.lean`'s `var`) and
-- reused via `Fixed.Expr.var "n"`, which `Stmt.evalWith`'s `.letBind` case
-- computes exactly once and resolves through `LocalEnv` thereafter —
-- unaffected by the later storage write.
#eval runS increment
  { storage := ({} : TStorage), context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 } }

end DeriveTest
