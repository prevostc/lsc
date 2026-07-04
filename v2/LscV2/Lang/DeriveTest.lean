import LscV2.Lang.Derive
import LscV2.Lang.TxM
import LscV2.Lang.Syntax
import LscV2.Lang.Eval
import LscV2.Lib.Wei.Eval

/-!
# Smoke test for the `ContractStorage`/`ContractEvent`/`ContractError`
deriving handlers + `derive_contract_dsl`

A miniature Counter-shaped contract: declares storage/error/event types
using the three `deriving` clauses from `Derive.lean`, wires them together
with `derive_contract_dsl`, and writes a small `TxM`-based function body
against the result, then evaluates it via `Stmt.eval`/`runS` to confirm
the whole pipeline (introspection-derived glue + step 1's builder monad)
actually works end-to-end.
-/

open LscV2

namespace DeriveTest

structure TStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner : Address := 0
  deriving Repr, LscV2.Deriving.ContractStorage

instance : Inhabited TStorage where
  default := {}

inductive TError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, LscV2.Deriving.ContractError

inductive TEvent where
  | Incremented (n : Wei)
  | Paused
  deriving Repr, DecidableEq, LscV2.Deriving.ContractEvent

derive_contract_dsl TStorage TError TEvent

-- ── Sanity checks on the derived glue ───────────────────────────────────

#check (TStorage.getField : (t : Ty) → Ident → TStorage → Option (Val t))
#check (TStorage.setField : (t : Ty) → Ident → Val t → TStorage → TStorage)
#check (TError.resolveError : String → Option TError)
#check (TEvent.buildEvent : String → List (Sigma Val) → Option TEvent)
#check (inferInstance : ContractDSL TStorage TEvent TError)

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

-- `ArithError.Overflow` maps to the same-named `TError.Overflow` constructor.
example : (ContractErrors.arith (Err := TError) ArithError.Overflow) = TError.Overflow := rfl

-- ── A `Syntax`-built function body against the derived storage ────────

tx incrementTx {
  require(!σ.paused) else revert Paused();
  let n = σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

-- `tx` no longer elaborates its body immediately (see `Syntax.lean`'s `tx` docstring); flush
-- the buffered body into a real `incrementTx : Stmt` def before referencing it below. This also
-- derives the `TM` abbreviation (`ContractM TStorage TEvent TError`) used just below — the extra
-- `contractDef`/`config`/`bytecodeHex`/`deployHex` defs `derive_contract_def` also emits are
-- simply unused here.
derive_contract_def "T" TStorage TError TEvent

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
-- reused via `Wei.Expr.var "n"`, which `Stmt.evalWith`'s `.letBind` case
-- computes exactly once and resolves through `LocalEnv` thereafter —
-- unaffected by the later storage write.
#eval runS increment
  { storage := ({} : TStorage), context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 } }

end DeriveTest
