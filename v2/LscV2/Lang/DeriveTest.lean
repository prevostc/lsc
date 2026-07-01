import LscV2.Lang.Derive
import LscV2.Lang.TxM
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

abbrev TM := ContractM TStorage TEvent TError

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

-- ── A `TxM`-built function body against the derived storage ────────────

def incrementTxM : TxM Unit := do
  require !(bool σ.paused) else revert Paused
  let n ← letWei "n" (wei σ.number +? 1)
  setWei "number" n
  emit "Incremented" [⟨Ty.wei, n⟩]

def incrementAst : Stmt := TxM.run incrementTxM

def increment : TM Unit := Stmt.eval incrementAst

-- `incrementAst`, built via `do`-notation over `TxM` (step 1's builder)
-- against `TStorage`'s *derived* field names, has exactly the expected
-- `Stmt` shape — confirms the builder + the `σ.field` notations work
-- against a derived storage type, not just hand-written ASTs as in
-- `TxMTest.lean`. Note `n` is bound via `letWei`/`Stmt.letBind` (computed
-- once) and referenced via `Wei.Expr.var "n"` in both the storage-set and
-- the `emit`, matching `examples/counter/src/Counter.lean`'s hand-written
-- `incrementAst` shape exactly — see `TxM.lean`'s module docstring for why
-- a plain Lean `let` would be wrong here.
example : incrementAst =
    (Stmt.require (!(CoreExpr.storageGet Ty.bool "paused")) "Paused").seq
      (((Stmt.letBind "n" ⟨Ty.wei, (Wei.Expr.storageGet "number").addCheckedNat 1⟩).seq Stmt.skip).seq
        ((Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩).seq
          (Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩]))) := by
  simp only [incrementAst, incrementTxM, TxM.run, TxM.runWith, letWei, setWei, emit, tellStmt,
    requireE, WriterT.run, MonadWriter.tell, bind, pure, Id.run, Functor.map, WriterT.mk]
  rfl

-- End-to-end check: running `increment` (a `TxM`-built function body)
-- through the fully *derived* `getField`/`setField`/`resolveErr`/
-- `buildEvent`/`ContractDSL` instance on a concrete starting state
-- produces a storage update and event — confirming the whole derived
-- pipeline actually executes correctly, not just type-checks. Printed via
-- `#eval` rather than asserted via `rfl`/`decide` since `ContractState`/
-- `Except` here have no `DecidableEq` instance (not needed by the compile
-- pipeline, so none is derived).
--
-- Fixed (previously a bug, see git history / `TxM.lean`'s module
-- docstring): `number` now correctly ends up `1` and the emitted event
-- carries `1` too (not `2`), because `n` is bound once via `letWei`
-- (a real `Stmt.letBind`) and reused via `Wei.Expr.var "n"`, which
-- `Stmt.evalWith`'s `.letBind` case computes exactly once and resolves
-- through `LocalEnv` thereafter — unaffected by the later `setWei` write.
#eval runS increment
  { storage := ({} : TStorage), context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 } }

end DeriveTest
