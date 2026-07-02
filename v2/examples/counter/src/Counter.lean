import LscV2.Prelude
import LscV2.Compile.Yul
import LscV2.Compile.Bytecode
import LscV2.Lang.Syntax2

/-!
Counter contract written with the Lean-first DSL: storage/error/event
`deriving` clauses (`ContractStorage`/`ContractError`/`ContractEvent`) plus
the two `derive_*` assembly commands (`derive_contract_dsl`/
`derive_contract_def`) generate all boilerplate — none of it is hand-written.

Function bodies (`increment`/`pause`/`unpause`) are written in the
dss2024-style bracket-delimited `tx <name> { <stmt>* }` grammar
(`Lang/Syntax2.lean`), e.g.:

```
tx increment {
  require(!σ.paused, Paused);
  var n := σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}
```

`σ.field` reads/writes, `require(cond, ErrCtor);`/`revert(ErrCtor);`,
`emit Ctor;`/`emit Ctor(arg);`, `var x := e;`, `if (cond) { .. } else { .. }`,
and the operators `!`/`+?`/`-?`/`==`/boolean literals (`true`/`false`) are
all real `lscExpr`/`lscStmt` grammar productions, elaborated directly into
`LscV2.Stmt`/`LscV2.Expr` values — no manually-repeated field-name strings,
and error/event names are checked against `CounterError`/`CounterEvent`'s
real constructors at compile time. Each `tx <name> { .. }` block expands to
a plain top-level `def name : LscV2.Stmt := ..`, so `increment`/`pause`/
`unpause` below are ordinary `Stmt` values usable anywhere one is expected
(e.g. `derive_contract_def`'s `[("increment", increment), ..]` list).

Target shape: `docs/spec_idea_2/reference/COUNTER.md`.
-/

open LscV2 LscV2.Compile

namespace Counter

structure CounterStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner : Address := 0
  deriving Repr, LscV2.Deriving.ContractStorage

instance : Inhabited CounterStorage where
  default := {}

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, LscV2.Deriving.ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, LscV2.Deriving.ContractEvent

derive_contract_dsl CounterStorage CounterError CounterEvent

abbrev CounterM := ContractM CounterStorage CounterEvent CounterError

tx increment {
  require(!σ.paused, Paused);
  var n := σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

-- `Syntax2.lean`'s `==` elaborator pins its `CoreExpr.eqAuto` type argument to the
-- operands' shared `FieldKind`-derived `Ty` literal explicitly (rather than relying on
-- `eqAuto`'s implicit-`t` inference from the first operand), so `msg.sender == σ.owner`
-- resolves to `@CoreExpr.eqAuto Ty.address ..` here — the same annotation the old
-- hand-written version needed to add by hand to avoid a defeq-but-not-syntactic-equality
-- mismatch between `msg.sender : CoreExpr (txFieldTy .caller)` and `σ.owner : CoreExpr
-- Ty.address` (see `CoreExpr.eqAuto`'s implicit `t` argument, `Lang/TxM.lean`).
tx pause {
  require(msg.sender == σ.owner, NotOwner);
  require(!σ.paused, Paused);
  σ.paused = true;
  emit Paused;
}

tx unpause {
  require(msg.sender == σ.owner, NotOwner);
  require(σ.paused, Paused);
  σ.paused = false;
  emit Unpaused;
}

/-! ## Compilation: `ContractDef` + Yul/bytecode emission -/

/-- Compile layout for Yul / bytecode emission. -/
def stubEventTopic0 : Ident → Option Nat
  | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
  | name => some name.hash.toNat

derive_contract_def "Counter" CounterStorage CounterError CounterEvent
  ([("increment", increment), ("pause", pause), ("unpause", unpause)])
  (stubEventTopic0)
  -- Set owner = msg.sender (deployer) at construction time so pause/unpause work.
  (some (Stmt.storageSet "owner" ⟨Ty.address, CoreExpr.txField .caller⟩))

-- Smoke-checks
#check Counter.CounterStorage
#check Counter.CounterError
#check Counter.CounterEvent
#check Counter.CounterM
#check (Counter.increment : CounterM Unit)
#check (Counter.pause : CounterM Unit)
#check (Counter.unpause : CounterM Unit)
#check Counter.contractDef
#check Counter.bytecodeHex
#check Counter.deployHex

end Counter
