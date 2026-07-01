# Reference: Pausable Counter

Canonical minimal reference contract. Every framework feature should be exercised here before attempting DeFi contracts.

Full design context: [DESIGN.md §13](../DESIGN.md). Implementation walkthrough: [IMPLEMENTATION.md Step 11](../IMPLEMENTATION.md).

## Contract

Surface syntax follows the actual implementation in [IMPLEMENTATION.md](../IMPLEMENTATION.md) §6–§7 (`TxM` builder monad + `deriving ContractStorage/ContractError/ContractEvent` + `derive_contract_dsl`) — full source: `v2/examples/counter/src/Counter.lean`.

```lean
structure CounterStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner  : Address := 0
  deriving Repr, LscV2.Deriving.ContractStorage

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

def incrementTxM : TxM Unit := do
  require !(bool σ.paused) else revert Paused
  let n ← letWei "n" (wei σ.number +? 1)
  setWei "number" n
  emit "Incremented" [⟨Ty.wei, n⟩]

def increment : CounterM Unit := Stmt.eval (TxM.run incrementTxM)

def pauseTxM : TxM Unit := do
  require (@CoreExpr.eqAuto Ty.address msg.sender (addr σ.owner)) else revert NotOwner
  require !(bool σ.paused) else revert Paused
  setBool "paused" (CoreExpr.lit Ty.bool (.bool true))
  emit "Paused" []

def pause : CounterM Unit := Stmt.eval (TxM.run pauseTxM)

def unpauseTxM : TxM Unit := do
  require (@CoreExpr.eqAuto Ty.address msg.sender (addr σ.owner)) else revert NotOwner
  require (bool σ.paused) else revert Paused
  setBool "paused" (CoreExpr.lit Ty.bool (.bool false))
  emit "Unpaused" []

def unpause : CounterM Unit := Stmt.eval (TxM.run unpauseTxM)
```

`number` is `Wei` — the 0-decimal numeric type (like `Wad`/`Ray` but with identity encoding: `1 Wei = 1`). Bare `UInt256` cannot be used for arithmetic in contract bodies; all numeric ops go through typed wrappers (`Wei`, `Wad`, `Ray`). Storage reads use the type-tagged `wei σ.field`/`bool σ.field`/`addr σ.field`/`u256 σ.field` notation family (not a single generic `σ.field`); storage writes are plain function calls (`setWei`/`setBool`/…), not `σ.field := e` sugar — see `IMPLEMENTATION.md` §6 for why. `n` is bound via `letWei` rather than a plain `let` because it's reused (in both `setWei` and `emit`) after a storage write — a plain `let` would silently re-evaluate against the *post-write* storage; see `IMPLEMENTATION.md` §6 / `TxM.lean`'s module docstring.

Overflow on `+? 1` reverts as `.error CounterError.Overflow` via `deriving ContractError`'s generated `ContractErrors.arith` (`ArithError.Overflow` → `Overflow`, by name-matching), with the actual loud-failure guarantee enforced separately by `Lang.Checks.checkArithErrorCoverage` once all function bodies are known (see `DESIGN.md` §3.2). Counter does not declare `Underflow` or `DivisionByZero` because the body uses only `+?`; adding `-?` or `/?` would require those variants on `CounterError`.


## Required theorems

Each must be provable with `simp` + `omega` in at most ~5 lines:

| Theorem | Technique |
|---------|-----------|
| `increment_increases_number_when_not_paused` | `simp` + `omega` |
| `increment_errors_when_paused` | `simp` (error case) |
| `increment_does_not_change_paused` | `rfl` / struct update |
| `increment_does_not_change_owner` | `rfl` |
| `increment_emits_incremented` | `simp` on event log |
| `pause_sets_paused_when_owner` | `simp` |
| `pause_errors_when_not_owner` | `simp` |
| `pause_errors_when_already_paused` | `simp` |
| `unpause_clears_paused_when_owner` | `simp` |

Proof hypotheses use `s.storage.field` on `ContractState` snapshots — not `σ.field` (the `σ.field` family is source-level notation for *building* a function body's `Stmt`; theorem statements and proofs work directly with `ContractState`/`runS`). The 9 theorems are proved in `test/CounterTheorem.lean` against `Counter.lean`, zero `sorry`s, via `simp` unfolding `Stmt.eval`/`ContractM.*` plus `omega`.

## Optional contract_spec

If using [extensions/CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md), the theorem list above maps directly to a `contract_spec Counter where …` block. Not required for v1.
