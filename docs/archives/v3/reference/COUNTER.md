# Reference: Pausable Counter

Canonical minimal reference contract. Every framework feature should be exercised here before attempting DeFi contracts.

Full design context: [DESIGN.md §13](../DESIGN.md). Implementation walkthrough (framework developers): [framework/IMPLEMENTATION.md Step 11](../framework/IMPLEMENTATION.md).

## Contract

Surface syntax follows the actual implementation: plain Lean `structure`/`inductive` declarations with `deriving ContractStorage/ContractError/ContractEvent`, the dss2024-style bracket-delimited `tx <name> { ... }` grammar (`Lsc/Lang/Syntax.lean`, see [DESIGN.md §3.4](../DESIGN.md)) for function bodies, and a single trailing `derive_contract` command that assembles everything — full source: `examples/counter/src/Counter.lean`.

```lean
structure CounterStorage where
  number : Wei := ⟨0⟩
  paused : Bool := false
  owner  : Address := 0
  deriving Repr, ContractStorage

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, ContractEvent

tx increment {
  require(!σ.paused) else revert Paused();
  let n = σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

tx pause {
  require(msg.sender == σ.owner) else revert NotOwner();
  require(!σ.paused) else revert Paused();
  σ.paused = true;
  emit Paused();
}

tx unpause {
  require(msg.sender == σ.owner) else revert NotOwner();
  require(σ.paused) else revert Paused();
  σ.paused = false;
  emit Unpaused();
}

derive_contract "Counter" CounterStorage CounterError CounterEvent
```

`number` is `Wei` — the 0-decimal numeric type (like `Wad`/`Ray` but with identity encoding: `1 Wei
= 1`). Bare `UInt256` cannot be used for arithmetic in contract bodies; all numeric ops go through
typed wrappers (`Wei`, `Wad`, `Ray`). `require(cond) else revert ErrCtor();`, standalone `revert
ErrCtor();`, and `emit Ctor(..);` all elaborate their argument against the real
`CounterError`/`CounterEvent` inductive, so a typo or wrong arity is a compile error. `derive_contract
"Counter" CounterStorage CounterError CounterEvent` is the single call a contract author writes —
see `Lsc/Lang/Syntax.lean`'s docstring for what it expands each `tx`/this call into.

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
| `increment_reverts_on_overflow` | `simp` (error case) |

Proof hypotheses use `s.storage.field` on `ContractState` snapshots — not `σ.field` (the `σ.field` family is source-level notation for *building* a function body's `Stmt`; theorem statements and proofs work directly with `ContractState`/`runS`). These 10 theorems are proved in `test/CounterTheorem.lean` against `Counter.lean`, zero `sorry`s, via `simp` unfolding `Stmt.eval`/`ContractM.*` plus `omega`.

## Optional contract_spec

If using [extensions/CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md), the theorem list above maps directly to a `contract_spec Counter where …` block. Not currently required.
