# LSC v2

Lean 4.30 implementation of the [spec idea 2](../docs/spec_idea_2/) contract language.

## Layout

| Path | Role |
|------|------|
| `LscV2/Core/` | `UInt256` checked ops, `ContractM` runtime |
| `LscV2/Lib/Wei/`, `Lib/Wad.lean`, `Lib/Ray.lean` | Numeric types: AST fragments, eval, lower, checks |
| `LscV2/Lang/AST.lean` | `Expr`/`Stmt`/`ContractDef`/`FunctionDef` inductives |
| `LscV2/Lang/Eval.lean` | `ContractM`, `Stmt.eval`, `Expr.eval` |
| `LscV2/Lang/TxM.lean` | `TxM := WriterT Stmt Id` builder monad + combinators/notations (`do`-notation contract bodies — see module docstring for the type-tagged `σ.field` read family and the `let` vs. `letWei`/`letBool`/`letAddr`/`letU256` distinction) |
| `LscV2/Lang/Derive.lean` | `deriving ContractStorage/ContractError/ContractEvent` handlers + `derive_contract_dsl` assembly command |
| `LscV2/Lang/Checks.lean` | Static validation (cycles, selectors, UInt256, arith-error coverage) |
| `LscV2/Compile/` | IR lowering → EvmYulLean AST → Yul text, plus `Bytecode/` (direct EVM opcode emission); `Correctness.lean` IR eval lemmas |
| `examples/counter/src/Counter.lean` | Reference contract, written with `TxM`/`deriving` |
| `examples/counter/test/CounterTheorem.lean` | 9 COUNTER.md theorems, proved against `Counter.lean` |

> Note: the original `contract … where` custom-syntax surface (`LscV2/Lang/Syntax.lean`, `Contract.lean`, `ContractGen.lean`, `ContractTypes.lean`) was implemented and later deleted in favor of `TxM.lean`/`Derive.lean` above — see `docs/spec_idea_2/DESIGN.md` §3 and `IMPLEMENTATION.md` §6–§7 for the full rationale. An earlier, hand-written version of `Counter.lean` (with `getField`/`setField`/etc. written by hand instead of `deriving`-generated) was kept alongside the new one for a while as a comparison reference; once the new approach was proven out it replaced the hand-written version outright, so there is now a single `Counter.lean`.

## Build

Requires a C toolchain (`cc`) for the `evmyul` dependency (FFI).

```bash
./scripts/ci-v2.sh
```

CI builds library tests, correctness lemmas, and the counter example, and **fails on any compiler/linter `warning:`** in build output. It also builds and runs the `BytecodeExecSmoke` target — except this is currently **skipped** (the vendored `evmyul` Python FFI shim isn't set up correctly in this CI environment, independent of any v2 code change; see the comment in `scripts/ci-v2.sh`), so a real EVM-execution smoke test exists but is not part of the green-CI gate today.

Or manually:

```bash
cd v2 && lake build
cd v2/examples/counter && lake build
```

## What is proved

The counter example proves all nine theorems from [COUNTER.md](../docs/spec_idea_2/reference/COUNTER.md) against `runS increment/pause/unpause` in `test/CounterTheorem.lean`, closing with `simp` (unfolding `Stmt.eval`/`ContractM.*`/the `deriving`-generated `getField`/`setField`/`resolveError`/`buildEvent` defs) plus `omega` — the same proof technique a hand-written contract would use, confirming the `TxM`/`deriving` redesign doesn't regress proof burden.

`LscV2.Compile.Correctness` proves kernel-checked lemmas for the increment lowering slice (Wei `+? 1` IR shape, IR eval of overflow-checked bind, body lowering success). `LscV2.Compile.YulTest` upgrades structural `#guard` checks to theorems on rendered Yul strings.

## What is trusted / deferred

- **Arithmetic**: `Wei.addCheckedNat` etc. in `LscV2/Lib/Wei/Eval.lean`/`Optimize.lean` (some edge lemmas use `native_decide`).
- **Keccak / ABI**: selectors use `String.hash` stub; real keccak256 deferred.
- **EvmYul text**: Yul rendering only; semantics via upstream `evmyul` Lake dependency (pinned in `lake-manifest.json`).
- **Direct bytecode emission** (`LscV2/Compile/Bytecode/*`): generates flat EVM `Instr` sequences and encodes them directly (bypassing Yul text); exercised by `BytecodeTest`/`BytecodeExecTest`, but the actual-EVM-execution smoke check (`BytecodeExecSmoke`) is currently skipped in CI (see above) — bytecode encoding is tested structurally, not against a real EVM execution in this environment.
- **`deriving ContractStorage`/`ContractEvent`/`ContractError`** (`LscV2/Lang/Derive.lean`): structural codegen only supports `Wei`/`Bool`/`Address`/`UInt256` storage fields and 0-/1-parameter event constructors; the `ArithError`/`FrameworkError` mapping in `deriving ContractError` is name-convention-based, with the actual reachability guarantee enforced by the separate `Lang/Checks.lean` arith-error-coverage pass (not at `deriving` time — see `docs/spec_idea_2/DESIGN.md` §3.2).
- **Linearity**: `checkLinear` is a no-op stub; AST `permits` removed (redesign TBD in `Lib/Linear`).

## Tests vs proofs

| Target | Role |
|--------|------|
| `LscV2.Lang.TxMTest` | `TxM` combinator smoke tests |
| `LscV2.Lang.DeriveTest` | `deriving` handler smoke tests |
| `LscV2.ChecksTest` | Validation pass smoke tests (`native_decide`) |
| `LscV2.Compile.YulTest` | Yul string theorems + `#eval` print |
| `LscV2.Compile.BytecodeTest`, `BytecodeExecTest` | Bytecode encoding structural checks; EVM-execution check (skipped in CI, see above) |
| `LscV2.Compile.Correctness` | IR ↔ lowering theorems for increment slice |
| `examples/counter` (`CounterTheorem`) | End-to-end `Stmt.eval` theorems for the reference contract |

Smoke tests are fast regressions; correctness lemmas and counter theorems are the semantic gate.
