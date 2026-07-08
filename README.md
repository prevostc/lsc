# LSC

Lean 4.30 implementation of the [design](docs/) contract language.

## Layout

| Path | Role |
|------|------|
| `Lsc/Core/` | `UInt256` checked ops, `ContractM` runtime |
| `Lsc/Lib/Wei/`, `Lib/Wad.lean`, `Lib/Ray.lean` | Numeric types: AST fragments, eval, lower, checks |
| `Lsc/Lib/Linear/TokenAmount.lean` | Linear-type stub (no capability model yet — see below) |
| `Lsc/Lang/AST.lean` | `Expr`/`Stmt`/`ContractDef`/`FunctionDef` inductives |
| `Lsc/Lang/Eval.lean` | `ContractM`, `Stmt.eval`, `Expr.eval` |
| `Lsc/Lang/Syntax.lean` | The `tx { ... }` contract-body grammar (current author surface) plus `derive_contract`, which assembles a contract from `tx`/`view` blocks + `deriving`-generated storage/error/event handlers |
| `Lsc/Lang/TxM.lean` | `TxM := WriterT Stmt Id` builder monad + combinators/notations underlying `Syntax.lean`'s desugaring (not the contract-author surface itself) |
| `Lsc/Lang/Derive.lean` | `deriving ContractStorage/ContractError/ContractEvent` handlers + internal DSL assembly used by `derive_contract` |
| `Lsc/Lang/Checks.lean` | Static validation (cycles, selectors, UInt256, arith-error coverage) |
| `Lsc/Compile/` | IR lowering → EvmYulLean AST → Yul text, plus `Bytecode/` (direct EVM opcode emission); `Correctness.lean` IR eval lemmas |
| `examples/counter/src/Counter.lean` | Reference contract, written with the `tx { ... }` grammar + `derive_contract` |
| `examples/counter/test/CounterTheorem.lean` | Theorems from `reference/COUNTER.md`, proved against `Counter.lean` |

> Note: an earlier, hand-written version of `Counter.lean` (with `getField`/`setField`/etc. written by hand instead of `deriving`-generated) was kept alongside the current one for a while as a comparison reference; once the `TxM`/`deriving` approach was proven out it replaced the hand-written version outright, so there is now a single `Counter.lean`. See `docs/DESIGN.md` and `docs/framework/IMPLEMENTATION.md` for the full history of the surface-syntax redesign.

## Build

Requires a C toolchain (`cc`) for the `evmyul` dependency (FFI).

```bash
./scripts/ci.sh
```

CI builds library tests, correctness lemmas, and the counter example, and **fails on any compiler/linter `warning:`** in build output. It also builds and runs the `BytecodeExecSmoke` target — except this is currently **skipped** (the vendored `evmyul` Python FFI shim isn't set up correctly in this CI environment, independent of any DSL code change; see the comment in `scripts/ci.sh`), so a real EVM-execution smoke test exists but is not part of the green-CI gate today.

Or manually:

```bash
lake build
cd examples/counter && lake build
```

## What is proved

The counter example proves all theorems from [COUNTER.md](docs/reference/COUNTER.md) against `runS increment/pause/unpause` in `test/CounterTheorem.lean`, closing with `simp` (unfolding `Stmt.eval`/`ContractM.*`/the `deriving`-generated `getField`/`setField`/`resolveError`/`buildEvent` defs) plus `omega` — the same proof technique a hand-written contract would use, confirming the `tx`/`deriving` redesign doesn't regress proof burden.

`Lsc.Compile.Correctness` proves kernel-checked lemmas for the increment lowering slice (Wei `+? 1` IR shape, IR eval of overflow-checked bind, body lowering success). `Lsc.Compile.YulTest` upgrades structural `#guard` checks to theorems on rendered Yul strings.

## What is trusted / deferred

- **Arithmetic**: `Wei.addCheckedNat` etc. in `Lsc/Lib/Wei/Eval.lean`/`Optimize.lean` (some edge lemmas use `native_decide`).
- **Keccak / ABI**: selectors use `String.hash` stub; real keccak256 deferred.
- **EvmYul text**: Yul rendering only; semantics via upstream `evmyul` Lake dependency (pinned in `lake-manifest.json`).
- **Direct bytecode emission** (`Lsc/Compile/Bytecode/*`): generates flat EVM `Instr` sequences and encodes them directly (bypassing Yul text); exercised by `BytecodeTest`/`BytecodeExecTest`, but the actual-EVM-execution smoke check (`BytecodeExecSmoke`) is currently skipped in CI (see above) — bytecode encoding is tested structurally, not against a real EVM execution in this environment.
- **`deriving ContractStorage`/`ContractEvent`/`ContractError`** (`Lsc/Lang/Derive.lean`): structural codegen only supports `Wei`/`Bool`/`Address`/`UInt256` storage fields and 0-/1-parameter event constructors; the `ArithError`/`FrameworkError` mapping in `deriving ContractError` is name-convention-based, with the actual reachability guarantee enforced by the separate `Lang/Checks.lean` arith-error-coverage pass, which runs at `lake build`/compile time via `Lsc.Lang.Checks.validateAll` (not source-position-attached — see `docs/DESIGN.md` §3.2).
- **Linearity**: `checkLinear` is a no-op stub; `Lsc/Lib/Linear/TokenAmount.lean` exists only as a minimal, non-enforcing structure — no capability model or AST integration yet.

## Tests vs proofs

| Target | Role |
|--------|------|
| `Lsc.Lang.TxMTest` | `TxM` combinator smoke tests |
| `Lsc.Lang.DeriveTest` | `deriving` handler smoke tests |
| `Lsc.ChecksTest` | Validation pass smoke tests (`native_decide`) |
| `Lsc.Compile.YulTest` | Yul string theorems + `#eval` print |
| `Lsc.Compile.BytecodeTest`, `BytecodeExecTest` | Bytecode encoding structural checks; EVM-execution check (skipped in CI, see above) |
| `Lsc.Compile.Correctness` | IR ↔ lowering theorems for increment slice |
| `examples/counter` (`CounterTheorem`) | End-to-end `Stmt.eval` theorems for the reference contract |

Smoke tests are fast regressions; correctness lemmas and counter theorems are the semantic gate.
