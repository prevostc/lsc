# LSC v2

Lean 4.30 implementation of the [spec idea 2](../docs/spec_idea_2/) contract language.

## Layout

| Path | Role |
|------|------|
| `LscV2/Core/` | `UInt256` checked ops, `ContractM` runtime |
| `LscV2/Lib/Wei/` | Wei type, AST fragment, eval, lower, checks |
| `LscV2/Eval.lean` | `CoreExpr.eval`, `Expr.eval` dispatch, `Stmt.eval` |
| `LscV2/Syntax.lean` | Surface DSL (`lsc!`, `contract … where`) |
| `LscV2/Checks.lean` | Static validation (cycles, selectors, UInt256, arith coverage) |
| `LscV2/Compile/` | IR lowering → EvmYulLean AST → Yul text; `Correctness.lean` IR eval |
| `LscV2/Contract.lean` | Contract command elaboration (Step 7; in progress) |
| `examples/counter/` | Reference contract + 9 COUNTER.md theorems |

## Build

Requires a C toolchain (`cc`) for the `evmyul` dependency (FFI).

```bash
./scripts/ci-v2.sh
```

CI builds library tests, correctness lemmas, and the counter example, and **fails on any compiler/linter `warning:`** in build output.

Or manually:

```bash
cd v2 && lake build
cd v2/examples/counter && lake build
```

## What is proved

The counter example proves all nine theorems from [COUNTER.md](../docs/spec_idea_2/reference/COUNTER.md) against `runS increment/pause/unpause`, via bridge lemmas to reference evaluators and `Stmt.eval` on monolithic ASTs.

`LscV2.Compile.Correctness` proves kernel-checked lemmas for the increment lowering slice (Wei `+? 1` IR shape, IR eval of overflow-checked bind, body lowering success). `LscV2.Compile.YulTest` upgrades structural `#guard` checks to theorems on rendered Yul strings.

## What is trusted / deferred

- **Arithmetic**: `Wei.addCheckedNat` etc. in `LscV2/Lib/Wei/Arith.lean` (some edge lemmas use `native_decide`).
- **Keccak / ABI**: selectors use `String.hash` stub; real keccak256 deferred.
- **EvmYul text**: Yul rendering only; semantics via upstream `evmyul` Lake dependency (pinned in `lake-manifest.json`).
- **Contract elaboration**: generic `contract` codegen not yet wired; counter is hand-written.
- **Linearity**: `checkLinear` is a no-op stub; AST `permits` removed (redesign TBD in `Lib/Linear`).

## Tests vs proofs

| Target | Role |
|--------|------|
| `LscV2.SyntaxTest` | Macro smoke tests (`example … := rfl`) |
| `LscV2.ChecksTest` | Validation pass smoke tests (`native_decide`) |
| `LscV2.Compile.YulTest` | Yul string theorems + `#eval` print |
| `LscV2.Compile.Correctness` | IR ↔ lowering theorems for increment slice |
| `examples/counter` | End-to-end `Stmt.eval` theorems |

Smoke tests are fast regressions; correctness lemmas and counter theorems are the semantic gate.
