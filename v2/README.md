# LSC v2

Lean 4.30 implementation of the [spec idea 2](../docs/spec_idea_2/) contract language.

## Layout

| Path | Role |
|------|------|
| `LscV2/Eval.lean` | `ContractM`, `Stmt.eval` — semantic core |
| `LscV2/Syntax.lean` | Surface DSL (`lsc!`, `contract … where`) |
| `LscV2/Checks.lean` | Static validation (cycles, selectors, UInt256, arith coverage) |
| `LscV2/Compile/` | IR lowering → EvmYulLean AST → Yul text |
| `LscV2/Contract.lean` | Contract command elaboration (Step 7; in progress) |
| `examples/counter/` | Reference contract + 9 COUNTER.md theorems |

## Build

Requires a C toolchain (`cc`) for the `evmyul` dependency (FFI).

```bash
./scripts/ci-v2.sh
```

Or manually:

```bash
cd v2 && lake build
cd v2/examples/counter && lake build
```

## What is proved

The counter example proves all nine theorems from [COUNTER.md](../docs/spec_idea_2/reference/COUNTER.md) against `runS increment/pause/unpause`, via bridge lemmas to reference evaluators and `Stmt.eval` on monolithic ASTs.

## What is trusted / deferred

- **Arithmetic**: `Wei.addCheckedNat` etc. in `LscV2/Arithmetic.lean` (some `sorry`s remain on edge lemmas).
- **Keccak / ABI**: selectors use `String.hash` stub; real keccak256 deferred.
- **EvmYul text**: Yul rendering only; semantics via upstream `evmyul` Lake dependency (pinned in `lake-manifest.json`).
- **Contract elaboration**: generic `contract` codegen not yet wired; counter is hand-written.
- **Linearity**: `checkLinear` is a no-op stub.

## DSL tests

`LscV2.SyntaxTest` checks macro output against hand-built AST (`example … := rfl`).

`LscV2.ChecksTest` runs validation passes on a fixture `ContractDef`.

`LscV2.Compile.YulTest` checks structural Yul output for increment lowering.
