# LSC Design Specification

LSC is a Lean 4 embedded DSL for writing formally verified EVM smart contracts. You write contracts and proofs in the same file; the compiler checks the proofs and emits Yul → EVM bytecode.

## Reading order

1. **[DESIGN.md](DESIGN.md)** — architecture, trust model, core semantics. Start here.
2. **[IMPLEMENTATION.md](IMPLEMENTATION.md)** — module layout, build steps, code sketches.
3. Extensions — read as needed:
   - [extensions/linear-types/](extensions/linear-types/) — one file per linear type
   - [extensions/TYPE-CONSTRAINTS.md](extensions/TYPE-CONSTRAINTS.md) — `@monotonic`, `@bounded`, etc.
   - [extensions/MATH.md](extensions/MATH.md) — `@math` annotation and ℝ proof patterns
   - [extensions/CONTRACT-SPEC.md](extensions/CONTRACT-SPEC.md) — optional auditor-facing spec layer
4. Reference contracts:
   - [reference/COUNTER.md](reference/COUNTER.md) — minimal acceptance test
   - [reference/AMM.md](reference/AMM.md) — full DeFi contract

## Document map

| File | Role |
|------|------|
| `DESIGN.md` | Authoritative decisions and architecture |
| `IMPLEMENTATION.md` | How to build it; defers to DESIGN for semantics |
| `extensions/linear-types/` | `TokenAmount`, `Capability`, etc. — enforcement and proof impact |
| `extensions/TYPE-CONSTRAINTS.md` | Storage invariants via field decorators |
| `extensions/MATH.md` | Fixed-point math, `@math` annotation, ℝ proof patterns |
| `extensions/CONTRACT-SPEC.md` | Optional auditor-readable proposition layer |
| `reference/COUNTER.md` | Minimal reference contract (framework acceptance test) |
| `reference/AMM.md` | DeFi reference contract (linear types, Wad reserves, world model) |

## Open questions

| Topic | Status |
|-------|--------|
| `Capability` call-site API | Open — parameter passed by caller vs `require`-style internal acquisition |
| Bounded loops | Not yet implemented; requires loop invariant syntax |
| End-to-end compilation correctness | Future work; currently has per-construct theorems + conformance tests |

## Glossary

| Term | Meaning |
|------|---------|
| `ContractM` | State monad where contract semantics and proofs live |
| `TokenAmount` | Planned linear type for in-flight ERC20 custody (cannot be duplicated or dropped); currently only a non-enforcing structure stub exists at `Lsc/Lib/Linear/TokenAmount.lean`, with no capability model or AST integration yet |
| `Capability` | Linear type proving the caller passed an identity check for a role |
| `ReentrancyLock` | Linear type representing exclusive execution access |
| `HonestWorld` | Typeclass bundling external-contract behavior assumptions for multi-contract theorems |
| `Wei` | 0-decimal numeric newtype (`1 Wei = 1`); checked `+?`/`-?`/`*?`/`/?` like `Wad`, no bracket-pair rounding |
| `UInt256` | Opaque EVM word — selectors, timestamps, mapping keys; compare only (`<`, `≤`, `==`), no arithmetic in contract bodies |
| `WayRayMath` | External Lean library supplying error-bound lemmas connecting ℕ fixed-point ops to ℝ |
| `contract_spec` | Optional syntax for auditor-facing propositions (`CounterSpec.lean`) |
| `@math` | Annotation generating a ℝ twin (`.ideal`) for fixed-point functions |
| `ContractErrors.arith` | Per-contract mapping from `ArithError` variants to user error type; strict 1:1 |
| `ContractErrors.fromFramework` | Per-contract mapping from `FrameworkError` to user error type |
