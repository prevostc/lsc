# LSC Design Specification

LSC is a Lean 4 embedded DSL for writing formally verified EVM smart contracts. You write contracts and proofs in the same file; the compiler checks the proofs and emits Yul → EVM bytecode.

## Reading order

For **contract authors** (writing contracts against LSC, not modifying LSC itself):

1. **[DESIGN.md](DESIGN.md)** — what LSC is, the guarantees it provides, and the architecture/
   trust model/core semantics that achieve them. Start here.
2. Reference contracts — worked examples, each with its required-theorems checklist:
   - [reference/COUNTER.md](reference/COUNTER.md) — minimal acceptance test
   - [reference/INTEREST.md](reference/INTEREST.md) — `Wad` math, parameterized `tx`
   - [reference/TOKEN.md](reference/TOKEN.md), [reference/ESCROW.md](reference/ESCROW.md) — cross-contract calls
   - [reference/AMM.md](reference/AMM.md) — full DeFi contract (target, not yet built)
3. Extensions — read as needed:
   - [extensions/linear-types/](extensions/linear-types/) — one file per linear type
   - [extensions/TYPE-CONSTRAINTS.md](extensions/TYPE-CONSTRAINTS.md) — `@monotonic`, `@bounded`, etc.
   - [extensions/MATH.md](extensions/MATH.md) — `@math` annotation and ℝ proof patterns
   - [extensions/CONTRACT-SPEC.md](extensions/CONTRACT-SPEC.md) — optional auditor-facing spec layer
4. **[todo/](todo/)** — unbuilt features and open backlog items, in case something you need isn't there yet.

For **framework developers** (working on LSC's own compiler/stdlib):

5. **[decisions/](decisions/)** — why the framework internals are the way they are, not some other
   way: one file per rejected/superseded approach. Read before touching code a decision covers.
6. **[framework/IMPLEMENTATION.md](framework/IMPLEMENTATION.md)** — module layout, build steps, code
   sketches for the compiler/stdlib itself.

## Document map

| File | Audience | Role |
|------|----------|------|
| `DESIGN.md` | Both | What LSC is, its guarantees, and the architecture that achieves them |
| `reference/` | Contract authors | Per-contract spec + required theorems |
| `extensions/linear-types/` | Contract authors | `TokenAmount`, `Capability`, etc. — enforcement and proof impact |
| `extensions/TYPE-CONSTRAINTS.md` | Contract authors | Storage invariants via field decorators |
| `extensions/MATH.md` | Contract authors | Fixed-point math, `@math` annotation, ℝ proof patterns |
| `extensions/CONTRACT-SPEC.md` | Contract authors | Optional auditor-readable proposition layer |
| `todo/` | Both | Unbuilt features and backlog |
| `decisions/` | Framework developers | Why: one ADR per rejected/superseded internal approach |
| `framework/IMPLEMENTATION.md` | Framework developers | How to build the compiler/stdlib; defers to DESIGN for semantics |

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
