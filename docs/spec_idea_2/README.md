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

## Resolved decisions

| Topic | Decision | Rationale |
|-------|----------|-----------|
| AMM reserves | `Wad` in storage; `TokenAmount` for in-flight ERC20 custody only | Reserves are persistent accounting; in-flight tokens need linear tracking |
| `contract_spec` | Optional extension — not required for v1 | Keeps core small; auditors opt in |
| Access control | `Capability` linear type retained; call-site shape (parameter vs `require`) still open | Forces explicit role checks |
| Counter events | `Paused` / `Unpaused` (not `WasPaused`) | Present-tense matches ERC convention |
| `require` syntax | `require (cond) else revert Error;` | Explicit revert target; mirrors Lean `if … then … else` |
| Storage access | `$.field` reads, `$.field := val` writes; proofs use `s.storage.field` | Distinguishes surface syntax from proof terms |
| Checked arithmetic | `+?`, `-?`, `*?`, `/?`; reverts via strict 1:1 `ContractErrors.arith` | Overflow → `Overflow`, Underflow → `Underflow`, DivByZero → `DivByZero`; no collapsing |
| Wrapping arithmetic | `+↻`, `-↻`, `*↻` — pure mod-2²⁵⁶, never reverts | Explicit opt-in for intentional wrapping |
| Fixed-point rounding | Bracket pairs `⌊*⌋?` `⸢*⸣?` `⌊/⌋?` etc.; activate with `open scoped Lsc.Wad` / `Lsc.Ray` | Forces naming the rounding direction; prevents silent precision loss |
| `@math` real-number twin | Named `.ideal` (e.g. `computeOutput.ideal`) | Avoids collision with `contract_spec` / `CounterSpec.lean` naming |
| `@math` error lift | `\|>.orRevert` on `Except ArithError` → same `ContractErrors.arith` as `+?` | One error path for all arithmetic failures |
| Framework errors | `ContractErrors.fromFramework` (reentrancy, unauthorized) | Separates framework errors from user-defined errors |

## Open questions

| Topic | Status |
|-------|--------|
| `Capability` call-site API | Open — parameter passed by caller vs `require`-style internal acquisition |
| Bounded loops (v2) | Not in v1; requires loop invariant syntax |
| End-to-end compilation correctness | v2 goal; v1 has per-construct theorems + conformance tests |

## Glossary

| Term | Meaning |
|------|---------|
| `ContractM` | State monad where contract semantics and proofs live |
| `TokenAmount` | Linear type for in-flight ERC20 custody; cannot be duplicated or dropped |
| `Capability` | Linear type proving the caller passed an identity check for a role |
| `ReentrancyLock` | Linear type representing exclusive execution access |
| `HonestWorld` | Typeclass bundling external-contract behavior assumptions for multi-contract theorems |
| `WayRayMath` | External Lean library supplying error-bound lemmas connecting ℕ fixed-point ops to ℝ |
| `contract_spec` | Optional syntax for auditor-facing propositions (`CounterSpec.lean`) |
| `@math` | Annotation generating a ℝ twin (`.ideal`) for fixed-point functions |
| `ContractErrors.arith` | Per-contract mapping from `ArithError` variants to user error type; strict 1:1 |
| `ContractErrors.fromFramework` | Per-contract mapping from `FrameworkError` to user error type |
