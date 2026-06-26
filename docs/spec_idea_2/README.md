# LSC Design Specification (spec_idea_2)

Formally verified EVM smart contract language — design, implementation guide, extensions, and reference contracts.

## Reading order

1. **[DESIGN.md](DESIGN.md)** — architecture, trust model, core semantics. Start here.
2. **[IMPLEMENTATION.md](IMPLEMENTATION.md)** — module layout, build steps, code sketches.
3. **Extensions** — read as needed:
   - [extensions/linear-types/](extensions/linear-types/) — linear type system (one file per type)
   - [extensions/TYPE-CONSTRAINTS.md](extensions/TYPE-CONSTRAINTS.md) — field decorators (`@monotonic`, `@bounded`, …)
   - [extensions/MATH.md](extensions/MATH.md) — `@math` annotation and ℝ specs
   - [extensions/CONTRACT-SPEC.md](extensions/CONTRACT-SPEC.md) — optional `contract_spec` layer (auditor-facing propositions)
4. **Reference contracts** — canonical examples:
   - [reference/COUNTER.md](reference/COUNTER.md)
   - [reference/AMM.md](reference/AMM.md)

## Document map

| File | Role |
|------|------|
| `DESIGN.md` | Authoritative design decisions and architecture |
| `IMPLEMENTATION.md` | How to build it; defers to DESIGN for semantics |
| `extensions/linear-types/` | Deep dive on each linear type; enforcement and proof impact |
| `extensions/TYPE-CONSTRAINTS.md` | Storage field invariants via decorators |
| `extensions/MATH.md` | Fixed-point math specs and proof patterns |
| `extensions/CONTRACT-SPEC.md` | Optional spec/proof separation for auditors |
| `reference/COUNTER.md` | Minimal reference contract (acceptance test) |
| `reference/AMM.md` | DeFi reference contract (Wad reserves, linear types, world model) |

## Resolved decisions

| Topic | Decision |
|-------|----------|
| AMM reserves | `Wad` in storage; `TokenAmount` for in-flight token custody only |
| `contract_spec` | Optional extension — not required for v1 |
| Access control | `Capability` linear type retained; API shape (parameter vs internal `require`) still open |
| Counter events | `Paused` / `Unpaused` (not `WasPaused`) |
| Surface `require` syntax | `require (cond) else revert Error;` (see IMPLEMENTATION) |
| Storage access | `$.field` reads, `$.field := val` writes; proofs use `s.storage.field` |
| Checked arithmetic | `+?`, `-?`, `*?`, `/?`; reverts via strict 1:1 `ContractErrors.arith` (named `Overflow` / `Underflow` / `DivByZero` in `errors:`) |
| Wrapping arithmetic | `+↻`, `-↻`, `*↻` — pure mod-2²⁵⁶, intentional only |
| Fixed-point rounding | Bracket pairs `⌊*⌋?`, `⸢*⸣?`, `⌊/⌋?`, … — no default `wadMul`; scope via `open scoped Lsc.Wad` / `Lsc.Ray` |
| `@math` error lift | `|>.orRevert` on `Except ArithError` → same `ContractErrors.arith` as `+?` |
| Framework errors | `ContractErrors.fromFramework` (reentrancy, unauthorized, …) |

## Glossary

- **ContractM** — state monad where contract semantics and proofs live
- **TokenAmount** — linear type for fungible token custody during a transaction
- **Capability** — linear type proving caller passed an identity check for a role
- **contract_spec** — optional syntax for human-readable propositions (`CounterSpec.lean`)
- **@math** — annotation generating ℝ specification lemmas for fixed-point functions
