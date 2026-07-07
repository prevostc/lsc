# Decisions

Architecture decision records: why the framework is built the way it is, and what alternatives
were tried and rejected along the way. This is the canonical home for that history — code
comments should link here instead of restating the rationale inline.

Not for: unbuilt features (see [`../todo/`](../todo/)) or day-to-day API documentation (see
doc-comments in the code itself, or [`../reference/`](../reference/) for per-contract specs).

| ADR | Decision |
|---|---|
| [0001](0001-txm-superseded-by-syntax.md) | `tx { .. }` custom grammar (`Lsc/Lang/Syntax.lean`) replaced the `TxM` do-notation builder as the contract-author surface |
| [0002](0002-pairm-cross-contract-model.md) | Cross-contract calls use a statically-typed `PairM` pair-of-states, not a general N-contract registry |
| [0003](0003-exec-read-black-box.md) | `exec`/`read` are black box (no `toErr`/`toEvent`), replacing the earlier `externalCall2` whitebox model |
| [0004](0004-escrow-hand-written-dsl-wiring.md) | `Escrow` no longer needs hand-written `ContractDSL`/`ContractErrors` glue, now that `exec`/`read` are black box |
| [0005](0005-bytecode-backend-scope.md) | The direct bytecode backend rejects constructs it can't yet lower, rather than emitting wrong bytecode |

## Template

Each ADR is a short markdown file:

```markdown
# NNNN: Title

## Context
What problem or question prompted this decision.

## Decision
What was chosen.

## Rejected alternatives
What else was tried or considered, and why it was dropped.

## Consequences
What this implies for the rest of the framework, including any follow-up work (link to
`docs/todo/` if there's a tracked item).
```
