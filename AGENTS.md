# Project Agent Instructions

## Context discipline

Treat context as scarce.

Use subagents for contained work such as coding, theorem proving, codebase exploration, build fixes, research, and isolated design questions.

Keep the main context focused on goals, architectural decisions, evidence, unresolved questions, and current work.

Prefer module APIs and exported guarantees over reading implementation internals.

Read `docs/PROJECT_GOAL.md` when you need the canonical product goal. Keep that document concise and do not turn it into a project diary.

## Model routing

When model selection is available:

- **Cursor 4.6 xhigh**: coding, refactoring, mechanical exploration, build fixes, contained proof tasks.
- **Fable 5.1 high/xhigh**: architecture, proof strategy, decomposition, hard design decisions, challenging results, deciding what to do next.

Do not spend Fable on work Cursor can reliably execute.

Do not let execution agents make major architectural decisions implicitly through code.

## Lean execution

**Never run more than one Lean build/checking process at once.**

Treat Lean execution as one global lock across all agents. This includes `lake build`, `lake env lean`, project-wide checks, and equivalent Lean processes.

Parallel reasoning is fine; parallel Lean builds are not.

## Theorem organization

Preferred default:

- `xxTheorems.lean`: concise natural-language meaning + clean theorem statement.
- `xxProof.lean`: detailed proof implementation.
- `xxTheorems.lean` should ideally close the theorem with a one-line reference to the proof implementation.

If Lean dependencies make this exact layout awkward, preserve the principle: theorem intent and proof implementation should be independently understandable and loadable.

## Implementation + proof

Plan implementation and proof jointly before substantial work.

Do not design code first and discover later that it is hostile to proof.

## Simplification

Treat deletion and refactoring as normal progress.

After substantial work ask:

> **If we rebuilt this subsystem today using what we now know, would it still look like this?**

Remove, collapse, or refactor unnecessary complexity before building more on top.

Temporary scaffolding must be removed or explicitly promoted to architecture.

## Architecture contracts

Do not silently change major architectural contracts.

Changes affecting semantics, compilation, trusted assumptions, or proof boundaries must make their effect on the documented end-to-end proof chain explicit.
