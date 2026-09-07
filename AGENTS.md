# Project Agent Instructions

## Context discipline

Treat context as scarce.

Use subagents for contained work such as coding, theorem proving, codebase exploration, build fixes, research, and isolated design questions.

Keep the main context focused on goals, architectural decisions, evidence, unresolved questions, and current work.

Prefer module APIs and exported guarantees over reading implementation internals.

Read `docs/PROJECT_GOAL.md` when you need the canonical product goal. Keep that document concise and do not turn it into a project diary.

## Model routing

When model selection is available:

- **Cursor Grok 4.6 xhigh** (default for everything): coding, refactoring, exploration, build fixes,
  proof implementation, proof-strategy drafts, design drafts, documentation, reports.
- **Fable 5.1**: reserved for the few most critical architecture decisions (semantics, proof
  boundaries, trusted assumptions) and for adjudicating when Grok's results conflict or fail
  twice. At most one Fable subagent at a time, read-only, with a tight brief and a ≤ 250-line
  deliverable. Never for implementation, docs, or first-draft designs.

Fable budget is the binding constraint of this project. Before spawning Fable ask: could Grok draft
this and Fable only review the draft? If yes, do that. The main (Fable) context must stay brief:
delegate, decide, record; do not read implementation files or long reports itself.

Do not let execution agents make major architectural decisions implicitly through code.

## Lean execution

**Never run more than one Lean build/checking process at once.**

Treat Lean execution as one global lock across all agents. This includes `lake build`, `lake env lean`, project-wide checks, and equivalent Lean processes.

The lock is enforced by `scripts/lean`: always run Lean through it, e.g. `scripts/lean lake build Lsc.Security.Wealth`. It blocks until the other Lean process finishes. Never invoke `lake` or `lean` directly.

Build only the targets you need (`lake build <Module>`), not the whole library, so another agent's in-progress file cannot fail your build.

Parallel reasoning is fine; parallel Lean builds are not.

## Theorem organization

A **guarantee module** is any module that exports a theorem referenced by
`Checks.lean`, by `docs/internals/*.md` or `docs/guide/*.md`, or by another module's *statement*
(not just its proof). Every guarantee module `Foo.lean` is split as follows:

- `FooTheorems.lean`: for each exported theorem, a docstring in plain language
  (what it guarantees, under which hypotheses, in one to four sentences, no
  proof talk), the statement verbatim, and the body `:= Foo.Proof.thm_name`
  (or `:= by exact Foo.Proof.thm_name` if elaboration needs it). Definitions
  the statement needs (`structure`s, `def`s, `abbrev`s such as `EvmTraceRunAll`,
  `TransportSetup`, `R`, `Inv`) stay in a `FooDefs.lean` (or the existing defs
  module) imported by both files; the Theorems file must **not** contain proof
  code beyond the one-line reference.
- `FooProof.lean`: the actual proof (`theorem thm_name … := by …`) in namespace
  `<orig>.Proof`, plus all private helpers. Imports whatever it needs.
- Downstream modules import `FooTheorems` (never `FooProof`).
- Fully-qualified theorem names used by `Checks.lean` must not change — the
  Theorems-file theorem keeps the original namespace and name.
- Placement: Theorems/Defs of a `Proof/*` guarantee module go **up** to
  `Lsc/Compiler/<Name>Theorems.lean` (and `…Defs.lean` if needed); the proof
  stays `Lsc/Compiler/Proof/<Name>Proof.lean`.
- Internal lemma libraries under `Lsc/Compiler/Proof/` (helpers nobody outside
  the proof tree references) stay there, with a 2–5-line module docstring.

Every theorem in a `*Theorems.lean` file must have a `/-- … -/` docstring
immediately above it (`@[simp]` and similar attributes may sit between). That
is a rule: `scripts/check-theorem-docs.sh` enforces it and runs in CI. State
the guarantee and its hypotheses in plain language — no proof talk, no
boilerplate.

```
/-- If `Inv` holds initially and is preserved, `claim a` does not fall. -/
theorem no_unauthorized_extraction …
-- rejected: /-- `foo` holds under the hypotheses in its type. -/
```

If Lean dependencies make the exact layout awkward, preserve the principle:
theorem intent and proof implementation should be independently understandable
and loadable.

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
