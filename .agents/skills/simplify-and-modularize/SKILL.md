---
name: simplify-and-modularize
description: Review completed work for deletion, refactoring, API simplification, proof-dependency reduction, and context isolation. Use after substantial implementation or proof milestones.
---

# Simplify and Modularize

Treat deletion as progress.

Ask:

- What became unnecessary because of what we learned?
- Which abstractions exist only because of historical decisions?
- Are multiple representations solving the same problem?
- Can stronger invariants or module APIs replace helper layers?
- Can Lean replace custom machinery?
- Did temporary scaffolding silently become architecture?
- If rebuilt today, would this subsystem still look like this?

## Module/context test

A downstream agent should ideally need only:

- module purpose;
- public API;
- exported guarantees/invariants;
- assumptions/dependencies.

It should not need implementation internals for unrelated work.

Refactor boundaries that leak internals into downstream proofs or code.

## Completion gate

Before moving on:

1. verify the intended new guarantee;
2. identify obsolete code/layers;
3. delete, collapse, or refactor where justified;
4. simplify APIs and theorem dependencies;
5. remove or explicitly promote temporary scaffolding;
6. update the concise project/architecture documents.

Then ask:

> **What new end-to-end guarantee can we establish now that we could not establish before?**

If the answer is weak or none, challenge whether the milestone was worthwhile.
