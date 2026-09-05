---
name: implement-and-prove
description: Execute a contained project change that requires both implementation and Lean proof work. Use for features, refactors, theorem work, compiler changes, or bug fixes with proof obligations.
---

# Implement and Prove

Do not design implementation independently from proof.

## 1. Define the local contract

Before editing, write a compact blueprint:

- intended behavior / theorem;
- affected module API;
- implementation change;
- proof obligations;
- key supporting lemmas;
- trust-boundary impact;
- explicit non-goals.

If a major architectural choice is required, surface it instead of burying it in code.

## 2. Minimize context

Read module APIs and exported guarantees first. Load internals only where necessary.

Delegate contained exploration, coding, or theorem proving when useful. Return compact conclusions rather than exploration logs.

## 3. Implement and prove

Keep theorem intent easy to inspect.

Preferred default:

- `xxTheorems.lean`: natural-language meaning + theorem statement;
- `xxProof.lean`: proof body;
- one-line reference from theorem to proof where practical.

Use exported invariants and reusable lemmas rather than reopening unrelated internals.

## 4. Serialize Lean

**Only one Lean build/check process may run at any time across all agents.**

## 5. Finish properly

Before declaring completion, run the `simplify-and-modularize` skill.

A change is not complete merely because it builds and proves.
