# Extension: `contract_spec` — Readable Specification Layer

Optional extension to the main [DESIGN.md](../DESIGN.md). Not currently required. Addresses the gap identified by comparison with evm-smith's spec/proof separation approach.

---

## Motivation

The current design proves things correctly but does not separate *what is claimed* from *how it is proved*. Theorems and proof terms live in the same file, interleaved with contract definitions. For a DeFi contract with 10 functions and 40 theorems, this is unreadable to an auditor who does not know Lean.

evm-smith's strongest practical idea is that the **human-readable specification is a first-class artifact**, structurally separate from the proofs. An auditor reads `Spec.lean`. A proof engineer writes `SpecProofs.lean`. Lean checks they agree.

This extension adds that separation to LSC via a `contract_spec` syntax construct.

---

## The Gap This Fills

When an auditor reviews an LSC contract today, they must read the contract source (readable) and the proof file (not readable without Lean expertise). There is no artifact that states guarantees as plain propositions in one place.

This does not change the trust boundary, the `simp + omega` invariant, linear types, or the compilation pipeline. It is an organizational improvement for auditability.

---

## Design

### The `contract_spec` Construct

```lean
contract_spec Counter where
  increment_increases_number :
      on_success Counter.increment ⊢
        $.number = old $.number +? 1

  increment_errors_when_paused :
      on_failure Counter.increment .Paused ⊢
        old $.paused = true

  pause_sets_paused :
      on_success Counter.pause ⊢
        $.paused = true
```

See [reference/COUNTER.md](../reference/COUNTER.md) for the full theorem list this would cover.

### What the Macro Generates

A Lean structure of propositions — no proofs:

```lean
structure CounterSpec where
  increment_increases_number  : Prop
  increment_errors_when_paused : Prop
  pause_sets_paused            : Prop

def Counter.spec : CounterSpec where
  increment_increases_number :=
    ∀ s s' log, runS Counter.increment s = .ok ((), s', log) →
      s'.storage.number.raw = s.storage.number.raw + 1
  -- ...
```

### The Proof Witness

```lean
instance : Counter.spec.proved where
  increment_increases_number := by intro s s' log h; simp [runS, Counter.increment] at h; omega
  -- ...
```

### `on_success` / `on_failure` / `old` Notation

Notation macros over `runS` — no new semantics:

```lean
-- on_success f ⊢ P  →  ∀ s s' log, runS f s = .ok ((), s', log) → P
-- on_failure f err ⊢ P  →  ∀ s, runS f s = .error err → P
-- old $.field  →  s.storage.field (initial state)
```

---

## Workflow

```
Counter.lean          ← contract definition
CounterSpec.lean      ← contract_spec block (propositions only) — optional
CounterProofs.lean    ← instance : Counter.spec.proved
```

All three can live in one file. The separation is a convention for reviewers.

---

## Auto-Generated Spec Entries

The macro can auto-generate entries for linear type obligations and field non-modification, marked `@[auto]`:

```lean
@[auto] increment_does_not_change_paused :
    on_success Counter.increment ⊢ $.paused = old $.paused
```

Auto-generated entries are proved by the framework. They appear in the spec so auditors can see them.

---

## Relationship to DESIGN

- **§3**: `contract_spec` is a new top-level syntax category alongside `contract`
- **§12**: If adopted, consider a spec legibility guideline — not currently a requirement
- **§13–14**: See [reference/COUNTER.md](../reference/COUNTER.md) and [reference/AMM.md](../reference/AMM.md)

---

## What This Does Not Do

- Does not make proofs deeper or change the Yul trust boundary
- Does not replace proofs — `instance : spec.proved` is still required
- Does not add `before_call` semantics (separate future concern)

---

## Why Not Just Write Theorems With Good Names?

A theorem in a proof file is a Lean term. A `contract_spec` entry is a proposition in a dedicated document with `on_success`/`old` notation and no proof terms. The test: can a security researcher who knows Solidity but not Lean read `CounterSpec.lean` and evaluate whether the guarantees are sufficient?
