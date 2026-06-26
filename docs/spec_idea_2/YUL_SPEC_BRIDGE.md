# Extension: `contract_spec` — Readable Specification Layer

> **Status**: Proposed extension to the main DESIGN.md. Inserts between §12 and §13. Addresses the gap identified by comparison with evm-smith's spec/proof separation approach.

---

## Motivation

The current design proves things correctly but does not separate *what is claimed* from *how it is proved*. Theorems and proof terms live in the same file, interleaved with contract definitions. For a DeFi contract with 10 functions and 40 theorems, this is unreadable to an auditor who does not know Lean.

evm-smith's strongest practical idea is not its `old`/`untouched`/`before_call` notation — it is that the **human-readable specification is a first-class artifact**, structurally separate from and independently inspectable to the proofs. An auditor reads `Spec.lean`. A proof engineer writes `SpecProofs.lean`. Lean checks they agree.

This extension adds that separation to LSC via a `contract_spec` syntax construct.

---

## The Gap This Fills

### What Is Currently Missing

When an auditor reviews an LSC contract today, they must read:

- The contract source (DSL) — readable
- The proof file — **not** readable without Lean expertise

There is no artifact that says: "here is what this contract guarantees, stated as plain propositions." The propositions exist, scattered across proof files, but they are not surfaced as a named, versioned document that stakeholders sign off on independently of proof details.

### What This Does Not Change

- The trust boundary is unchanged. Proofs still run at the ContractM level.
- The `simp + omega` invariant is unchanged.
- The linear type library is unchanged.
- The compilation pipeline is unchanged.

This is purely an organizational and communication improvement. It does not make proofs deeper. It makes them **auditable**.

---

## Design

### The `contract_spec` Construct

```lean
contract_spec Counter where
  -- Function postconditions
  increment_increases_number :
      on_success Counter.increment ⊢
        storage.number = old storage.number + 1

  increment_errors_on_overflow :
      on_failure Counter.increment .Overflow ⊢
        old storage.number = UInt256.max

  increment_errors_when_paused :
      on_failure Counter.increment .Paused ⊢
        old storage.paused = true

  pause_sets_paused :
      on_success Counter.pause ⊢
        storage.paused = true

  pause_errors_when_not_owner :
      on_failure Counter.pause .NotOwner ⊢
        old storage.caller ≠ old storage.owner

  -- Invariants (hold across all functions)
  invariant number_never_decreases :
      ∀ f ∈ Counter.functions, on_success f ⊢
        storage.number ≥ old storage.number
```

### What the Macro Generates

The `contract_spec` macro generates a **Lean structure of propositions — no proofs**:

```lean
structure CounterSpec where
  increment_increases_number  : Prop
  increment_errors_on_overflow : Prop
  increment_errors_when_paused : Prop
  pause_sets_paused            : Prop
  pause_errors_when_not_owner  : Prop
  number_never_decreases       : Prop

-- Concrete instantiation with real propositions:
def Counter.spec : CounterSpec where
  increment_increases_number :=
    ∀ s s' log,
      runS Counter.increment s = .ok ((), s', log) →
      s'.storage.number = s.storage.number + 1
  increment_errors_on_overflow :=
    ∀ s log,
      runS Counter.increment s = .error (.Overflow) →
      s.storage.number = UInt256.max
  -- ... etc
```

`Counter.spec` contains only propositions. It is a value of type `CounterSpec`. It can be `#print`ed, diffed, versioned, and handed to an auditor who knows nothing about Lean proofs.

### The Proof Witness

Separately — in a different file if desired — the proof engineer provides a **term that witnesses `Counter.spec`**:

```lean
-- CounterSpecProofs.lean
instance : Counter.spec.proved where
  increment_increases_number := by
    intro s s' log h
    simp [runS, Counter.increment] at h
    omega
  increment_errors_on_overflow := by
    intro s log h
    simp [runS, Counter.increment] at h
  -- ... etc
```

Lean checks that every field of `Counter.spec.proved` has exactly the type stated in `Counter.spec`. The propositions cannot drift from the proofs — Lean's type checker enforces the match. If someone changes `Counter.increment` in a way that breaks a proof, the `instance` fails to elaborate. If someone changes a proposition in `contract_spec` to state something weaker, the `instance` might still compile but now proves something different — which is visible in the diff of `contract_spec`.

### `on_success` / `on_failure` / `old` Notation

These are **notation macros over `runS`**, not new semantic constructs. They exist to make `contract_spec` blocks readable to non-Lean-experts. They desugar completely:

```lean
-- on_success f ⊢ P desugars to:
∀ (s s' : _) (log : _), runS f s = .ok ((), s', log) → P

-- on_failure f err ⊢ P desugars to:
∀ (s : _), runS f s = .error err → P

-- old storage.field (inside on_success or on_failure) desugars to:
s.storage.field   -- the initial state s, not the final s'
```

No new axioms. No new semantics. `simp` and `omega` still close every proof that was already closable. The notation exists entirely in the surface layer.

The choice to add `old` as notation — rather than require explicit `s.storage.field` — is motivated by readability of the spec structure. An auditor reading `storage.number = old storage.number + 1` understands immediately: final value equals initial value plus one. The same auditor reading `s'.storage.number = s.storage.number + 1` has to track two variable names whose meaning is not self-evident.

### Invariants

```lean
invariant number_never_decreases :
    ∀ f ∈ Counter.functions, on_success f ⊢
      storage.number ≥ old storage.number
```

This desugars to a universally quantified proposition over the contract's function set. `Counter.functions` is a `Finset` of `ContractM` terms, generated by the `contract` macro (already available as §3's macro output). The invariant is one proposition in the spec structure, witnessed once, and covers all functions.

For contracts with complex invariants this is more useful than per-theorem statements because it names the invariant explicitly as a contract-level property rather than a collection of similarly named function-level theorems.

---

## Workflow

### Authoring

```
Counter.lean          ← contract definition (DSL)
CounterSpec.lean      ← contract_spec block (propositions only)
CounterProofs.lean    ← instance : Counter.spec.proved (proofs)
```

The separation is a convention, not enforced by the macro. All three can live in one file. The point is that `CounterSpec.lean` is the document that gets reviewed, versioned, and signed off on. It has no proof terms. It can be read by a security researcher who knows Solidity but not Lean.

### Audit Workflow

1. Auditor reads the DSL in `Counter.lean` — what the contract does.
2. Auditor reads `CounterSpec.lean` — what the contract guarantees.
3. Auditor confirms the propositions match their security model.
4. They do not need to read `CounterProofs.lean`. Lean's kernel has already checked it.

Steps 1–3 require no Lean knowledge. Step 4 is Lean's job.

This is the same trust model as a compiled binary: you trust the compiler (Lean kernel), you inspect the source (spec), you don't read the assembly (proof terms).

### Versioning

`CounterSpec.lean` can be diffed across versions. A change to a postcondition is visible as a source diff on a human-readable file. This matters for protocol upgrades: "what changed about what this contract guarantees between v1 and v2" is answerable by reading a diff, not by reverse-engineering proof changes.

---

## What Counts as a Well-Formed Spec

A `contract_spec` block is **complete** if it covers:

1. Every external function: at least one success postcondition and every named error condition.
2. Every storage field that is modified by any function: at least one theorem per field per function that modifies it.
3. Every linear type obligation: `FlashLoanReceipt` repayment, `ReentrancyLock` state, etc. — these are auto-generated (see below).

### Auto-Generated Spec Entries

The `contract_spec` macro auto-generates spec entries for linear type obligations and field non-modification (the untouched cases). These appear in the spec structure but are marked `@[auto]`:

```lean
-- Auto-generated because increment does not write storage.paused:
@[auto] increment_does_not_change_paused :
    on_success Counter.increment ⊢ storage.paused = old storage.paused

-- Auto-generated because contract uses FlashLoanReceipt:
@[auto] flashloan_always_repaid :
    ∀ s s' log, runS Pool.flashLoan s = .ok ((), s', log) →
      s'.storage.loanOutstanding = false
```

Auto-generated entries are proved automatically by the framework (`by rfl` for field non-modification, by linearity erasure proofs for linear types). They appear in the spec so the auditor can see them, but the proof engineer does not write them.

The auditor can audit the `@[auto]` entries too — but their provenance is clear (generated, not authored), and the auto-generation rule is simple enough to inspect.

---

## Relationship to the Existing Design

### §3 (Macro Layer)

`contract_spec` is a new top-level syntax category alongside `contract`. It adds one item to the list of what the macro generates: a `structure` of `Prop` fields plus a concrete instantiation value. The elaboration step for `contract_spec` validates that every named function in the spec exists in the corresponding `contract` definition.

### §12 (Proof Ergonomics)

Add a fifth design invariant: **the spec legibility invariant**. Every external function must have a corresponding `contract_spec` entry. The spec entry must be readable by a developer who understands the domain but does not know Lean. If a proposition requires Lean-specific phrasing to state, the spec DSL notation is inadequate — extend `on_success`/`on_failure`/`old` until it can be stated readably.

### §13 and §14 (Reference Contracts)

The Counter and AMM reference sections each gain a `contract_spec` block alongside the existing theorem list. The theorem list in §13 becomes the body of `CounterSpec`. The required theorems in §14 become the body of `AMMSpec`.

---

## What This Does Not Do

**It does not make proofs deeper.** The trust boundary between ContractM and Yul is unchanged. `compile_correct` is still a v2 goal. This extension lives entirely above the trust boundary.

**It does not replace proofs with specifications.** A `contract_spec` without a corresponding `instance : spec.proved` is a statement with no proof. The Lean kernel will not accept a contract as verified without the witness. The spec and the proof are both required.

**It does not add `before_call` semantics.** That requires extending `ContractM` with call observability, which touches the execution model and the Yul emitter. It is a separate concern. If added later, `before_call` propositions would appear in `contract_spec` blocks using the same notation machinery.

---

## Why Not Just Write Theorems With Good Names?

The current design already has well-named theorems. The difference is structural, not cosmetic:

- A theorem in a proof file is a Lean term. Reading it requires knowing Lean syntax, understanding `runS`, tracking variable names, and distinguishing hypotheses from conclusions.
- A `contract_spec` entry is a proposition in a dedicated document, with `on_success`/`old` notation that reads like an English spec, auto-generated entries clearly labeled, and no proof terms anywhere in the file.

The auditor workflow is the real test: can a security researcher who knows Solidity, knows the DeFi domain, but does not know Lean, read `CounterSpec.lean` and tell you whether the stated guarantees are sufficient for their security model? With the current design, no. With this extension, yes.

That is the only thing this extension adds. It is not a small thing.
