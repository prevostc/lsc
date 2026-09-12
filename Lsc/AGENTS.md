# Guarantee modules (`Lsc/`)

A **guarantee module** exports a theorem referenced by `Checks.lean`,
`docs/internals/*.md` or `docs/guide/*.md`, or another module's *statement* (not
just its proof). Split `Foo.lean` as:

- `FooTheorems.lean`: for each exported theorem, a plain-language docstring
  (what it guarantees, under which hypotheses, one to four sentences, no proof
  talk), the statement verbatim, and `:= Foo.Proof.thm_name` (or
  `:= by exact Foo.Proof.thm_name` if elaboration needs it). No other proof
  code.
- `FooDefs.lean` (or the existing defs module), imported by both: `structure`s,
  `def`s, `abbrev`s the statement needs (`EvmTraceRunAll`, `TransportSetup`,
  `R`, `Inv`, …).
- `FooProof.lean`: actual proofs (`theorem thm_name … := by …`) in namespace
  `<orig>.Proof`, plus all private helpers. Imports whatever it needs.

Downstream modules import `FooTheorems`, never `FooProof`. Fully-qualified names
used by `Checks.lean` must not change — the Theorems-file theorem keeps the
original namespace and name.

Compiler: Theorems/Defs of a `Proof/*` guarantee module go **up** to
`Lsc/Compiler/<Name>Theorems.lean` (and `…Defs.lean` if needed); the proof stays
`Lsc/Compiler/Proof/<Name>Proof.lean`. Internal lemma libraries under
`Lsc/Compiler/Proof/` (helpers nobody outside the proof tree references) stay
there, with a 2–5-line module docstring.

Every theorem in a `*Theorems.lean` file must have a `/-- … -/` docstring
immediately above it (`@[simp]` and similar attributes may sit between).
`scripts/check-theorem-docs.sh` enforces this in CI. No proof talk, no
boilerplate.

```
/-- If `Inv` holds initially and is preserved, `claim a` does not fall. -/
theorem no_unauthorized_extraction …
-- rejected: /-- `foo` holds under the hypotheses in its type. -/
```

If Lean dependencies make the exact layout awkward, preserve the principle:
theorem intent and proof implementation should be independently understandable
and loadable.
