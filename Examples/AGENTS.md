# `Examples/<Name>/`

Exactly:

- `Contract.lean` — the contract only
- `Spec.lean` — invariant, claim, authorisation predicates, and any
  binding/`TransportSetup` definitions — what we claim, no theorems
- `Theorems.lean` — every exposed theorem (Tx-level, security, compiler
  instance, bytecode); plain-language docstring and a one-line body referencing
  `Proofs/…`
- `Proofs/` — `Tx.lean`, `Security.lean`, `Compile.lean`, `EndToEnd.lean`, plus
  helpers. Nothing outside `Proofs/` contains proof code beyond one-line
  references. Compile witnesses stay in `Proofs/Compile.lean`
- optional `Tests.lean` — executable smoke `#guard`s
- `README.md` — what the contract does, what is proved in prose, one line per
  file
- `compiled/` — Yul, labelled Asm, bytecode, ABI, heimdall decompile; written
  in place by `scripts/export_bytecode.sh`, not copied from `out/`

`Checks.lean` imports `Examples.<Name>.Theorems` only. This is the example-level
instance of the Theorems/Proof split in `Lsc/AGENTS.md`; the docstring checker
treats `Theorems.lean` as a Theorems file (glob `*Theorems.lean` matches).
