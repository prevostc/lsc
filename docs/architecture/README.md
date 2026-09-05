# Architecture Documents

These documents record **decisions discovered by architecture reviews**, not guesses made in advance.
They were first produced by the September 2026 review (verdict: SIMPLIFY).

- `LANGUAGE_ARCHITECTURE.md` — surface, Core (the only IR), arithmetic domains, proof UX, backend, toolchain.
- `SECURITY_MODEL.md` — the anti-exploit formalization (`Inv`/`claim`/`Auth`), Interface model, adversary scope, language vs stdlib vs protocol boundary.
- `PROOF_CHAIN.md` — the four links from a `Tx` theorem to deployed bytecode and their status.
- `MODULE_MAP.md` — module boundaries and dependency rules.
- `TRUSTED_COMPUTING_BASE.md` — what every end-to-end theorem trusts or assumes.
- `YUL_TARGET.md` — the contract with powdr's Yul semantics and compiler: which theorems we consume, the Core → Yul mapping, keccak and revert-atomicity decisions.

Keep them concise and decision-oriented. Changes to semantics, compilation, trusted assumptions,
or proof boundaries must update `PROOF_CHAIN.md` and `TRUSTED_COMPUTING_BASE.md`.

Agents working on local tasks should rely on these contracts and module APIs rather than
repeatedly reconstructing the whole system.
