# Project Goal

Build a **provable DeFi programming language compiling to EVM bytecode**.

The primary product goal is not exhaustive functional correctness. It is:

> **Make it practical to prove, under explicit assumptions, that deployed DeFi bytecode cannot be exploited for unauthorized wealth extraction or violation of critical asset/security invariants.**

Expected developer workflow:

`program + high-level security specs/invariants`
→ `generated proof obligations`
→ `AI constructs Lean proofs`
→ `Lean checks them`
→ `guarantee connects to deployed EVM bytecode`

Users are not expected to manually write most Lean proofs.

The language should eventually ship with a verified DeFi standard library that makes recurring anti-exploit guarantees easy to express and prove.

The project should optimize for:

- strong practical anti-exploit guarantees;
- small, explicit trust assumptions;
- simple language/proof/compiler architecture;
- reliable AI theorem proving with small context;
- modular code whose APIs and exported guarantees usually suffice without reading internals;
- aggressive deletion/refactoring of unnecessary complexity.
