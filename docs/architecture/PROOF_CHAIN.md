# Proof Chain

The end-to-end theorem for a contract `C` is assembled from four independently checked links.
Each link's status is tracked here; a change to any link must update this file.

## Target chain

```
Tx theorem  ──(1) core_denote (rfl)──  Core
Core        ──(2) toYul_correct──────  Yul (powdr yul-semantics `Run`)
Yul         ──(3) powdr compileObject_correct──  bytecode (powdr evm-semantics)
bytecode    ──(4) EndToEnd glue──────  bytecode-level anti-exploit theorem
```

1. **Surface → Core.** `f.core_denote : Core.denote schema f.core args = f args := rfl`. Emitted
   by the untrusted reifier, checked by the kernel. Status: **proved** for every reified function.
2. **Core → Yul.** `toYul_correct`: for every Core program `c`, every world `w` related to a Yul
   state by the layout relation `R`, `Core.denote c` and `YulSemantics.Run (toYul c)` agree on
   outcome (return data, revert data, storage under `R`, logs); external calls are simulated under
   `ExternalsRealized` and "responses follow the interface model". Status: **incomplete** (S1
   for the call-free fragment, S2 for `letCall`). Current state: `Lsc/Compiler/Yul.lean` emits
   the call-free fragment; `Lsc/Compiler/Correctness.lean` states `toYul_correct` for one
   `FnDef` (`sorry`, not imported by `Lsc.lean`). The statement is **tested** for Counter and
   Token by the differential harness in `Lsc/Compiler/YulTests.lean` (powdr's Yul interpreter vs
   `Tx.run`; compiled by powdr: Counter 480/494 bytes, Token 1650/1742). Known weaknesses of the
   stated theorem: `R` relates logs only by length and address (event data not yet related), and
   the dispatcher (`runtimeBlock`: selector → `toYulFn`, calldata decoding) has no theorem yet.
3. **Yul → bytecode.** powdr `YulEvmCompiler.compileObject_correct`, axioms exactly
   `propext`, `Classical.choice`, `Quot.sound`. Status: **proved** (external, pinned).
4. **Glue.** Generic theorem: a `Security` result about `Tx.run` traces implies the same statement
   about EVM call sequences on the compiled bytecode, storage read through `R`, under the
   hypotheses listed in `TRUSTED_COMPUTING_BASE.md`. Status: **incomplete** (S1).

## Status of the v3 chain being replaced (for the record)

- Core → bytes: general codegen existed; correctness was proved only for Counter scenarios by
  monolithic symbolic execution (~9.5k lines), never linked to `Tx.run`, never for Token/Vault.
  Deleted.
- Home-grown EVM machine → EvmYulLean: word and decode lemmas only, no step refinement. Deleted.
- Bytecode → real EVM: `#eval` only. Replaced by powdr's conformance-tested semantics plus a
  revm/anvil differential harness.

## Hypotheses that appear in every end-to-end theorem

Sufficient gas for each call; keccak oracle injective on the keys used; `Conforms I addr` for
each declared external address; powdr `ExternalsRealized`; fork = Osaka; adversary model scope
per `SECURITY_MODEL.md`.

## Rules

- No `sorry`, `native_decide`, `bv_decide` or new `axiom` in any link; CI pins the axiom footprint
  of every end-to-end theorem.
- `Security` depends only on `Lang`; `Compiler` depends on `Core` and powdr, never on `Security`;
  only `EndToEnd` sees both.
