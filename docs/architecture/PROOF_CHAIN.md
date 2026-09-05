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

1. **Surface → Core.** `f.core_denote` by `rfl`, emitted by the untrusted reifier, kernel-checked.
   Shape is `Core.denote schema f.core args = f args` for word-typed programs, or
   `Core.denoteAWord` / `Core.denoteAUnit` when the surface is Amount-typed (`INTERFACE_MODEL.md`).
   Status: **proved** for every reified function. The compiler obligation `toYul_correct` still
   talks about `Core.denote` (Nat). Amount programs therefore need a future `toNat`/`ofNat`
   agreement lemma between `denoteAWord`/`denoteAUnit` and `Core.denote` before the bytecode
   link is as tight as for `Nat` programs.
2. **Core → Yul.** Two theorems in `Lsc/Compiler/Correctness.lean` (`sorry`, not imported by
   `Lsc.lean`): `toYulFn_correct` (one runtime entrypoint, `V' = []`) and
   `runtimeBlock_correct` (dispatcher). Hypotheses: `Γ.st.Lawful c.fields` (nine update equations,
   generated as `C.schema_lawful`), `KeccakSep c κ`, `ctxRel` (`static = false`, `halted = none`,
   `CtxWF`), `R` including `WorldWF` and `logsRel` via `List.Forall₂` with `Γ.ev.build` /
   `abiBytes` witnesses. Args are `decodeArgs f st0.env.calldata` (no `calldataRel`). The
   `letCall` case (S2) still quantifies existentially over the fault oracle. Status:
   **M2a proved** for every Counter runtime entrypoint (`Lsc.Compiler.counter_correct`, and the
   named `counter_increment_correct` / `counter_incrementBy_correct` /
   `counter_decrement_correct` / `counter_get_correct`; axioms `propext` / `Classical.choice` /
   `Quot.sound`) via `core_sim` on `M1Frag` (`load`, `addChecked`, `subChecked`, `Op.pure`,
   `store`, one-word `emit`, 0-arg `require` with `eq`/`ne`, `letOp`/`seq`/`stmtTail`/`letPure`
   id / `ite` / `opTail` word `ret`). Params `n ≤ 1` with `calldataload`. General
   `toYulFn_correct` / dispatcher remain `sorry`. `ctxRel` does not bound `calldata.length`, so
   the general `runtimeBlock_correct` is not proved (Yul `calldatasize` wraps at `2^256`).
   Emitter: temp-free nested Yul, gated by `coreWF` / `Nodup`. Tested for Counter and Token by
   `Lsc/Compiler/YulTests.lean`.
3. **Yul → bytecode.** powdr `YulEvmCompiler.compileObject_correct`, axioms exactly
   `propext`, `Classical.choice`, `Quot.sound`. Status: **proved** (external, pinned).
   Known gap for the deploy object: `compileObject_correct` starts from `L.initState` (empty
   calldata), while constructor arguments are currently read with `calldataload`. The emitter
   must switch to the Solidity convention (arguments appended to the creation code and read with
   `codecopy`) before the constructor link can be proved. Runtime calls are unaffected.
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

Sufficient gas for each call; keccak oracle injective on the keys used; per-binding `Conforms`
(including non-interference) and `RelyEnv` (`INTERFACE_MODEL.md`, `TRUSTED_COMPUTING_BASE.md`);
powdr `ExternalsRealized`; fork = Osaka; adversary model scope per `SECURITY_MODEL.md`.

## Rules

- No `sorry`, `native_decide`, `bv_decide` or new `axiom` in any link; CI pins the axiom footprint
  of every end-to-end theorem.
- `Security` depends only on `Lang`; `Compiler` depends on `Lang` (`Core`, `Interface`) and
  powdr, never on `Security`; only `EndToEnd` sees both.
