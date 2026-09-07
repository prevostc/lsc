# Proof Chain

The end-to-end theorem for a contract `C` is assembled from four independently checked links.
Each link's status is tracked here; a change to any link must update this file.

## Target chain

```
Tx theorem  ──(1) core_denote (rfl)──  Core
Core        ──(2) toYul_correct──────  Yul (powdr yul-semantics `Run`)
Yul         ──(3) powdr compile_correct──  bytecode (powdr evm-semantics)
bytecode    ──(4) EndToEnd glue──────  bytecode-level anti-exploit theorem
```

1. **Surface → Core.** `f.core_denote` by `rfl`, emitted by the untrusted reifier, kernel-checked.
   Shape is `Core.denote schema f.core args = f args` for word-typed programs, or
   `Core.denoteAWord` / `Core.denoteAUnit` when the surface is Amount-typed (`INTERFACE_MODEL.md`).
   Status: **proved** for every reified function. The compiler obligation `toYul_correct` still
   talks about `Core.denote` (Nat). Amount programs therefore need a future `toNat`/`ofNat`
   agreement lemma between `denoteAWord`/`denoteAUnit` and `Core.denote` before the bytecode
   link is as tight as for `Nat` programs.
2. **Core → Yul.** Two layers in `Lsc/Compiler/Correctness.lean` (`sorry`, not imported by
   `Lsc.lean`) plus S1 proofs in `Lsc/Compiler/Proof/`:
   - **S1 (call-free fragment, no `sorry`):** `toYulFn_correct_callFree` (`Proof/Core.lean`) and
     `runtimeBlock_correct_callFree` (`Proof/Dispatch.lean`). Extra hypothesis `CallFree` (alias
     of `M1Frag`): every Core constructor Vault uses except `Op.call`/`Stmt.call` — ctx reads
     including `selfAddress`, checked `mul`/`div`/`mulDiv*`, `emit` of arity 0/1/3, and
     `addr`/`flag` (single-word) returns. Still excluded: wrapping `letPure`, other
     `require`/`revert`/`emit` arities, `pair` returns. `ctxRel` includes
     `calldata.length < 2^256` so `calldatasize` agrees with `List.length`.
     `token_correct` / `counter_correct` instantiate the function theorem;
     `token_dispatch_correct` / `counter_dispatch_correct` instantiate the dispatcher. Axioms
     `propext` / `Classical.choice` / `Quot.sound`. Vault `deposit`/`withdraw` are `S2Frag`
     (they `Stmt.call`); `constructor` is excluded by `f.kind ≠ .constructor`.
   - **S2 (external calls, backward):** dialect `yulD calls := evmWithExternal calls .none .none`.
     Glue (`Conforms`, `NoInterfere`, `RX`, `Realizes`) is `Lsc/Compiler/Externals.lean`.
     `ToYulFnCorrectExt` / `RunCommittedExt` are in `Correctness.lean`. The main theorem is
     **backward**: `∀` Yul run of a `Conforms` `calls`, `∃ fo` such that Core under
     `{w with faults := fo}` predicts it. `Realizes` is not a hypothesis (only `_exists`).
     Soundness fixes: `logsRel` vs `selfLogs` (filter by `st.env.address`); `boolOpt` return
     check requires empty or `≥ 32` bytes with `mload(0x80) = 1`.
     **Status:** `step_descend` / `execStmts_append_inv` (`Proof/Descend.lean`) + scoped
     `emitExtCall` (temps `_tok_*`/`_ok_*` live in a Yul `{ … }` so `restore` drops them and
     `Inv.venv` is structural). Call-free backward `toYulFn_correct_ext` (`Proof/CoreExt.lean`)
     is **proved**: invert `Run` → descend → S1 → `EVM.evm_deterministic`. Extra `hstab` /
     `haddr` close `RX` (call-free `sstore` updates `storageOf` at the executing address;
     `ignoresLocal` is foreign `accountKey` only). `Op.call`/`Stmt.call`
     (`op_sim_call_bwd`, `core_sim_ext`) cover `S2Frag` including Vault `deposit`/`withdraw`.
     `RuntimeBlockCorrectExt` is in `Correctness.lean`; proof `runtimeBlock_correct_ext`
     (`Proof/DispatchExt.lean`) is **proved** (M3): invert the call-free guard/selector/`switch`
     prefix, then `toYulFn_correct_ext` on the selected body. Axioms: `propext` /
     `Classical.choice` / `Quot.sound`. Hypotheses: `Γ.st.Lawful`, `KeccakSep`, `ctxRel`, `R`,
     `RX`, `ignoresLocal`, `Conforms`, `BindWF`, `hslot` / `coreAvoids`. Args are
     `decodeArgs f st0.env.calldata`.
     **S2 step (this session):** `step_ofState` / `ofState_noExt_halt` / `execStmts_normal_ofState` close `hstab` for `noExt` Yul (`selfdestruct` excluded). `core_sim_ext_callFree` is proved (S1 `core_sim` + descend + `callFree_run_faults` + `RX_callFree`). `toYulFn_correct_ext` dropped global `haddr`/`hstab` in favor of `hslot` (`callFree_preserves_addr` / BindWF scalar) + `ofState_noExt_halt`. S2 per-function backward theorem proved for `S2Frag`; Vault runtime functions all covered (`vault_correct_ext` / `vault_deposit_correct_ext` / `vault_withdraw_correct_ext`). `core_sim_ext` has no extra `hCallFree`. Dispatcher: `runtimeBlock_correct_ext` (M3).
   Emitter: temp-free nested Yul, gated by `coreWF` / `Nodup`. Tested for Counter and Token by
   `Lsc/Compiler/YulTests.lean`.
3. **Yul → bytecode.** Runtime: powdr `YulEvmCompiler.compile_correct` (consumed by
   `bytecode_call_correct`). Deploy: `compileObject_correct`. Axioms exactly
   `propext`, `Classical.choice`, `Quot.sound`. Status: **proved** (external, pinned).
   Known gap for the deploy object: `compileObject_correct` starts from `L.initState` (empty
   calldata), while constructor arguments are currently read with `calldataload`. The emitter
   must switch to the Solidity convention (arguments appended to the creation code and read with
   `codecopy`) before the constructor link can be proved. Runtime calls are unaffected.
4. **Glue.** S1, call-free (`Lsc/Compiler/EndToEnd.lean`,
   `Lsc/Examples/TokenEndToEnd.lean`):
   - `bytecode_call_correct`: one compiled call matches the dispatcher conclusion
     (`runtimeBlock_correct_callFree` → `runCommitted_lift_run` → `compile_correct`).
   - `steps_halted_unique` (`Proof/EvmDet.lean`): two halted `Steps` runs from the same
     start state are equal (`Step` is deterministic; a done frame has no successor).
   - `EvmCallRun`: `∃ b, ∀` matching start states with gas `≥ b`, a halted run exists
     **and** every halted run has the same post-storage (identified with the
     `compile_correct` run via `steps_halted_unique`).
   - `bytecode_trace_transport`: a list of encoded Core calls has an `EvmTraceRun`
     whose storage is `storageRel` of `coreRun` (logs stripped each step).
   - `bytecode_trace_all` / `EvmTraceRunAll`: the same post-storage for every matching
     start state (needs one `EvmStartOK` witness per call so uniqueness is non-vacuous).
   - `token_bytecode_no_unauthorized_extraction` / `token_bytecode_solvent`: `∀ σ'`,
     `EvmTraceRunAll` implies the Security conclusion, storage read through `R` /
     `mapSlot1 evmKeccak 2`. Companions `*_exists` keep the predicted `EvmTraceRun`.
   Top-level revert rollback is a modelling assumption (`TRUSTED_COMPUTING_BASE.md`).
   Status: **proved (S1, universal over halted matching executions)**.
   S2 (`EndToEndExt.lean`, `VaultEndToEnd.lean`): `CallsTotal` + `yul_progress` produce
   a Yul `Run`; `compile_correct` + `steps_halted_unique` give `EvmCallRunExtAll` /
   `EvmTraceRunExtAll` (Token's `EvmTraceRunAll` shape). Core at a witnessing `fo`
   predicts unique halted post-storage. Vault `deposit`/`withdraw` are Nat-returning;
   ABI words agree via `f.core_denote` (`deposit_core_toNat`).
   `vault_bytecode_no_unauthorized_extraction` is `∀ σ' ξ', EvmTraceRunExtAll →`
   `vaultClaimRead σ a ≤ vaultClaimRead σ' a` (shares schema, not a Spec∧Yul
   conjunction). Companions `*_exists` keep a predicted `EvmTraceRunExt`.
   `vault_bytecode_solvent` is `vaultSolventRead α σ' ξ' self assetAddr`:
   finite support of `vaultClaimRead` on `a < wordBound` from `σ'`, summed and
   bounded by holdings `(α.ofState (mkEvmStateExt [] σ' ξ' …) assetAddr).balances self`.
   Derived from Spec `Inv`/`Solvent` plus `storageRel`/`RX` at the last EVM-synced
   world (trailing `env` may raise Spec holdings while `ξ'` stays at the last call).
   powdr adequacy is not used. The converse (every EVM execution is a Yul run) is
   **not** claimed. Foreign `ξ` is threaded; `α.ofState_foreign` plus initial `hRX`
   re-establish `RX` at each `mkEvmStateExt`. `ξ'` is read from the halted EVM
   state (`postForeign`).

## Status of the v3 chain being replaced (for the record)

- Core → bytes: general codegen existed; correctness was proved only for Counter scenarios by
  monolithic symbolic execution (~9.5k lines), never linked to `Tx.run`, never for Token/Vault.
  Deleted.
- Home-grown EVM machine → EvmYulLean: word and decode lemmas only, no step refinement. Deleted.
- Bytecode → real EVM: `#eval` only. Replaced by powdr's conformance-tested semantics plus a
  revm/anvil differential harness (`scripts/difftest.sh`: Counter/Token `Tx.run` vs Osaka anvil).

## Hypotheses that appear in every end-to-end theorem

See `TRUSTED_COMPUTING_BASE.md`. S1 call-free glue (`bytecode_call_correct`, Token
bytecode theorems) uses `ExternalsRealized.none` and does not mention `Conforms`.
S2 / `Op.call` programs still need `Conforms` / `RelyEnv` / a realised external model.

## Rules

- No `sorry`, `native_decide`, `bv_decide` or new `axiom` in any link; CI pins the axiom footprint
  of every end-to-end theorem.
- `Security` depends only on `Lang`; `Compiler` depends on `Lang` (`Core`, `Interface`) and
  powdr, never on `Security`; only `EndToEnd` sees both.
