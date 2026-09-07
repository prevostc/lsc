# Proof Chain

The end-to-end theorem for a contract `C` is assembled from four independently
checked links. A change to any link must update this file and
`TRUSTED_COMPUTING_BASE.md`.

```
Tx theorem  ──(1) core_denote (rfl)──  Core
Core        ──(2) toYul_correct──────  Yul (powdr `Run`)
Yul         ──(3) compile_correct────  bytecode (powdr `Steps`)
bytecode    ──(4) EndToEnd glue──────  bytecode-level anti-exploit theorem
```

| Link | Theorem(s) | File | Status | Fragment | Examples |
|------|------------|------|--------|----------|----------|
| 1 Spec→Core | `f.core_denote` | `Lsc/Lang/Reify.lean` | proved | both | Counter, Token, Vault, AMM |
| 2 Core→Yul | `toYulFn_correct_callFree`, `runtimeBlock_correct_callFree`; instances `counter_correct`, `token_correct`, `counter_dispatch_correct`, `token_dispatch_correct` | `Proof/Core.lean`, `Proof/Dispatch.lean` | proved | S1 | Counter, Token |
| 2 Core→Yul | `toYulFn_correct_ext`, `runtimeBlock_correct_ext`; instance `vault_correct_ext` | `Proof/CoreExtSim.lean`, `Proof/DispatchExt.lean`, `Proof/Vault.lean` | proved | S2 | Vault (one binding) |
| 3 Yul→EVM | `compile_correct`, `steps_halted_unique` | powdr `YulEvmCompiler`, `Proof/EvmDet.lean` | proved | both | runtime of the above |
| 4 Glue | `bytecode_call_correct`, `bytecode_trace_all` | `EndToEnd.lean` | proved | S1 | Token |
| 4 Glue | `bytecode_call_correct_ext`, `yul_progress` | `EndToEndExt.lean`, `Proof/ProgressCore.lean` | proved | S2 | Vault |
| Security | `token_bytecode_no_unauthorized_extraction`, `token_bytecode_solvent` | `Examples/TokenEndToEnd.lean` | proved | S1 | Token |
| Security | `vault_bytecode_no_unauthorized_extraction`, `vault_bytecode_solvent` | `Examples/VaultEndToEnd.lean` | proved | S2 | Vault |
| Security | `amm_no_unauthorized_extraction`, `amm_solvent` | `Examples/AmmSecurity.lean` | proved | spec only | AMM |
| Deploy | `compileObject_correct` | powdr | not covered | — | constructor / init calldata |

S1 is the call-free fragment (`CallFree` / `M1Frag`). S2 is `S2Frag` (`CallFree`
plus `Op.call` / `Stmt.call`), one `Binding`. Link 1 is `Core.denote schema f.core
args = f args` (or `Core.denoteAWord` / `Core.denoteAUnit` when the surface is
Amount-typed). Bytecode glue talks about `Core.denote` (Nat); Vault Amount ABI is
identified via `deposit.core_denote` / `withdraw.core_denote`.

## Hypotheses common to all links

See `TRUSTED_COMPUTING_BASE.md`. S1 Token glue uses `ExternalsRealized.none` and
does not mention `Conforms`. S2 still needs `Conforms` / `RelyEnv` / a realised
external model (`CallsRealized`, `CallsTotal`). No `sorry`, `native_decide`,
`bv_decide`, or project `axiom` in any link; CI pins the axiom footprint in
`Checks.lean`. `Security` depends only on `Lang`; `Compiler` depends on `Lang`
and powdr, never on `Security`; only `EndToEnd*.lean` see both.

## Open items

- **Deploy / constructor.** `compileObject_correct` starts from empty calldata;
  constructor arguments currently use `calldataload`. Runtime calls are unaffected.
- **AMM through the compiler.** Needs a multi-binding `toYulFn_correct_ext`.
- **S2 post-world.** Vault's transported world is the fault-oracle-adjusted fold, while
  Token relates `Security.run` directly; unifying them is cosmetic (Security is `∀ w`).
