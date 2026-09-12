# Proof Chain

The end-to-end theorem for a contract `C` is assembled from four independently
checked links. A change to any link must update this file and
`TRUSTED_COMPUTING_BASE.md`.

```
Tx theorem  ──(1) core_denote (rfl)──  Core
Core        ──(2) toYulFn_correct_*──  Yul (powdr `Run`)
Yul         ──(3) compile_correct────  bytecode (powdr `Steps`)
bytecode    ──(4) EndToEnd glue──────  bytecode-level anti-exploit theorem
```

How a `ContractDef` becomes hex/ABI (functions, not theorems):
[`COMPILER_PIPELINE.md`](COMPILER_PIPELINE.md).

| Link | Theorem(s) | File | Status | Fragment | Examples |
|------|------------|------|--------|----------|----------|
| 1 Spec→Core | `f.core_denote` | `Lsc/Lang/Reify.lean` | proved | both | Counter, Token, Vault, AMM |
| 2 Core→Yul | `toYulFn_correct_callFree`, `runtimeBlock_correct_callFree`; instances `counter_correct`, `token_correct`, `counter_dispatch_correct`, `token_dispatch_correct` | `CoreTheorems.lean`, `DispatchTheorems.lean`, `Examples/Counter/Theorems.lean`, `Examples/Token/Theorems.lean` | proved | S1 | Counter, Token |
| 2 Core→Yul | `toYulFn_correct_ext`, `runtimeBlock_correct_ext`; instances `vault_correct_ext`, `amm_correct_ext` | `CoreExtSimTheorems.lean`, `DispatchExtTheorems.lean`, `Examples/Vault/Theorems.lean`, `Examples/Amm/Theorems.lean` | proved | S2 | Vault (one binding); AMM (two `IERC20`) |
| 3 Yul→EVM | `compile_correct`, `steps_halted_unique` | powdr `YulEvmCompiler`, `EvmDetTheorems.lean` | proved | both | runtime of the above |
| 4 Glue | `bytecode_call_correct`, `bytecode_trace_all` | `EndToEndTheorems.lean` | proved | S1 | Token |
| 4 Glue | `bytecode_call_correct_ext`, `yul_progress` | `EndToEndExtTheorems.lean`, `ProgressCoreTheorems.lean` | proved | S2 | Vault, AMM |
| Security | `token_bytecode_no_unauthorized_extraction`, `token_bytecode_solvent` | `Examples/Token/Theorems.lean` | proved | S1 | Token |
| Security | `vault_bytecode_no_unauthorized_extraction`, `vault_bytecode_solvent` | `Examples/Vault/Theorems.lean` | proved | S2 | Vault |
| Security | `amm_bytecode_no_unauthorized_extraction` | `Examples/Amm/Theorems.lean` | proved | S2 | AMM |
| Deploy | `compileObject_correct` / `bytecode_deploy_correct` | powdr + `DeployTheorems.lean` | Yul ctor proved; EVM args gap | S1 | Token constructor (call-free); Counter has no ctor args |


S1 is the call-free fragment (`CallFree` / `M1Frag`). S2 is `S2Frag` (`CallFree`
plus `Op.call` / `Stmt.call`) over a list of `BindEnv` packages (Vault is the
singleton `[assetB]`; AMM is `[token0B, token1B]`). Link 1 is `Core.denote schema f.core
args = f args`. `Amount a` / `Fixed d` erase to words. Bytecode glue
talks about `Core.denote` (Nat).

## Hypotheses common to all links

See `TRUSTED_COMPUTING_BASE.md`. S1 Token glue uses `ExternalsRealized.none` and
does not mention `Conforms`. S2 still needs `Conforms` / `RelyAlong` / a realised
memory-blind CALL oracle (`ExtOracle`, `CallsRealized (toCalls o)`; totality
is by construction). S2 bytecode glue takes `compileBlock` (erase or powdr
spill), the same compile hypothesis as S1. No `sorry`, `native_decide`,
`bv_decide`, or project `axiom` in any link; CI pins the axiom footprint in
`Checks.lean`. `Security` depends only on `Lang`; `Compiler` depends on `Lang`
and powdr, never on `Security`; only `EndToEnd*.lean` see both.

## Open items

- **Deploy / constructor.** Yul `constructor_correct` (`ConstructorTheorems.lean`) uses the
  Solidity CREATE convention (args are the last `32n` bytes of `env.code`).
  `bytecode_deploy_correct` is `compileObject_correct`: init frame is `L.initState`
  (`env.code = L.code`, empty calldata) and `FrameOK` requires exact `mkCode L.code`,
  so **appended constructor args are not in that EVM model**. The private
  `compileResolvedObject_compileWitness` blocks re-applying `compile_correct_withPayload`
  with extra trailing bytes. Runtime calls are unaffected. Vault/AMM constructors
  with `call` are out of scope.

- **S2 post-world.** Vault's transported world is the fault-oracle-adjusted fold, while
  Token relates `Security.run` directly; unifying them is cosmetic (Security is `∀ w`).
