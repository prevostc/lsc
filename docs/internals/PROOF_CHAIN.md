# Proof Chain

The end-to-end theorem for a contract `C` is assembled from independently
checked links. A change to any link must update this file and
`TRUSTED_COMPUTING_BASE.md`.

```
Tx / trace theorem  ──(1) core_denote (rfl)──  Core
Core               ──(2) toYulFn_correct_*──  Yul (powdr `Run`)
Yul                ──(3) compile_correct────  bytecode (powdr `Steps`)
example theorems   ──(4) transport_*_ext────  bytecode-level anti-exploit fact
```

How a `ContractDef` becomes hex/ABI (functions, not theorems):
[`COMPILER_PIPELINE.md`](COMPILER_PIPELINE.md). Public entry:
`Lsc.Compiler.compileContract` → `Artifacts`.

Example security and compiler/glue theorems pinned by `Checks.lean` are
named below. `transport_claim_ext` / `transport_exists_claim_ext` lift a
trace fact onto bytecode; they are not in `Checks.lean`. Examples do not
ship `*_bytecode_*` theorems (DECISIONS 2026-09-12).

| Link | Theorem(s) | File | Status | Fragment | Examples |
|------|------------|------|--------|----------|----------|
| 1 Spec→Core | `f.core_denote` | `Lsc/Lang/Reify.lean` | proved | both | Counter, Token, Vault, Cpamm |
| 2 Core→Yul | `toYulFn_correct_callFree`, `runtimeBlock_correct_callFree` | `CoreTheorems.lean`, `DispatchTheorems.lean` | proved | S1 | Counter, Token |
| 2 Core→Yul | `toYulFn_correct_ext`, `core_sim_ext_callFree`, `runtimeBlock_correct_ext` | `CoreExtSimTheorems.lean`, `DispatchExtTheorems.lean` | proved | S2 | Vault, Cpamm |
| 3 Yul→EVM | `compile_correct`, `steps_halted_unique` | powdr `YulEvmCompiler`, `EvmDetTheorems.lean` | proved | both | runtime of the above |
| 4 Glue | `bytecode_call_correct`, `bytecode_trace_all` | `EndToEndTheorems.lean` | proved | S1 | Token-shaped call-free |
| 4 Glue | `bytecode_call_correct_ext`, `yul_progress`, `evmCallRunExtAll_of_progress` | `EndToEndExtTheorems.lean`, `ProgressCoreTheorems.lean` | proved | S2 | Vault, Cpamm |
| 4 Transport | `transport_claim_ext`, `transport_exists_claim_ext` | `TransportTheorems.lean` | proved | S2 | lifts example trace theorems |
| Security (examples) | `token_no_unauthorized_extraction`, `token_solvent`, `token_spec` | `Examples/Token/Theorems.lean` | proved | S1 | Token |
| Security (examples) | `vault_no_unauthorized_extraction`, `vault_solvent` | `Examples/Vault/Theorems.lean` | proved | S2 | Vault |
| Security (examples) | `cpamm_no_unauthorized_extraction`, `cpamm_solvent`, `swap0for1_k` | `Examples/Cpamm/Theorems.lean` | proved | S2 | Cpamm |
| Deploy | `constructor_correct`, `bytecode_deploy_correct` | `ConstructorTheorems.lean`, `DeployTheorems.lean` | Yul ctor proved; EVM args gap | S1 | Token constructor (call-free) |

Compiled runtimes begin with `if tload(0) { revert(0,0) }`. When that
slot is set, `lock_held_reverts_yul` / `_open` (`LockTheorems.lean`)
prove the memoryguard-erased `runtimeBlock` reverts with empty data and
unchanged committed storage, transient storage, and logs (no call
oracle). `lock_held_reverts_evm` lifts that through `compile_correct` to
assembled bytecode: a matching start frame (`FrameOK`, `StateMatch`,
`pc = 0`, empty stack) halts in revert with the executing account's
storage and transient storage, and the log series, agreeing with the
Yul start. S2 glue still takes `hNR : ExtOracle.NoReentry`; dropping it
is slice 8C.

S1 is the call-free fragment (`CallFree` / `M1Frag`). S2 is `S2Frag`
(`CallFree` plus `Op.call` / `Stmt.call`) for contracts that CALL out.
Link 1 is `Core.denote schema f.core args = f args`. `Amount a` / `Fixed d`
erase to words. Bytecode glue talks about `Core.denote` (Nat).

## Hypotheses common to all links

See `TRUSTED_COMPUTING_BASE.md`. S1 Token glue uses a closed external model
and does not mention `IERC20.Spec`. S2 still needs `IERC20.Spec` at the
example, `RelyAlong`, and a realised memory-blind CALL oracle (`ExtOracle`,
`toCalls_total`). S2 bytecode glue takes `compileBlock` (erase or powdr
spill). No `sorry`, `native_decide`, `bv_decide`, or project `axiom` in any
link; CI pins the axiom footprint in `Checks.lean`. `Security` depends only
on `Lang`; `Compiler` depends on `Lang` and powdr, never on `Security`; only
`EndToEnd*.lean` see both.

## Open items

- **Deploy / constructor.** Yul `constructor_correct` (`ConstructorTheorems.lean`) uses the
  Solidity CREATE convention (args are the last `32n` bytes of `env.code`).
  `bytecode_deploy_correct` is `compileObject_correct`: init frame is `L.initState`
  (`env.code = L.code`, empty calldata) and `FrameOK` requires exact `mkCode L.code`,
  so **appended constructor args are not in that EVM model**. Runtime calls are
  unaffected. Vault/Cpamm constructors with `call` are out of scope.
