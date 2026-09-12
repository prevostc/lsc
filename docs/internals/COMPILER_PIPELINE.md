# Compiler pipeline

Single entry: `Lsc.Compiler.compileContract` (`Lsc/Compiler/Pipeline.lean`).
It does not change compilation; it names the existing stages.

| Stage | Input | Output | Module | Correctness theorem |
|---|---|---|---|---|
| Contract | Lean `Tx` defs | `ContractDef`, `C.Fn` / `C.spec` | `lsc_contract` in `Lsc/Lang/Reify.lean` | — (untrusted MetaM) |
| Core reify | `C.f` | `f.core`, `f.core_denote` | `Lsc/Lang/Reify.lean`, `Lsc/Lang/Core.lean` | `f.core_denote` |
| Yul | `ContractDef` | `YBlock` / `YObject` | `toYulFn`, `runtimeBlock`, `deployObject` in `Yul.lean` | `toYulFn_correct_*`, `runtimeBlock_correct_*`, `constructor_correct` |
| powdr compile | runtime `YBlock` | `List Instr` | `compileBlock` in `Bytecode.lean` (erase or spill) | powdr `compile_correct` |
| Bytecode | `List Instr` | runtime bytes | `assembleBytes`; `compileRuntime` | `bytecode_call_correct`, `_ext`; `steps_halted_unique` |
| ABI / selectors | `ContractDef` | JSON strings | `Tools/AbiJson.lean`, `Pipeline.selectorsJson` | — (keccak on `FnDef.selector`) |
| Deploy | `deployObject` | init bytes + deploy Yul | `compileDeploy` in `Bytecode.lean` | `bytecode_deploy_correct` / `compileObject_correct` (no CREATE args) |

Proof chain: [`PROOF_CHAIN.md`](PROOF_CHAIN.md).

## Where to look when X is wrong

- **Wrong selector / ABI JSON** — `Lsc/Lang/Contract.lean` (keccak), `Tools/AbiJson.lean`, `Pipeline.selectorsJson`.
- **Wrong Yul / dispatcher** — `Yul.lean` (`runtimeBlock`, `entryCase`, `toYulFn`); Core→Yul theorems in `CoreTheorems` / `DispatchTheorems` (S1) or `CoreExtSimTheorems` / `DispatchExtTheorems` (S2).
- **Compiles in solc, rejected here** — `Bytecode.compileBlock`: erasure needs `DUP17+` → spill; `memoryguard` marker; `gas()` only via fused `gasCall`.
- **Runtime hex ≠ `compileRuntime`** — `Pipeline.compileRuntimeArtifacts` follows the exporter (`compileAsmBlock` then `lowerProg`), not `compile`'s peephole wrapper; deploy hex is `compileDeploy`.
- **Deploy / constructor args** — `constructor_correct` at Yul; EVM `bytecode_deploy_correct` has no trailing CREATE args (`DeployTheorems`).
- **CALL / token ghosts** — `Externals.lean`, `ExtOracleTheorems` (`toCalls_total`); glue in `EndToEndExtTheorems`.
