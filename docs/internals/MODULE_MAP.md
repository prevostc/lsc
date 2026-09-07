# Module Map

Every guarantee module exposes an API (definitions, theorem statements) in
`*Theorems.lean` and keeps proofs in `*Proof.lean` (plus `*Defs.lean` when
the statement needs structures). Downstream modules import `*Theorems`,
never `*Proof`. `Checks.lean` pins exported theorems and the axiom
footprint. Tasks should read APIs, not proofs.

Lake libraries (`lakefile.lean`): `Lsc` (language, compiler, security — `Lsc.Lang`,
`Lsc.Security`, `Lsc.Compiler`, `Lsc.Compiler.Proof`, `Lsc.Compiler.Transport`,
`Lsc.Tools`, `Lsc.Util`, barrel `Lsc.lean`) → `Stdlib` (`Stdlib.ERC20`,
`Stdlib.Scales`, `Stdlib.SafeERC20`, barrel `Stdlib.lean`) → `Examples`
(`Examples.Counter.*`, `Examples.Token.*`, `Examples.Vault.*`, `Examples.Amm.*`,
`Examples.Misc.*`). Import direction is strictly downward.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx S X E ε`, `World S X E`, `Ctx`, `Err` (including `callFailed`),
  primitives, the `run_*` simp normal form, monad laws (`bind_assoc` and friends)
  for reifier certificates. Language specification.
- `Interface.lean` — `Interface`, `Binding`, `Tx.call` / `Tx.callUnit`, `run_call`.
  Bindings are explicit constants.
- `Amount.lean` — `Amount τ s`, `Flag`, `Price`, `Fixed`, `Rounding`,
  `add` / `sub` / `shareDown` / `shareUp`, `Tx.mulDivDown` / `Up`. Named scales
  and derived ops (`mulDown`, `rescale`, `convert`) are in `Stdlib/Scales.lean`.
- `Core.lean` — `Core` (`Op.call`, `Stmt.call`), `Core.denote` (Nat, compiler),
  `Core.denoteAWord` / `Core.denoteAUnit` (Amount certificates), `Core.effects`.
  `ContractSchema.ext` supplies `call : Nat → Nat → List Nat → Tx`.
- `CoreTheorems.lean` / `CoreProof.lean` — `Op.effects_frame`,
  `Stmt.effects_frame_on`, `effects_frame_on` / `effects_frame` /
  `effects_frame_map1` / `effects_frame_map2`.
- `Spec.lean` — `Entry`, `Spec` (finite family of `Tx` entrypoints). Language-level
  so `Reify` can generate it without depending on `Lsc.Security`.
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted).
  Exports `f.core`, `f.core_denote`, `C.contract`, `C.Fn` / `C.entry` / `C.spec`,
  `#lsc_obligations C`. Bytecode transport glue generation is in progress
  (`DECISIONS.md`).
- `Contract.lean` — `ContractDef` (including `bindings : List BindingDef`),
  `FnDef`, ABI signatures, keccak selectors.
- `Syntax/` — `read` / `write` and related command/elab (`Commands`, `Grammar`,
  `ElabStmt`, `ElabExpr`, `Params`, `CrossCall`).

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `Step` (`call` / `env`), `Wf` (`target = self` and
  `sender ≠ self`), `run`, revert-frame lemmas.
- `Invariant.lean` — `Inv : World S X E → Prop`, `RelyAlong`,
  `PreservesInv` / `PreservesInvEnv`.
- `InvariantTheorems.lean` / `InvariantProof.lean` — `inv_run`, `inv_run_at`.
- `Wealth.lean` — `claim`, `Auth`, `holdings`, `Solvent`.
- `WealthTheorems.lean` / `WealthProof.lean` — `no_unauthorized_extraction`,
  `no_unauthorized_extraction_at`, `solvent_run`, `solvent_run_at`.

Depends only on `Lsc/Lang`.

## `Stdlib/` — user-importable features

Does not import `Examples`. `Lsc` does not import `Stdlib`.

- `ERC20.lean` — IERC20 may-model: `Ghost` (`balances` + `decimals`), `Method`,
  `model`, `Rely`, `IERC20`, `IERC20.Ref`, `Binding.*` aliases. Namespace stays
  `Lsc.Stdlib` / `Lsc.Binding`. No allowances / `totalSupply` in the ghost.
- `Scales.lean` — `WAD`, `RAY`, `USDC_SCALE`, `Q96`, `E8`; derived `Amount`
  ops (`mulDown` / `rescale` / `convert`, …) still named `Lsc.Amount.*`.
- `SafeERC20.lean` — spec-level `safeTransfer` / `safeTransferFrom` /
  `safeApprove` (`checkOk`); `@[lsc_inline]`, usable mid-`do`.
- `Tests.lean` — reify of stdlib helpers, including a compound helper mid-`do`.

Protocol instances (Token, Vault, AMM, Counter) live under `Examples/`, not
stdlib.

## `Lsc/Compiler` — Core → Yul → bytecode

Guarantee theorems sit in `Lsc/Compiler/<Name>Theorems.lean`; proofs in
`Lsc/Compiler/Proof/<Name>Proof.lean` unless noted. `*Defs.lean` hold
statement-level structures.

- `Yul.lean` — `toYulFn`, `runtimeBlock`, `deployObject` (powdr yul-semantics
  AST), `printYul`. Does not emit `tload` / `tstore`.
- `YulExec.lean` — executable harness on powdr's Yul interpreter.
- `Bytecode.lean` — `compileRuntime` / `compileDeploy` through powdr's verified
  compiler.
- `Correctness.lean` — `R`, `logsRel` / `selfLogs`, `mkEvmState` / `mkEvmStateExt`,
  `RunCommittedExt`, `ToYulFnCorrectExt`, `RuntimeBlockCorrectExt`.
- `Externals.lean` — `yulD`, `Abs`, `ofState_foreign`, `Foreign` / `evmForeign`,
  `NoInterfere`, `decodeRet`, `RX`, `Conforms`, `Realizes`, `CallsTotal`,
  `BindWF`. Bytecode glue must use `gas := .none`. Never imported by `Lsc/Lang`.
- `CoreDefs.lean` / `CoreTheorems.lean` — `M1Frag` / `CallFree`;
  `toYulFn_correct_callFree`. Proof: `Proof/CoreProof.lean`.
- `CoreExtSimDefs.lean` / `CoreExtSimTheorems.lean` — `core_sim_ext_callFree`,
  `toYulFn_correct_ext`, `toYulFn_correct_ext_one` (`hS2 : S2Frag f.core`).
  Proof: `Proof/CoreExtSimProof.lean`.
- `DispatchDefs.lean` / `DispatchTheorems.lean` — `runtimeBlock_correct_callFree`.
  Proof: `Proof/DispatchProof.lean`.
- `DispatchExtDefs.lean` / `DispatchExtTheorems.lean` — `runtimeBlock_correct_ext`.
  Proof: `Proof/DispatchExtProof.lean`.
- `EndToEnd.lean` / `EndToEndTheorems.lean` / `EndToEndProof.lean` — S1 glue
  (`EvmCallRun`); `bytecode_call_correct`, `bytecode_trace_all`. Directly
  imports `Security`.
- `EndToEndExt.lean` / `EndToEndExtDefs.lean` / `EndToEndExtTheorems.lean` /
  `EndToEndExtProof.lean` — S2 glue (`EvmCallRunExt` / `EvmTraceRunExtAll`);
  `bytecode_call_correct_ext`, `evmCallRunExtAll_of_progress`. Imports
  `EndToEnd`, so it sees `Security`.
- `Transport.lean` / `TransportTheorems.lean` / `TransportProof.lean` —
  `transport_trace` / `_exists` and S2 `_ext` / `_claim_ext` variants.
- `Transport/Defs.lean` — `TransportCodec` / `TransportSetup` / `TransportBindings`,
  `decodeTrace` / `CallsWF`.
- `Transport/Step.lean` — per-call `transport_step` / `transport_step_ext`.
- `Transport/Abi.lean`, `Transport/Slots.lean` — ABI length lemmas;
  `storageRel_scalar_toNat` / `storageRel_map1_toNat`.
- `EvmDetDefs.lean` / `EvmDetTheorems.lean` — `Halted`; `steps_halted_unique`.
  Proof: `Proof/EvmDetProof.lean`.
- `ProgressCoreTheorems.lean` — `yul_progress`. Proof: `Proof/ProgressCoreProof.lean`.
- `ConstructorDefs.lean` / `ConstructorTheorems.lean` — `constructor_correct`,
  `deployBlock_correct`. Proof: `Proof/ConstructorProof.lean`.
- `DeployTheorems.lean` / `DeployProof.lean` — `bytecode_deploy_correct`
  (powdr `compileObject_correct`; init frame has no appended constructor args).

Depends on `Lsc/Lang` (`Core`, `Interface`) and powdr; never on `Lsc/Security`
except `EndToEnd*.lean`.

### `Lsc/Compiler/Proof` — internal lemma libraries

Helpers nobody outside the proof tree should import. Grouped by role:

- Words / memory / env / layout: `Words`, `Memory`, `Env`, `Layout`.
- Mapping slots: `Maps`, `Maps2`.
- Emitter and M1 ops: `Emit`, `Ops`, `OpsMore`, `OpsToken`, `OpsArith`,
  `OpsMulDiv`, `OpsCtx`.
- Calldata / constructor prologue: `Calldata`, `ConstructorPrologue`,
  `ObjectExtra`.
- EVM lift / descend: `Lift`, `Descend`.
- S2 call simulation: `CoreExt`, `CallState`, `AbiCall`, `Call`, `CallFwd`,
  `CallBwd`, `Oracle`, `OfState`, `BindEnvs`, `CoreExtCall`.
- S2 progress infrastructure: `Progress`.

## `Lsc/Tools` and `Lsc/Util`

- `Tools/AbiJson.lean` — ABI JSON.
- `Util/OpenPrivate.lean` — test/util helper.
- EVM differential harness: `scripts/difftest.sh` (Lean `Tx.run` vs anvil/revm
  on `compileRuntime` / `compileDeploy` bytecode). Interpreter tests:
  `Examples/Misc/YulTests.lean`.

## `Examples` — separate Lake library

Example contracts, Tx-level proofs, security theorems, compiler instances,
and bytecode-level theorems. Do not treat `Lsc/Examples/` (if present on
disk) as this library.

Naming (each protocol is a directory; modules are `Examples.C.Role`):

| Role | Files |
|------|--------|
| Contract | `Examples/C/Contract.lean` |
| Tx-level lemmas | `Proofs.lean`, optionally `ProofsTheorems.lean` / `ProofsProof.lean` |
| Security spec + theorems | `Security.lean`, `SecurityTheorems.lean`, `SecurityProof.lean` |
| Compiler instance | `CompileTheorems.lean`, `CompileProof.lean`, optional `CompileDefs.lean` |
| Bytecode theorems | `EndToEndTheorems.lean`, `EndToEndProof.lean`, `EndToEnd.lean` (glue) |

- **Counter** — `Examples/Counter/`. `counter_correct`, `counter_dispatch_correct`;
  no Security / bytecode theorem.
- **Token** — `Examples/Token/`. S1. `token_no_unauthorized_extraction`, `token_solvent`;
  `token_correct`, `token_dispatch_correct`;
  `token_bytecode_no_unauthorized_extraction`, `token_bytecode_solvent`,
  `token_deploy_then_no_unauthorized_extraction`.
- **Vault** — `Examples/Vault/`. S2, one `IERC20`. `vault_no_unauthorized_extraction`,
  `vault_solvent`; `vault_correct_ext`;
  `vault_bytecode_no_unauthorized_extraction`, `vault_bytecode_solvent`,
  `vault_abs_nonvacuous`.
- **AMM** — `Examples/Amm/`. S2, two `IERC20`. `amm_no_unauthorized_extraction`, `amm_solvent`;
  `amm_correct_ext`; `amm_bytecode_no_unauthorized_extraction` (no bytecode
  solvency theorem).
- `Examples/Misc/AmountDemo.lean` — Amount-typed surface demo.
- `Examples/Misc/YulTests.lean` — interpreter harness.
