# Module Map

Every guarantee module exposes an API (definitions, theorem statements) in
`*Theorems.lean` and keeps proofs in `*Proof.lean` (plus `*Defs.lean` when
the statement needs structures). Downstream modules import `*Theorems`,
never `*Proof`. `Checks.lean` pins exported theorems and the axiom
footprint. Agents update it when a pinned theorem is added or renamed
(the commit message records what moved). Tasks should read APIs, not proofs.

Lake libraries (`lakefile.lean`): `LscSemantics` (`Lsc.Lang`, `Lsc.Security`,
`Lsc.Util`) → `Lsc` (`Lsc.Compiler`, `Lsc.Compiler.Proof`, `Lsc.Compiler.Transport`,
`Lsc.Tools`, barrel `Lsc.lean`) → `Stdlib` (`Stdlib.ERC20`, `Stdlib.Scales`,
`Stdlib.SafeERC20`, barrel `Stdlib.lean`) → `Examples`
(`Examples.Counter.*`, `Examples.Token.*`, `Examples.Vault.*`,
`Examples.Cpamm.*`, `Examples.WETH.*`) → `Checks`. Import direction is strictly downward.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx S X E ε`, `World S X E`, `Ctx`, `Oracle`, `Err` (including
  `callFailed`), primitives, `Field`, `deriving Fields` marker, `Lsc.Syntax`
  `read` / `write`. Language specification.
  `TxTheorems.lean` / `TxProof.lean` — `run_*` peeling lemmas and monad laws.
- `Interface.lean` — `Fn` / `View`, `Interface`, `Tx.call` / `Tx.view` /
  `Tx.tryCall`, `decodeOrDefault`, `I.Ref` macro, `read`/`write` elaborators
  (lens values; bare idents → `S.Fields.f`). `InterfaceDeriving.lean`
  generates `I.Ref` / `I.Impl` / `Impl.ofRef`. `FieldsDeriving.lean`
  generates per-field `Field S α` lenses. `InterfaceTheorems.lean` /
  `InterfaceProof.lean` — `run_call` / `run_view` and certificate lemmas.
- `Word.lean` — `Word`, `Flag`, checked `+? -? *? /?`, `mulDivDown` / `Up` /
  `pow10`. `WordTheorems.lean` / `WordProof.lean` for `Tx.run` lemmas.
- `Amount.lean` — `Asset`, `Amount a` (one-field; not an abbrev), `Fixed d`,
  same-asset `+? -?`, scalar `*? /?`, dimensional `mulDivDown` / `Up`.
  Named scales (`WAD`, `mulDown`, `rescale`) are in `Stdlib/Scales.lean`.
- `ExtState.lean` — the fixed compiled `World.ext` type.
- `Core.lean` — `Core` (`Op.call`, `Stmt.call`), `Core.denote` (words;
  Reify erases `Amount` / `Fixed`), `Core.effects`.
  `CoreTheorems.lean` / `CoreProof.lean` — `effects_frame` family.
- `Spec.lean` — `Entry`, `Spec` (finite family of `Tx` entrypoints).
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted).
  Exports `f.core`, `f.core_denote`, `C.contract`, `C.Fn` / `C.entry` / `C.spec`,
  `C.impl` from `implements`. `#lsc_obligations C`.
- `Contract.lean` — `ContractDef`, `FnDef`, ABI signatures, keccak selectors.
- `Inline.lean` — `@[internal]` / `@[internal inline]` for non-entrypoint helpers.

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `Step` (`call` / `env`), `accepted`, `External` /
  `Wf` (`target = self` and `sender ≠ self`), `HasRely` / `defaultRely`,
  `run`.
- `State.lean` — public `State C` / `Txs w`, `Msg w` (a call to a
  deployed state: `sender ≠ self`), `foldAccepted`, `HasSpent` /
  `Txs.spent`.
- `Invariant.lean` — `Inv : World S X E → Prop`, `RelyAlong`,
  `PreservesInv` / `PreservesInvEnv` / `PreservesInvAt`, `Reachable`.
- `InvariantTheorems.lean` / `InvariantProof.lean` — `inv_run`, `inv_run_at`.
- `Wealth.lean` — `claim`, `Auth`, `holdings`, `Solvent`.
- `WealthTheorems.lean` / `WealthProof.lean` — `no_unauthorized_extraction`,
  `no_unauthorized_extraction_at`, `solvent_run`, `solvent_run_at`.

Depends only on `Lsc/Lang`.

## `Stdlib/` — user-importable features

Does not import `Examples`. `Lsc` does not import `Stdlib`.

- `ERC20.lean` — `structure IERC20 (a : Asset)` (`deriving Interface`) and
  `IERC20.Spec T`. Namespace `Lsc.Stdlib`.
- `Scales.lean` — `WAD`, `RAY`, `USDC_SCALE`, `Q96`, `E8`; `Fixed` helpers.
- `SafeERC20.lean` — `safeTransfer` / `safeTransferFrom` / `safeApprove`
  (`@[internal inline]`).
- Tests: `Tests.lean`, `InterfaceTests.lean`, `ReifyInterfaceTests.lean`,
  `ReifyVaultLikeTests.lean`.

Protocol instances (Token, Vault, Cpamm, Counter) live under `Examples/`.

## `Lsc/Compiler` — Core → Yul → bytecode

Guarantee theorems sit in `Lsc/Compiler/<Name>Theorems.lean`; proofs in
`Lsc/Compiler/Proof/<Name>Proof.lean` unless noted. `*Defs.lean` hold
statement-level structures.

- `Pipeline.lean` — `compileContract` / `Artifacts`.
- `Yul.lean` — `toYulFn`, `runtimeBlock`, `deployObject`, `printYul`.
- `YulExec.lean` — executable harness on powdr's Yul interpreter.
- `Bytecode.lean` — `compileRuntime` / `compileDeploy` through powdr.
- `Correctness.lean` — `R`, `logsRel`, `mkEvmState` / `mkEvmStateExt`.
- `Externals.lean` — thin re-export; `Conforms` / `Abs` deleted.
  `ExtOracle.lean` / `ExtOracleTheorems.lean` — `ExtOracle`, `Oracle.ofExt`,
  `toCalls`, `toCalls_total`, `ExtOracle.NoReentry`. Never imported by `Lsc/Lang`.
- `CoreTheorems.lean` — `toYulFn_correct_callFree`. Proof: `Proof/CoreProof.lean`.
- `CoreExtSimTheorems.lean` — `core_sim_ext_callFree`, `toYulFn_correct_ext`.
  Proof: `Proof/CoreExtSimProof.lean`.
- `DispatchTheorems.lean` — `runtimeBlock_correct_callFree`.
- `DispatchExtTheorems.lean` — `runtimeBlock_correct_ext`.
- `EndToEndTheorems.lean` — S1 `bytecode_call_correct`, `bytecode_trace_all`.
- `EndToEndExtTheorems.lean` — S2 `bytecode_call_correct_ext`,
  `evmCallRunExtAll_of_progress`.
- `TransportTheorems.lean` — `transport_trace` / `_exists` and S2 `_ext` /
  `transport_claim_ext` / `transport_exists_claim_ext`.
- `Transport/Defs.lean`, `Transport/Abi.lean` — `TransportSetup`,
  `TransportBindings`, ABI length lemmas.
- `ProgressCoreTheorems.lean` — `yul_progress`.
- `ConstructorTheorems.lean` — `constructor_correct`, `deployBlock_correct`.
- `DeployTheorems.lean` — `bytecode_deploy_correct`.
- `EvmDetTheorems.lean` — `steps_halted_unique`.

Depends on `Lsc/Lang` (`Core`, `Interface`) and powdr; never on `Lsc/Security`
except `EndToEnd*.lean`.

### `Lsc/Compiler/Proof` — internal lemma libraries

Helpers nobody outside the proof tree should import: `Words`, `Memory`,
`Env`, `Layout`, `Maps`, `Maps2`, `Emit`, `Ops*`, `Calldata`,
`ConstructorPrologue`, `Lift`, `Descend`, `CoreExt`, `Call*`, `Oracle`,
`Progress`, `MemFootprint*`, `Spill*`, `GasLift`, `NoGas`, `Erase`.

## `Lsc/Tools` and `Lsc/Util`

- `Tools/AbiJson.lean`, `Tools/Disasm.lean`.
- `Util/OpenPrivate.lean`.
- EVM differential harness: `scripts/difftest.sh`.

## `Examples` — separate Lake library

Each protocol is a directory (`Examples/AGENTS.md`):

| Role | Files |
|------|--------|
| Contract | `Examples/C/Contract.lean` |
| Spec | `Spec.lean` (`claim`, `Auth`, `rely`, `holdings`; `Inv` is a proof device — WETH keeps it in `Proofs/`) |
| Exported theorems | `Theorems.lean` |
| Proofs | `Proofs/Tx.lean`, `Proofs/Security.lean`, `Proofs/Compile.lean`, `Proofs/Implements.lean` |

- **Counter** — `Examples/Counter/`. Tx deltas (`increment_adds`, …); no wealth theorem.
- **Token** — `Examples/Token/`. S1. `token_no_unauthorized_extraction`,
  `token_solvent`, `erc20` (`IERC20.Spec Token.impl`). Public theorems
  take `State` / `Txs`.
- **Vault** — `Examples/Vault/`. S2, one `IERC20.Ref`. `vault_no_unauthorized_extraction`,
  `vault_solvent` (`State` / `Txs`; `IERC20.Spec` lives in `HasDeploy` / `State`).
- **Cpamm** — `Examples/Cpamm/`. S2, two `IERC20.Ref`. `swap0for1_k`,
  `cpamm_no_unauthorized_extraction`, `cpamm_solvent` (`State` / `Txs`;
  both `IERC20.Spec`s and `TokensIndependent` live in `HasDeploy` / `State`).
- **WETH** — `Examples/WETH/`. Wrapped native (`Chain` profile). `weth_exact`,
  `weth_backed` / `weth_no_unauthorized_extraction` (`State` / `Txs`),
  `deposit_delta`, `withdraw_delta`.

`Checks.lean` imports `Examples.<Name>.Theorems` only. Bytecode transport is
the compiler family in `TransportTheorems.lean`, not per-example theorems.
