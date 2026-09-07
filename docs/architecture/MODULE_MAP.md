# Module Map

Every module exposes an API (definitions, theorem statements, assumptions) and keeps proofs in
`*Proof.lean` files. Tasks should read APIs, not proofs.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx S X E ε`, `World S X E` (`self`, `ext : X`, `log`, `faults`, `ncalls`), `Ctx`,
  `Err` (including `callFailed`), primitives, the `run_*` simp normal form. Language specification.
- `Interface.lean` — `Interface`, `Binding`, `Tx.call` / `Tx.callUnit`, `run_call`. Bindings are
  explicit constants.
- `Amount.lean` — `Amount τ s` (structure), `Flag`, `Price`, rounding-explicit ops, `toNat` simp
  normal form, ℚ cast pack. External scales are opaque symbols; `rescale` / `Amount.one` take
  runtime scale words.
- `Core.lean` — `Core` (`Op.call`, `Stmt.call`), `Core.denote` (Nat, compiler), `Core.denoteAWord`
  / `Core.denoteAUnit` (Amount surface certificates), `Core.effects` (including `calls`).
  `ContractSchema.ext` supplies `call : Nat → Nat → List Nat → Tx`.
- `CoreProof.lean` — `Op.effects_frame` / `Stmt.effects_frame_on` / `effects_frame_on`
  (successful denote leaves unwritten projections of `self` unchanged).
- `Spec.lean` — `Entry`, `Spec` (a contract as a finite family of `Tx` entrypoints). Language-level
  so `Reify` can generate it without depending on `Lsc/Security`.
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted). Exports `f.core`,
  `f.core_denote`, `C.contract`, `C.Fn`/`C.entry`/`C.spec`, and `#lsc_obligations C`.
- `Contract.lean` — `ContractDef` (including `bindings : List BindingDef`), `FnDef`, ABI
  signatures, keccak selectors.

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `Step` (`call`/`env`), `Wf` (`target = self` and `sender ≠ self`),
  `run`, adversary sets, revert-frame lemmas.
- `Invariant.lean` — `Inv : World S X E → Prop`, `RelyAlong`, `PreservesInv`/`PreservesInvEnv`,
  `inv_run`.
- `Wealth.lean` — `claim`, `Auth`, `holdings`, `no_unauthorized_extraction`, `solvency`.

Depends only on `Lsc/Lang`.

## `Lsc/Stdlib` — verified components

- `ERC20.lean` — IERC20 may-model: `Ghost` (`balances` + `decimals`), `Method`, `model`, `Rely`,
  `IERC20`, `IERC20.Ref`, `Binding.*` aliases. No allowances/`totalSupply` in the ghost.

Vault and AMM live under `Lsc/Examples/` (protocol instances, not stdlib modules).

## `Lsc/Lib`

`Math.lean`, `Fixed.lean`, `Wad.lean`, `Ray.lean`, `Wei.lean`: arithmetic helpers used by
Amount-typed examples.

## `Lsc/Compiler` — Core → Yul → bytecode

- `Yul.lean` — `toYulFn`, `runtimeBlock`, `deployObject` (powdr yul-semantics AST), `printYul`.
  Does not emit `tload`/`tstore`.
- `YulExec.lean`, `YulTests.lean` — executable harness on powdr's Yul interpreter and differential
  tests against `Tx.run`.
- `Bytecode.lean` — `compileRuntime`/`compileDeploy` through powdr's verified compiler.
- `Correctness.lean` — `R`, `logsRel`/`selfLogs`, `mkEvmState` / `mkEvmStateExt` (threads foreign
  `ξ`), `RunCommittedExt`, `ToYulFnCorrectExt`, `RuntimeBlockCorrectExt`.
- `Externals.lean` — `yulD`, `Abs`, `ofState_foreign`, `Foreign` / `evmForeign`, `NoInterfere`,
  `decodeRet`, `RX`, `Conforms`, `Realizes`, `CallsTotal`, `BindWF`. Bytecode glue must use
  `gas := .none`. Never imported by `Lsc/Lang`.
- `EndToEnd.lean` — S1 glue: `bytecode_call_correct`, `EvmCallRun`, `bytecode_trace_transport` /
  `bytecode_trace_all`. Directly imports `Security`.
- `EndToEndExt.lean` — S2 glue: `openModel`, `EvmCallRunExt` / `EvmCallRunExtAll`,
  `EvmTraceRunExt` / `EvmTraceRunExtAll`, `EvmTraceRunExt_of_ExtAll`,
  `bytecode_call_correct_ext`. Universality uses
  `CallsTotal` + EVM determinism (no powdr adequacy). Imports `EndToEnd`, so it sees `Security`.
- `Transport/Defs.lean` — `TransportCodec` / `TransportSetup` / `TransportBindings`,
  `decodeTrace` / `CallsWF`.
- `Transport/Step.lean` — per-call `transport_step` / `transport_step_ext`.
- `Transport.lean` — `transport_trace` / `_exists` and S2 `_ext` / `_claim_ext` variants.

Depends on `Lsc/Lang` (`Core`, `Interface`) and powdr; never on `Lsc/Security` except
`EndToEnd.lean` (and `EndToEndExt.lean` through it).

### `Lsc/Compiler/Proof`

- `Words.lean` — word / identifier lemmas (`toNat_ofNat`, `identV` injectivity).
- `Memory.lean` — aligned `mstore` / overlapping Panic stores.
- `Env.lean` — environment / `Step` plumbing for `toYulFn_correct`.
- `Layout.lean` — layout / `Inv` (scalar `sstore`, one-word `log1`).
- `Maps.lean` — mapping slots: `mstore(0,k) mstore(32,f) keccak256(0,64)`.
- `Maps2.lean` — nested mapping slots (inner hash to `[32]`, then `mstore(0, k₂)`).
- `Emit.lean` — accumulator homomorphism for the Yul emitter.
- `Ops.lean` — M1 `load` / `addChecked` / `store` / one-word `emit` / `stop`.
- `OpsMore.lean` — `subChecked`, 0-arg `require`, `eq`/`ne`, one-word `return`.
- `OpsToken.lean` — context words, 3-word `log1`, 0-arg `revert`.
- `OpsArith.lean` — checked `mul` / `div` and the shared mul-overflow guard.
- `OpsMulDiv.lean` — `mulDivDown` / `mulDivUp` simulation.
- `OpsCtx.lean` — 0-arg `log1` (Vault `Paused` / `Unpaused`).
- `Core.lean` — `M1Frag` / `CallFree` and `toYulFn_correct_callFree`.
- `Counter.lean` — `toYulFn_correct_callFree` for every Counter runtime entrypoint;
  `counter_correct`.
- `Token.lean` — `toYulFn_correct_callFree` for every Token runtime entrypoint;
  `token_correct`.
- `Dispatch.lean` — `runtimeBlock_correct_callFree`; `counter_dispatch_correct` /
  `token_dispatch_correct`.
- `Calldata.lean` — `fnCalldata` recovers `decodeArgs` / `calldataSelector`.
- `EvmDet.lean` — `Halted`, `steps_halted_unique`.
- `Lift.lean` — lift `Step` / `Run` from `evm` into `evmWithExternal`.
- `Descend.lean` — inverse of `step_lift` for call-free Yul; `execStmts_det_evm`.
- `CoreExt.lean` — `S2Frag`; call-free backward setup (`hstab` / `haddr`).
- `CallState.lean` — `R` / `RX` after `finishCall`; `restore` after a scoped call block.
- `AbiCall.lean` — pack / `finishCall` / `decodeRet` lemmas for S2 (`boolOpt` bit algebra).
- `Call.lean` — CALL inversion for scoped `emitExtCall`.
- `CallFwd.lean` — forward packing / suffix helpers for scoped `emitExtCall`.
- `CallBwd.lean` — backward `op_sim_call_bwd` / `stmt_sim_call_bwd`.
- `Oracle.lean` — fault-oracle agreement and M1/`CallFree` independence from `faults`.
- `OfState.lean` — `α.ofState` preservation along local `stepOp` / `noExt` `Step`.
- `BindEnvs.lean` — `BindEnvs.avoids` and address/`RXs` preservation along M1/`CallFree` steps.
- `CoreExtCall.lean` — call-head helpers for `core_sim_ext` (`sim_ext_letOp_call`, `sim_ext_seq_call`, `sim_ext_op_call_return`).
- `CoreExtSim.lean` — S2 `core_sim_ext` / `toYulFn_correct_ext` (`hS2 : S2Frag f.core`).
- `DispatchExt.lean` — S2 backward dispatcher `runtimeBlock_correct_ext`.
- `Progress.lean` — S2 Yul progress infrastructure under `CallsTotal`.
- `ProgressCore.lean` — `yul_progress`: a halted `Run` of compiled S2Frag runtime exists.
- `Transport/Abi.lean` — generic ABI word-list length lemmas (`length_eq_zero` / `_two`).
- `Transport/Slots.lean` — `storageRel_scalar_toNat` / `storageRel_map1_toNat`.
- `ConstructorPrologue.lean` — CREATE `codecopy` / `mload` prologue.
- `Constructor.lean` — `constructor_correct` / `deployBlock_correct`.

## `Lsc/Tools`

ABI JSON (`AbiJson.lean`). EVM differential harness: `scripts/difftest.sh` (Lean `Tx.run`
vs anvil/revm on `compileRuntime` / `compileDeploy` bytecode).

## `Lsc/Examples`

- `Counter.lean` — compiler S1 instance (`counter_correct`); no Security/bytecode theorem.
- `Token*.lean` / `TokenEndToEnd.lean` — spec Security plus S1 bytecode theorems.
- `Vault*.lean` / `VaultEndToEnd.lean` — spec Security plus S2 bytecode theorems.
- `Amm*.lean` — spec-level Security only (`amm_no_unauthorized_extraction`, `amm_solvent`).
- `AmountDemo.lean` — Amount-typed surface demo.
