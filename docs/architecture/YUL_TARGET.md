# Yul Target Contract (powdr)

Decisions for `Lsc/Compiler` fixed by the study of `yul-semantics`, `evm_semantics`,
`yul-evm-compiler` (pinned in `lake-manifest.json`). File references are into `.lake/packages/`.

## Which powdr theorems we consume

- **Deploy**: `YulEvmCompiler.compileObject_correct` (`ObjectCompile.lean`) — relates the
  resolved object run from `L.initState` (empty calldata/storage) to the compiled creation code.
  Object shape: `object C { code { <constructor body>; datacopy(0, dataoffset("runtime"),
  datasize("runtime")) return(0, datasize("runtime")) } object "runtime" { code { dispatcher } } }`
  (`YulSemantics.EVM.constructorCode`, in `ObjectRun.lean`). Constructor-time `call` in the
  constructor body is subject to verification against this theorem.
- **Runtime calls**: `compile_correct` / `compile_runContract` (`Correctness.lean`,
  `ContractCorrectness.lean`) on the *resolved runtime block* from a custom `EvmState`
  (calldata, storage, `keccakOf`, caller, …). There is no `compileObject_runContract`.
- Preconditions we discharge or assume: `ExternalsRealized model`, `FrameOK` (fork = Osaka,
  not a precompile, empty call stack), `StateMatch yst0 s0`, `pc = 0`, empty stack, gas ≥ `b`.

## Source semantics we prove against

- `Run (EVM.evmWithExternal calls creates gas)` for entrypoints that call out;
  `Run EVM.evm` (closed) for the call-free fragment. Values are `BitVec 256`
  (`YulSemantics.EVM.U256`); literals are `Literal.number n` interpreted mod `2^256`.
- **Revert atomicity**: raw `Run` does not roll back storage/logs on `revert`. `toYul_correct`
  is stated against `RunCommitted` (`Observation.lean`), whose `committedState` restores
  storage, transient storage and logs on non-committing halts. This matches `Tx`'s
  `Except.error` discarding the world.
- Halts: `EvmState.halted : Option (HaltKind × List UInt8)` with `.ret`/`.revert` carrying the
  memory slice; `stop` carries `[]`. Logs: ordered `List LogEntry { address, topics, data }`.

## Keccak

- The dialect reads `st.env.keccakOf : List UInt8 → U256` (default `opaque keccakBytes`).
  Under `StateMatch`, `keccakOf` is pinned to `EvmSemantics.keccak256`.
- Assumptions (TCB): injectivity of `keccak256` on the finite set of 64-byte mapping keys we form
  and distinctness from scalar slots; `KeccakEngine` agrees with `EvmSemantics.keccak256` on
  the ABI signatures used for selectors/topics.

## Core → Yul mapping

- de Bruijn local `i` → `let v_i`; `letOp`/`letPure` → `let`; `seq` → sequence.
- Scalar field `f` → slot `f`; `loadMap f k` → `mstore(0,k) mstore(32,f) sload(keccak256(0,64))`.
  `map2` nests, but `keccak256(0,64)` reads `[0,64)`, so the inner hash is written to `[32]`
  *before* `mstore(0, k₂)` (`mstore(32, keccak256(0,64)); mstore(0, k₂); sload(keccak256(0,64))`).
  Ctx reads → `caller/callvalue/timestamp/number/address`.
- Checked arithmetic → guard + `revert` with `Panic(uint256)` selector and code `0x11`/`0x12`;
  `mulDiv*` → overflow guard on the product then `div` (512-bit later).
- `require c err args` → `if iszero(c) { <custom error ABI at 0x80> revert(0x80, 4+32n) }`.
- `emit` → ABI-pack at `0x80`, `log1(0x80, 32n, topic0)`.
- `ite` → `switch c case 0 {…} default {…}` (Yul `if` has no `else`). Core's `ite` carries two
  full tail continuations, so no result variables need to be joined.
- Nested Yul expressions (no flatten / `t_i` temps). `Cond`, map-slot `keccak256(0,64)`, and
  pure primitives are expression trees; checked ops reuse the result variable as scratch
  (`let v_d := add(a,b); if lt(v_d,a) { panic }`). `{ … }` only wraps `if` bodies and `switch`
  cases. `toYulFn` returns `none` unless `coreWF` (literals `< 2^256`, field kinds, event/error
  arity) and `identV` names on `[0, maxDepth)` are pairwise distinct; `runtimeBlock` also
  requires unique selectors. Parameters are `let v_i := calldataload(4 + 32 i)` (empty `VEnv`).
- `ret` → ABI-encode at `0x80`, `return(0x80, 32k)`; unit → `stop()`.
- `Op.call` / `Stmt.call` → `sload` the bound address slot, ABI-pack at `0x80`,
  `call(<gas literal>, tok, 0, …)` (**never `gas()`**; powdr rejects it),
  `if iszero(ok) { revert(0,0) }`. Return handling: `boolOpt` — success ⇔ call ok ∧
  (`returndatasize() = 0` ∨ returned word `= 1`) (missing-return-value tokens OK);
  `word` — require `returndatasize() ≥ 32`. `toYul_correct`'s `letCall` case: `PROOF_CHAIN.md`.
- Constructor-time `call` (e.g. caching `decimals`) is subject to verification against powdr's
  deploy theorem (`compileObject_correct` / `evmWithExternal` in init code). If that theorem
  cannot take external calls in creation code, `decimals` is a constructor argument.
- Dispatcher → `if lt(calldatasize(), 4) { revert(0,0) }` then
  `switch shr(224, calldataload(0))` with one `case <selector>` per entrypoint and `default { revert(0,0) }`.
- Reentrancy lock → `tload`/`tstore` of a fixed transient slot around every `tx` entrypoint;
  views revert while locked.
- Never emitted: `for`, `delegatecall`, `selfdestruct`, `create`, `gas`, `datasize`/`dataoffset`
  outside the constructor.

## Executable checks

- Yul: `Interp.run EVM.exec fuel prog st0` with `EVM.run_adequacy` (call-free only; `call`
  and `gas` are stuck in the executable dialect).
- EVM: `EvmSemantics.stepF` iterated until halt; calldata in `executionEnv.calldata`, storage in
  `accountMap`.
- Differential harness: `Tx.run` vs `Interp.run` on emitted Yul vs `stepF` on compiled bytes vs
  revm/anvil on the same calldata.
- Measured bytecode (`compileRuntime` / `compileDeploy` from `YulTests.lean`): Counter 424 / 438,
  Token 1408 / 1498. Token `stackOK2` holds (no DUP16). Nested `map2` hashes inner `keccak256(0,64)`
  into `[32]` before `mstore(0, k₂)`, so the read does not see a clobbered `[0]`.
