# Yul Target Contract (powdr)

Decisions for `Lsc/Compiler` fixed by the study of `yul-semantics`, `evm_semantics`,
`yul-evm-compiler` (pinned in `lake-manifest.json`). File references are into `.lake/packages/`.

## Which powdr theorems we consume

- **Deploy**: `YulEvmCompiler.compileObject_correct` (`ObjectCompile.lean`) — relates the
  resolved object run from `L.initState` (empty calldata/storage) to the compiled creation code.
  Object shape: `object C { code { datacopy(0, dataoffset("runtime"), datasize("runtime"))
  return(0, datasize("runtime")) } object "runtime" { code { dispatcher } } }`
  (`YulSemantics.constructorCode`).
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
- Scalar field `f` → slot `f`; `loadMap f k` → `mstore(0,k) mstore(32,f) sload(keccak256(0,64))`;
  `map2` nests. Ctx reads → `caller/callvalue/timestamp/number/address`.
- Checked arithmetic → guard + `revert` with `Panic(uint256)` selector and code `0x11`/`0x12`;
  `mulDiv*` → overflow guard on the product then `div` (512-bit later).
- `require c err args` → `if iszero(c) { <custom error ABI at 0x80> revert(0x80, 4+32n) }`.
- `emit` → ABI-pack at `0x80`, `log1(0x80, 32n, topic0)`.
- `ite` (two-armed, value-producing) → predeclared result variables + `switch c case 0 {…}
  default {…}` (Yul `if` has no `else`).
- `ret` → ABI-encode at `0x80`, `return(0x80, 32k)`; unit → `stop()`.
- External ERC20 call → `call(<literal gas word>, tok, 0, in, n, out, 32)`; **never `gas()`**
  (powdr rejects it). Under the lock, `toYul_correct` constrains `ExternalCalls` to the
  interface model and to leaving our storage unchanged.
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
