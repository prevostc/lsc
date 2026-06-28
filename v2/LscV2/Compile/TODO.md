# Compile pipeline backlog

Deferred work for the LSC v2 compiler. Items are removed or checked off as they land.

## Bytecode follow-ups

- [x] ABI dispatcher (selector routing on calldata)
- [x] `contractToBytecode` for full `counterDef` (increment + pause + unpause)
- [x] Global unique jump labels per function (fixes cross-function `JUMPI`/`JUMP` collisions)
- [x] Encode-time duplicate `JUMPDEST` label detection
- [x] EvmYul execution smoke test (`BytecodeExecSmoke`: increment / pause / unpause storage)
- [ ] Creation bytecode (deploy wrapper returning runtime code)
- [ ] Real keccak256 ABI selectors (replace `String.hash` stub in `Selectors.lean`)
- [ ] Real keccak256 event topic0 for `Paused` / `Unpaused` (currently `name.hash` stub)
- [ ] ABI encode/decode for revert data and return values
- [ ] EvmYul execution with real 256-bit LOG topics (keccak topic0 currently trips gas accounting in EvmYul)
- [ ] Gas-aware codegen / stack peephole optimization
- [ ] Memory-spilled locals (`MSTORE`/`MLOAD` scratch slots) to simplify stack codegen for decompilers
- [ ] Bytecode ↔ IR semantic preservation proofs (beyond structural smoke tests)

## Other compile paths (not pursued now)

- [ ] Yul text emission via `Yul.lean` — kept in tree, not on critical path
- [ ] `solc` / strict-assembly pipeline
- [ ] forge-lean Foundry fork (see `docs/spec_idea_1/lsc-toolchain.md`)
- [ ] Removing or refactoring existing Yul modules
