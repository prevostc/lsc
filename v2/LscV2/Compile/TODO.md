# Compile pipeline backlog

Deferred work for the LSC v2 compiler. Items are removed or checked off as they land.

## Bytecode follow-ups (post increment-body milestone)

- [ ] ABI dispatcher (selector routing on calldata)
- [ ] `contractToBytecode` for full `counterDef` (increment + pause + unpause)
- [ ] Creation bytecode (deploy wrapper returning runtime code)
- [ ] Real keccak256 ABI selectors (replace `String.hash` stub in `Selectors.lean`)
- [ ] ABI encode/decode for revert data and return values
- [ ] Full `incrementAst` with `require !paused` (beyond increment-body slice)
- [ ] `pause` / `unpause` bytecode emission (needs Paused/Unpaused event topic0 in config)
- [ ] EvmYul end-to-end execution test (load bytecode, assert storage/logs)
- [ ] Gas-aware codegen / stack peephole optimization
- [ ] Bytecode ↔ IR semantic preservation proofs (beyond structural smoke tests)

## Other compile paths (not pursued now)

- [ ] Yul text emission via `Yul.lean` — kept in tree, not on critical path
- [ ] `solc` / strict-assembly pipeline
- [ ] forge-lean Foundry fork (see `docs/spec_idea_1/lsc-toolchain.md`)
- [ ] Removing or refactoring existing Yul modules
