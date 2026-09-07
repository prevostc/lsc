# AMM

Constant-product pool, two `IERC20` bindings, no fee. First LP mint is `a0`;
later `min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)`. Swaps use Uniswap floor output. External
transfers are checked (`safeTransferFrom` / `safeTransfer`) after storage
writes.

**Proved:** each reserve is ≤ the pool's ghost balance of that token; share
balances sum to `totalShares`. An address's **share count** never falls unless
they called `removeLiquidity` (Tx-level and Yul-level). The runtime hex is
emitted by powdr's memory-spilling path (`DUP17+`); the bytecode theorem still
assumes the non-spilled compile, so it is not yet a bytecode guarantee for
this contract. Solvency of each reserve vs pro-rata LP claims is at the spec
only. Constructor writes token slots (outside S2 runtime).

| File | Role | Depends on |
|------|------|------------|
| `Contract.lean` | Pool surface + `lsc_contract` | `Lsc`, `Stdlib.ERC20`, `Stdlib.Scales` |
| `Proofs.lean` | `Tx.run` lemmas, `k` monotone | `Contract.lean` |
| `Security.lean` | `Inv`, share `claim`, `Auth` | `Proofs.lean` |
| `SecurityProof.lean` | Security proof bodies | `Security.lean` |
| `SecurityTheorems.lean` | Exported wealth theorems | `SecurityProof` |
| `CompileDefs.lean` | Two-binding `ammBs` | `Contract.lean` |
| `CompileProof.lean` | S2 multi-binding proofs | `CompileDefs` |
| `CompileTheorems.lean` | Exported `amm_correct_ext` | `CompileProof` |
| `EndToEnd.lean` | Bytecode glue | `Compile*`, `Security*`, Vault E2E |
| `EndToEndProof.lean` | Bytecode theorem bodies | `EndToEnd.lean` |
| `EndToEndTheorems.lean` | Exported bytecode anti-extraction | `EndToEndProof` |
