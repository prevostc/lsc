# AMM

Constant-product pool, two `IERC20` bindings, no fee. First LP mint is `a0`;
later `min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)`. Swaps use Uniswap floor output. External
transfers are checked after storage writes.

**Proved:** each reserve is ≤ the pool's ghost balance of that token; share
balances sum to `totalShares`. An address's share count never falls unless
they called `removeLiquidity` (spec and bytecode, including the spill
compile). Solvency of each reserve vs pro-rata LP claims is at the spec
only. Constructor writes token slots (outside S2 runtime). Other contracts
cannot see the pool's private memory, which is true of the EVM.

| File | Role |
|------|------|
| `Contract.lean` | Pool surface + `lsc_contract` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, two-token `ammBs`, codec |
| `Theorems.lean` | Exported security, compiler, and bytecode theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas; `k` monotone on swaps |
| `Proofs/Security.lean` | Invariant and authorisation instances |
| `Proofs/Compile.lean` | S2 multi-binding compiler proofs |
| `Proofs/EndToEnd.lean` | Bytecode glue and anti-extraction proof |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
