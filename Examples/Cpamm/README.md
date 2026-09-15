# CPAMM

Constant-product AMM with an LP swap fee and a protocol-fee switch. Binds two
typed `Ref (IERC20 …)` tokens. The swap fee is 30 bps of `amountIn`; LPs keep
it on the curve. When `feeTo ≠ 0`, a protocol share of that fee (not of
`amountIn`) is skimmed into `protocolFees*` and never enters `k`. External
calls run after storage writes.

**Proved (Tx):** a successful swap does not decrease `reserve0 · reserve1`
(the fee is what makes the increase strict in typical trades); protocol
buckets move only on swaps and `collectProtocolFees`; `removeLiquidity` pays
the floor pro-rata of each reserve; `addLiquidity` mints the floor-min of
the two reserve ratios, or `a0 − 1000` on the first mint, locking
`MINIMUM_LIQUIDITY` at address 0 (`addLiquidity_min_liquidity` on a first
mint). `mint` updates both `shares[to]` and `totalShares`; first mint
calls `mint 0 MINIMUM_LIQUIDITY` then `mint who minted`. Owner admin does
not touch the buckets.

**Proved (spec):** share-count anti-extraction
(`cpamm_no_unauthorized_extraction`) and solvency of LP claims plus protocol
buckets against live holdings (`cpamm_solvent`). Address 0's locked shares
count as a claim; only a `removeLiquidity` it signs could burn them.
Assumed of the tokens: they
are distinct conforming ERC-20s per `IERC20.Spec`; a CALL on one does not
change the other's `balanceOf` / `totalSupply` views; no reentrancy is
modelled; no fee-on-transfer. Between calls neither pool balance may fall
(`cpammRely`). Bytecode trust is the compiler's transport theorems, not
repeated here.

**Not proved:** strict `k` increase, 512-bit `mulDiv` (a word-overflow
intermediate reverts), impermanent loss, the owner redirecting future fees
via `setFeeTo`.

| File | Role |
|------|------|
| `Contract.lean` | Pool surface, shared `swapOut` quote, schema, contract |
| `Spec.lean` | `claim`, `Auth`, `Inv`, `holdings0/1`, `cpammRely` |
| `Theorems.lean` | Exported Tx and security theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas |
| `Proofs/SwapOut.lean` | Shared `swapOut` quote `Tx.run` lemma |
| `Proofs/Security.lean` | Invariant and authorisation |
| `Proofs/Compile.lean` | Runtime `compileRuntime` non-vacuity `#guard` |
| `Proofs/Math.lean` | Floor-product facts for `k` |
| `Tests.lean` | Smoke `#guard`s |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
