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

**Proved (spec):** in any reachable `State`, after any `Txs`, an LP's
shares drop by at most what they themselves redeemed
(`cpamm_no_unauthorized_extraction`); each reserve plus that token's
protocol bucket is covered by live holdings (`cpamm_solvent`). Address 0's
locked shares count as a claim; only a `removeLiquidity` it signs could
burn them. Honest-counterparty (`IERC20.Spec` of both tokens, and
`TokensIndependent`) lives in `HasDeploy` / `State`. Between calls neither
pool balance may fall (`HasRely` / `cpammRely`). No reentrancy or
fee-on-transfer is modelled. Bytecode trust is the compiler's transport
theorems, not repeated here.

**Not proved:** strict `k` increase, 512-bit `mulDiv` (a word-overflow
intermediate reverts), impermanent loss, the owner redirecting future fees
via `setFeeTo`.

| File | Role |
|------|------|
| `Contract.lean` | Pool surface, `SwapDirection`-indexed `swap` / `swapOut`, schema, contract |
| `Spec.lean` | `claim`, `Auth`, `Inv`, `holdings0/1`, `cpammRely` |
| `Theorems.lean` | Exported Tx and security theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas |
| `Proofs/SwapOut.lean` | Shared `swapOut` quote `Tx.run` lemma |
| `Proofs/Security.lean` | Invariant and authorisation |
| `Proofs/Compile.lean` | Runtime `compileRuntime` non-vacuity `#guard` |
| `Proofs/Math.lean` | Floor-product facts for `k` |
| `Tests.lean` | Smoke `#guard`s |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
