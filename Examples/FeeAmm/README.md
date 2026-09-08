# FeeAmm

Constant-product pool with a 0.3% swap fee accruing to LPs and an owner-settable
protocol-fee switch. Same two-token `IERC20` bindings as `Examples/Amm` (the
fee-less teaching version). The protocol take is a share of the swap fee, not
of `amountIn`, and never enters the curve.

**Proved (Tx):** a successful swap does not decrease `reserve0 · reserve1`;
protocol buckets move only on swaps and `collectProtocolFees`; `removeLiquidity`
pays the floor pro-rata of each reserve.

**Proved (spec, later):** share-count anti-extraction and solvency of LP claims
plus protocol buckets against holdings.

**Not proved:** strict `k` increase, bytecode solvency, 512-bit `mulDiv` (a
word-overflow intermediate reverts), impermanent loss, the owner redirecting
future fees via `setFeeTo`, fee-on-transfer/rebasing tokens, reentrancy
(inherited from `Conforms`).

| File | Role |
|------|------|
| `Contract.lean` | Pool surface + `lsc_contract` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, two-token `feeAmmBs`, codec |
| `Theorems.lean` | Exported Tx, security, compiler, and bytecode theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas |
| `Proofs/Security.lean` | Invariant and authorisation (checkpoint B) |
| `Proofs/Compile.lean` | S2 compile check / compiler proofs |
| `Proofs/EndToEnd.lean` | Bytecode glue (checkpoint C) |
