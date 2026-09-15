# Cpamm example

Constant-product pool in LSC (`Examples/Cpamm/Contract.lean`), two
`Ref (IERC20 …)` tokens, 0.3% LP fee, protocol-fee switch.

## Design

Storage: `token0/1`, `reserve0/1`, `totalShares`, `shares`, `owner`,
`feeTo`, `protocolShareBps`, `protocolFees0/1`. First LP mint is
`a0.asUnchecked lpShare` minus `MINIMUM_LIQUIDITY = 1000` locked at
address 0 (no `sqrt`, no loop; revert `.InsufficientLiquidity` if
`a0 ≤ 1000`). Later mint is `min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)` via
`ite`. Both swap directions use `swapOut` (0.3%-fee notional, then
`require (protoFee ≤ fee)`). LPs keep the fee on the curve. When
`feeTo ≠ 0`, `⌊fee · protocolShareBps / BPS⌋` is skimmed into
`protocolFees*` and never enters `k`. CEI is state-then-call; reentrancy
is not modelled (`EXTERNAL_CALLS.md`). Constructor requires `t0 ≠ t1`.

## Invariants (proved at `Tx` / spec)

- `Inv`: `reserve_i + protocolFees_i ≤` live `holdings_i` (`tok.impl w`
  / `.balanceOf`), share support (`∑ shares = totalShares`),
  `protocolShareBps ≤ BPS`.
- `cpamm_solvent`: every LP’s pro-rata `⌊s·r_i/S⌋` plus protocol buckets
  is ≤ live `holdings_i`.
- `cpamm_no_unauthorized_extraction`: an address’s **share count** never
  falls without `Auth` (only that address’s `removeLiquidity`). Address 0
  holds the 1000 locked shares as a claim; they are not excluded.
- `addLiquidity_min_liquidity`: a successful first mint leaves
  `1000 ≤ totalShares`. `Wf` only excludes `sender = self`, so
  `ctx.sender = 0` can later burn `shares[0]`.
- `swap0for1_k` / `swap1for0_k`: `k` does not drop on a successful swap
  (not an `Inv` conjunct). `swapOut` reverts when `protoFee` would
  exceed the 0.3% fee. LP rounding favours the pool.

Assumed, not proved here: `IERC20.Spec` on both tokens; `TokensIndependent`;
`Wf` traces (`sender ≠ self`); `cpammRely`. Standard axioms only
(`propext`, `Quot.sound`, `Classical.choice`).

## Bytecode status

Examples do not ship `*_bytecode_*` theorems (DECISIONS 2026-09-12).
A Cpamm trace fact lifts through `transport_claim_ext` /
`transport_exists_claim_ext` (`Lsc/Compiler/TransportTheorems.lean`).
`Proofs/Compile.lean` is the `compileRuntime` witness. Constructor remains
out of S2 runtime (writes the token slots). User walkthrough:
`docs/guide/AMM.md`.
