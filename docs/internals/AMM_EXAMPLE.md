# AMM example

Constant-product pool in LSC (`Examples/Amm/Contract.lean`), two `IERC20` bindings, no fee.

## Design

Storage: `reserve0/1`, `totalShares`, `shares`, plus cached `token0/1` and `decimals0/1`.
First LP mint is `a0` (no `sqrt`, no loop). Later mint is
`min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)` via `ite`. Swaps use Uniswap floor
`⌊dx·r_out/(r_in+dx)⌋` so `k=r0·r1` cannot drop. CEI is state-then-call;
sound because `Conforms`/`NoInterfere` exclude reentrancy
(`SECURITY_MODEL.md`, `INTERFACE_MODEL.md`). Constructor requires `t0 ≠ t1`.

## Invariants (proved at `Tx` / `spec`)

- `Inv`: `reserve_i ≤` IERC20 ghost balance of the pool, and share support
  (`∑ shares = totalShares`).
- `amm_solvent`: every LP’s pro-rata `⌊s·r_i/S⌋` is ≤ ghost `balance_i`.
- `amm_no_unauthorized_extraction`: an address’s **share count** never falls
  without `Auth` (only that address’s `removeLiquidity`).
- `k_nondecreasing` on successful swaps (not an `Inv` conjunct: `removeLiquidity`
  floors and can drop `k`). LP rounding favours the pool.

Assumed, not proved here: IERC20 `model`/`Rely`/`Conforms`; `Wf` traces
(`sender ≠ self`). Standard axioms only
(`propext`, `Quot.sound`, `Classical.choice`).

## Bytecode status

`amm_correct_ext` instantiates family `toYulFn_correct_ext` on
`bs = [⟨α, token0B⟩, ⟨α, token1B⟩]`. Headline
`amm_bytecode_no_unauthorized_extraction` transports
`amm_no_unauthorized_extraction` (share count) to compiled runtime storage,
universally over halted calldata. Non-vacuity: Solidity-layout `Abs` at both
token addresses (requires `token0 ≠ token1`). Constructor remains out of S2
runtime (writes the token slots). User walkthrough: `docs/guide/AMM.md`.
