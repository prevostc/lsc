# AMM example

Constant-product pool in LSC (`Lsc/Examples/Amm.lean`), two `IERC20` bindings, no fee.

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
(`sender ≠ self`); no bytecode simulation. Standard axioms only
(`propext`, `Quot.sound`, `Classical.choice`).

## Compiler gaps for bytecode-level AMM theorems

`compileRuntime` is not claimed (compiler WIP). Needed: two bindings in
`ContractDef` through Yul (already in the language model), `Op.call` arities
3 and 2 (`transferFrom`/`transfer`), `mulDivDown`, and `min` as `Core.ite`.
Do not treat this example as closing the bytecode proof chain.
