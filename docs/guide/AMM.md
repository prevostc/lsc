# AMM walkthrough

`Examples/Amm/Contract.lean` is a constant-product pool with two `IERC20` bindings
and no fee. It is the multi-token example: same security story as Vault,
two callees instead of one.

## Design

Storage holds `token0Ref` / `token1Ref`, `reserve0` / `reserve1`,
`totalShares`, and `shares`. Amounts are indexed by the asset they
denominate (`Amount token0`, `Amount lpShare`). The constructor requires
the two tokens to differ and stores the binding addresses; it does not
cache decimals (this pool never converts between assets).

The first LP mint is `a0` (no square root, no loop). Later mints are
`min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)`. Swaps use the Uniswap floor
`⌊dx·r_out/(r_in+dx)⌋`, so `k = r0·r1` cannot drop on a successful swap.
`k` is a swap fact, not part of the invariant: `removeLiquidity` floors
and can decrease `k`. Rounding favours the pool.

External calls run after requires and storage updates:

```lean
write shares[who] bal'
-- …
Binding.safeTransferFrom token0B who me a0 .TransferFailed
Binding.safeTransferFrom token1B who me a1 .TransferFailed
```

That CEI order is sound here because conforming tokens are assumed not to
reenter our storage ([External calls](EXTERNAL_CALLS.md)).

## What is proved

The invariant: each reserve is ≤ the pool's ghost balance of that token,
and share balances sum to `totalShares`.

Solvency (spec): every LP's pro-rata `⌊s·r_i/S⌋` is covered by the
corresponding ghost balance.

Unauthorised extraction (spec, Yul, and bytecode): an address's **share
count** never falls unless that address called `removeLiquidity`. Swaps
and adding liquidity do not decrease another LP's share count. Other
contracts cannot see the pool's private memory, which is true of the EVM.
The compiler may have used either the erase path or powdr spill
(`compileBlock`).

Assumed, not proved in the AMM file: the `IERC20` model, `Rely`, and
conformance of both tokens; well-formed traces (`sender ≠ self`); the two
token addresses remain distinct.

The constructor is outside S2 runtime (it writes the token slots). There
is no AMM bytecode solvency theorem; solvency stays at the spec.

---

For the curious: the theorems behind this are `amm_no_unauthorized_extraction`
and `amm_bytecode_no_unauthorized_extraction` (`amm_solvent` at the spec).

CPAMM (constant-product AMM with LP fee and protocol-fee switch) is
`Examples/Cpamm/Contract.lean`: same two-token shape, plus a 0.3% LP fee and
an owner-settable protocol-fee switch.
