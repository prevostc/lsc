# AMM walkthrough

`Examples/Amm.lean` is a constant-product pool with two `IERC20` bindings
and no fee. It is the multi-token example: same security story as Vault,
two callees instead of one.

## Design

Storage holds `reserve0` / `reserve1`, `totalShares`, `shares`, and cached
token addresses and decimals. The constructor requires the two tokens to
differ, then caches `decimals`.

The first LP mint is `a0` (no square root, no loop). Later mints are
`min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)`. Swaps use the Uniswap floor
`⌊dx·r_out/(r_in+dx)⌋`, so `k = r0·r1` cannot drop on a successful swap.
`k` is a swap fact, not part of the invariant: `removeLiquidity` floors
and can decrease `k`. Rounding favours the pool.

External calls run after requires and storage updates:

```lean
write shares[who] bal'
-- …
let _ ← Binding.transferFrom token0B who me a0.toNat
let _ ← Binding.transferFrom token1B who me a1.toNat
```

That CEI order is sound here because conforming tokens are assumed not to
reenter our storage ([External calls](EXTERNAL_CALLS.md)).

## What is proved

The invariant: each reserve is ≤ the pool's ghost balance of that token,
and share balances sum to `totalShares`.

Solvency (spec): every LP's pro-rata `⌊s·r_i/S⌋` is covered by the
corresponding ghost balance.

Unauthorised extraction (spec and bytecode): an address's **share count**
never falls unless that address called `removeLiquidity`. Swaps and
adding liquidity do not decrease another LP's share count.

Assumed, not proved in the AMM file: the `IERC20` model, `Rely`, and
conformance of both tokens; well-formed traces (`sender ≠ self`); the two
token addresses remain distinct.

The constructor is outside S2 runtime (it writes the token slots). There
is no AMM bytecode solvency theorem; solvency stays at the spec.

---

For the curious: the theorems behind this are `amm_no_unauthorized_extraction`
and `amm_bytecode_no_unauthorized_extraction` (`amm_solvent` at the spec).
