# Cpamm walkthrough

`Examples/Cpamm/Contract.lean` is a constant-product pool with two
`Ref (IERC20 …)` tokens, a 0.3% LP swap fee, and an owner-settable
protocol-fee switch. It is the multi-token example: same security story
as Vault, two callees instead of one.

## Design

Storage holds `token0` / `token1`, `reserve0` / `reserve1`, `totalShares`,
`shares`, `owner`, `feeTo`, `protocolShareBps`, and `protocolFees0/1`.
Amounts are indexed by the asset they denominate (`Amount asset0`,
`Amount lpShare`). The constructor requires the two tokens to differ and
stores the ref addresses.

The first LP mint is `a0` (no square root, no loop). Later mints are
`min(⌊a0·S/r0⌋, ⌊a1·S/r1⌋)`. Swaps use the 0.3%-fee notional
`⌊dx · 9970 / 10000⌋` on the curve; when `feeTo ≠ 0`, a protocol share of
that fee is skimmed into `protocolFees*` and never enters `k`. Rounding
favours the pool. `k` is a swap fact, not part of the invariant:
`removeLiquidity` floors and can decrease `k`.

External calls run after requires and storage updates:

```lean
let t0 ← read token0
let t1 ← read token1
safeTransferFrom t0 who me a0 .TransferFailed
safeTransferFrom t1 who me a1 .TransferFailed
```

That CEI order is sound here because reentrancy is not modelled
([External calls](EXTERNAL_CALLS.md)).

## What is proved

The invariant: each reserve plus that token's protocol bucket is covered
by the pool's live `balanceOf`, share balances sum to `totalShares`, and
`protocolShareBps ≤ BPS`.

Solvency (spec): every LP's pro-rata `⌊s·r_i/S⌋` plus the protocol
buckets is covered by live holdings (`cpamm_solvent`).

Unauthorised extraction (spec): an address's **share count** never falls
unless that address called `removeLiquidity` (`cpamm_no_unauthorized_extraction`).
Swaps and adding liquidity do not decrease another LP's share count.
Successful swaps do not decrease `reserve0 · reserve1` (`swap0for1_k`,
`swap1for0_k`) when `protocolShareBps ≤ BPS`.

Assumed, not proved in the Cpamm file: both tokens are distinct conforming
ERC-20s per `IERC20.Spec`; a CALL on one does not change the other's
`balanceOf` / `totalSupply` views; well-formed traces (`sender ≠ self`);
no reentrancy; no fee-on-transfer. Between calls neither pool balance may
fall (`cpammRely`). Bytecode trust is the compiler's `transport_claim_ext`
/ `transport_exists_claim_ext`, not a per-example bytecode theorem.

The constructor is outside S2 runtime (it writes the token slots).

---

For the curious: the theorems behind this are `cpamm_no_unauthorized_extraction`
and `cpamm_solvent` (`Examples/Cpamm/Theorems.lean`).
