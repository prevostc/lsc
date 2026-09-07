import Examples.Amm.Security
import Examples.Amm.SecurityProof

/-!
AMM at the spec: Alice's LP share count cannot fall unless she removed
liquidity, and each reserve is covered by the pool's balance of that
token.

Authorisation is only Alice's own `removeLiquidity`. Swaps and other
LPs cannot burn her shares. Both tokens are assumed conforming ERC-20s
at distinct addresses; between calls neither pool balance falls.

The constant product `k` is a swap fact, not these theorems:
`removeLiquidity` may decrease `k` by rounding. Solvency of pro-rata
reserves is spec-only; bytecode lifts share-count anti-extraction.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

/-- After any well-formed sequence of pool calls, each reserve is still
covered by the pool's balance of that token: every LP's pro-rata slice
of token0 (resp. token1) sums to no more than the pool holds. The
starting world must already be solvent in that sense, the two tokens
must remain distinct, and between calls neither balance may fall.
Unlike `amm_no_unauthorized_extraction` this is about redeemable
reserves, not share count; it is not lifted to bytecode. -/
theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  Proof.amm_solvent self tr w hW hR h

/-- No sequence of calls by other users can reduce Alice's LP share count
without a `removeLiquidity` she signed. Swaps, other LPs adding or
removing, and views cannot burn her shares; she may lose shares only
through her own removals. This does not protect her against impermanent
loss — her redeemable token amounts can move when the pool is traded.
Both tokens must behave like conforming ERC-20s; between calls neither
pool balance may fall. Callers must not be the pool itself. -/
theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.amm_no_unauthorized_extraction self tr w a hw hW hR hA

end Amm
