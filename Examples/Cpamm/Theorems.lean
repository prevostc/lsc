import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Tx
import Examples.Cpamm.Proofs.Security
import Stdlib.ERC20

/-!
CPAMM theorems: swap `k` non-decrease, protocol-fee accounting, pro-rata
redemption, share-count anti-extraction, and reserve+protocol solvency.
The honest-counterparty assumption (`IERC20.Spec` of both bound tokens,
and that their views do not interfere) lives in `State` / `HasDeploy`.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm Stdlib

namespace Cpamm

section Tx

variable (msg : Ctx) (w : World)

/-- A successful `swap0for1` does not decrease the product of the two reserves.
The conclusion is a Nat product (`k`); overflow in the `mulDiv` intermediates
reverts. -/
theorem swap0for1_k (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World}
    (h : Tx.run (swap0for1 dx minOut) msg w = .ok (out, w')) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap0for1_k h

/-- A successful `swap1for0` does not decrease the product of the two reserves.
The conclusion is a Nat product (`k`). -/
theorem swap1for0_k (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World}
    (h : Tx.run (swap1for0 dx minOut) msg w = .ok (out, w')) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap1for0_k h

/-- On a successful `swap0for1`, the token0 protocol bucket grows by exactly
`protocolFee` (zero when `feeTo = 0`) and the token1 bucket is unchanged. -/
theorem swap0_protocol_fee (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World}
    (h : Tx.run (swap0for1 dx minOut) msg w = .ok (out, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 + protocolFee w.self dx ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.swap0_protocol_fee h

/-- On a successful `swap1for0`, the token1 protocol bucket grows by exactly
`protocolFee` and the token0 bucket is unchanged. -/
theorem swap1_protocol_fee (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World}
    (h : Tx.run (swap1for0 dx minOut) msg w = .ok (out, w')) :
    w'.self.protocolFees1 = w.self.protocolFees1 + protocolFee w.self dx ∧
      w'.self.protocolFees0 = w.self.protocolFees0 :=
  Proof.swap1_protocol_fee h

/-- Success of `collectProtocolFees` zeros both protocol buckets and leaves
the curve reserves unchanged. -/
theorem collect_only_feeTo {p : Amount asset0 × Amount asset1}
    {w' : World}
    (h : Tx.run collectProtocolFees msg w = .ok (p, w')) :
    w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 :=
  Proof.collect_only_feeTo h

/-- `addLiquidity` does not touch either protocol-fee bucket. -/
theorem addLiquidity_buckets (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World}
    (h : Tx.run (addLiquidity a0 a1) msg w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.addLiquidity_buckets h

/-- `removeLiquidity` does not touch either protocol-fee bucket. -/
theorem removeLiquidity_buckets (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World}
    (h : Tx.run (removeLiquidity s) msg w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.removeLiquidity_buckets h

/-- `setProtocolShare` does not touch either protocol-fee bucket. -/
theorem setProtocolShare_buckets (bps : Bps) {w' : World}
    (h : Tx.run (setProtocolShare bps) msg w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setProtocolShare_buckets h

/-- `setFeeTo` does not touch either protocol-fee bucket. -/
theorem setFeeTo_buckets (recipient : Address) {w' : World}
    (h : Tx.run (setFeeTo recipient) msg w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setFeeTo_buckets h

/-- A successful `removeLiquidity s` lowers each reserve by the floor-pro-rata
payout. -/
theorem removeLiquidity_pro_rata (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World}
    (h : Tx.run (removeLiquidity s) msg w = .ok (p, w')) :
    w'.self.reserve0 = w.self.reserve0 - p.1 ∧
      w'.self.reserve1 = w.self.reserve1 - p.2 :=
  Proof.removeLiquidity_pro_rata h

/-- The tokens paid by a successful `removeLiquidity s` are the floor-pro-rata
payouts `proRata0` / `proRata1`. -/
theorem removeLiquidity_paid (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World}
    (h : Tx.run (removeLiquidity s) msg w = .ok (p, w')) :
    p.1 = proRata0 w.self s ∧ p.2 = proRata1 w.self s :=
  Proof.removeLiquidity_paid h

/-- A successful `addLiquidity` credits the caller with the minted shares
(plus the first-mint lock if the caller is address 0) and raises
`totalShares` by the minted shares plus any locked liquidity. -/
theorem addLiquidity_pro_rata (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World}
    (h : Tx.run (addLiquidity a0 a1) msg w = .ok (n, w')) :
    w'.self.shares msg.sender =
      sharesAfterDead w.self msg.sender + n ∧
      w'.self.totalShares =
        w.self.totalShares + n + lockedLiquidity w.self :=
  Proof.addLiquidity_pro_rata h

/-- Shares minted by a successful `addLiquidity` are the floor-min of the
two reserve ratios, or `a0 − 1000` on the first mint. -/
theorem addLiquidity_minted (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World}
    (h : Tx.run (addLiquidity a0 a1) msg w = .ok (n, w')) :
    n = mintedSharesAmt w.self a0 a1 :=
  Proof.addLiquidity_minted h

/-- A successful first mint leaves at least `MINIMUM_LIQUIDITY` shares
outstanding. On that mint those 1000 shares are locked at address 0. -/
theorem addLiquidity_min_liquidity (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World}
    (h : Tx.run (addLiquidity a0 a1) msg w = .ok (n, w')) :
    w.self.totalShares.raw = 0 → 1000 ≤ w'.self.totalShares.raw :=
  Proof.addLiquidity_min_liquidity h

end Tx

/-- Each reserve plus that token's protocol bucket is covered by the pool's
live token balance. -/
theorem cpamm_solvent (w : State) :
    w.self.reserve0 + w.self.protocolFees0 ≤ w.holdings0 ∧
    w.self.reserve1 + w.self.protocolFees1 ≤ w.holdings1 :=
  Proof.cpamm_solvent w

/-- Between any two moments, an LP's shares drop by at most what they
themselves redeemed. -/
theorem cpamm_no_unauthorized_extraction (w : State) (t : Txs w) (a : Address) :
    w.self.shares a ≤ t.end.self.shares a + t.spent a :=
  Proof.cpamm_no_unauthorized_extraction w t a

end Cpamm
