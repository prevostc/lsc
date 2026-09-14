import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Tx
import Examples.Cpamm.Proofs.Security
import Stdlib.ERC20

/-!
CPAMM theorems: swap `k` non-decrease, protocol-fee accounting, pro-rata
redemption, share-count anti-extraction, and LP+protocol solvency.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm Stdlib

namespace Cpamm

section Tx

variable (ctx : Ctx) (w : World Storage ExtState Event)

/-- A successful `swap0for1` does not decrease the product of the two reserves.
`protocolShareBps ≤ BPS` is required at `Tx.run` level: a stored share above
100% can skim more than the 0.3% fee, so the input reserve can grow by less
than the fee-less notional used to compute the output and `k` can fall.
The pool maintains that bound after construction and `setProtocolShare`.
Word overflow in the `mulDiv` intermediates reverts; that is not a 512-bit
`mulDiv`. -/
theorem swap0for1_k (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap0for1_k h hps

/-- A successful `swap1for0` does not decrease the product of the two reserves.
Same protocol-share bound as `swap0for1_k`. -/
theorem swap1for0_k (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap1for0_k h hps

/-- On a successful `swap0for1`, the token0 protocol bucket grows by exactly
`proto` (zero when `feeTo = 0`, otherwise `⌊fee · protocolShareBps / BPS⌋` of
the 0.3% swap fee) and the token1 bucket is unchanged. -/
theorem swap0_protocol_fee (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees0 =
      w.self.protocolFees0 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.swap0_protocol_fee h

/-- On a successful `swap1for0`, the token1 protocol bucket grows by exactly
`proto` and the token0 bucket is unchanged. -/
theorem swap1_protocol_fee (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees1 =
      w.self.protocolFees1 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees0 = w.self.protocolFees0 :=
  Proof.swap1_protocol_fee h

/-- Success of `collectProtocolFees` zeros both protocol buckets and leaves
the curve reserves unchanged. -/
theorem collect_only_feeTo {p : Amount asset0 × Amount asset1}
    {w' : World Storage ExtState Event}
    (h : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 :=
  Proof.collect_only_feeTo h

/-- `addLiquidity` does not touch either protocol-fee bucket. -/
theorem addLiquidity_buckets (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.addLiquidity_buckets h

/-- `removeLiquidity` does not touch either protocol-fee bucket. -/
theorem removeLiquidity_buckets (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.removeLiquidity_buckets h

/-- `setProtocolShare` does not touch either protocol-fee bucket. -/
theorem setProtocolShare_buckets (bps : Bps) {w' : World Storage ExtState Event}
    (h : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setProtocolShare_buckets h

/-- `setFeeTo` does not touch either protocol-fee bucket. -/
theorem setFeeTo_buckets (recipient : Address) {w' : World Storage ExtState Event}
    (h : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setFeeTo_buckets h

/-- A successful `removeLiquidity s` lowers each reserve by the floor-pro-rata
payout. Success already implies a positive share supply and a positive
payout. -/
theorem removeLiquidity_pro_rata (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.reserve0 = w.self.reserve0 - p.1 ∧
      w'.self.reserve1 = w.self.reserve1 - p.2 :=
  Proof.removeLiquidity_pro_rata h

/-- The tokens paid by a successful `removeLiquidity s` are
`⌊reserve_i · s / totalShares⌋`. -/
theorem removeLiquidity_paid (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p.1.raw = w.self.reserve0.raw * s.raw / w.self.totalShares.raw ∧
      p.2.raw = w.self.reserve1.raw * s.raw / w.self.totalShares.raw :=
  Proof.removeLiquidity_paid h

/-- A successful `addLiquidity` credits the caller and `totalShares` by the
minted shares. -/
theorem addLiquidity_pro_rata (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender + n ∧
      w'.self.totalShares = w.self.totalShares + n :=
  Proof.addLiquidity_pro_rata h

/-- Shares minted by a successful `addLiquidity` are the floor-min of the
two reserve ratios, or `a0` on the first mint. -/
theorem addLiquidity_minted (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    n = Amount.ofWord (mintedShares w.self a0.raw a1.raw) :=
  Proof.addLiquidity_minted h

end Tx

/-- After any well-formed sequence of pool calls, LP pro-rata claims plus
protocol-fee buckets remain covered by the pool's token balances. The
starting world must already satisfy `Inv`, and between calls neither
pool balance may fall. Assumed of the tokens: they are distinct conforming
ERC-20s per `IERC20.Spec`; a CALL on one does not change the other's
`balanceOf` / `totalSupply` views; no reentrancy is modelled; no
fee-on-transfer. Callers must not be the pool itself. -/
theorem cpamm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage ExtState Event)
    (hW : Wf self tr)
    (hR : RelyAlong (cpammRely self w.self.token0 w.self.token1 w.oracle) tr w)
    (hT0 : IERC20.Spec (w.self.token0.impl : Token0Impl))
    (hT1 : IERC20.Spec (w.self.token1.impl : Token1Impl))
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (h : Inv self w) :
    CoversLpsAndProtocol self (run tr w) :=
  Proof.cpamm_solvent self tr w hW hR hT0 hT1 hInd h

/-- No sequence of calls by other users can reduce Alice's LP share count
without a `removeLiquidity` she signed. Swaps, protocol-fee collection,
other LPs adding or removing, and views cannot burn her shares; she may
lose shares only through her own removals. This does not protect her
against impermanent loss. Assumed of the tokens: they are distinct
conforming ERC-20s per `IERC20.Spec`; a CALL on one does not change the
other's views; no reentrancy is modelled; no fee-on-transfer. Between
calls neither pool balance may fall. Callers must not be the pool itself. -/
theorem cpamm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr)
    (hR : RelyAlong (cpammRely self w.self.token0 w.self.token1 w.oracle) tr w)
    (hT0 : IERC20.Spec (w.self.token0.impl : Token0Impl))
    (hT1 : IERC20.Spec (w.self.token1.impl : Token1Impl))
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.cpamm_no_unauthorized_extraction self tr w a hw hW hR hT0 hT1 hInd hA

end Cpamm
