import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Tx
import Examples.Cpamm.Proofs.Security
import Examples.Cpamm.Proofs.Compile
import Examples.Cpamm.Contract
import Lsc.Security.WealthTheorems

set_option linter.unusedVariables false

/-!
CPAMM (constant-product AMM with LP fee and protocol-fee switch) theorems:
swap `k` non-decrease, protocol-fee accounting, pro-rata redemption,
share-count anti-extraction, and LP+protocol solvency.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm

namespace Cpamm

section Tx

variable (ctx : Ctx) (w : World Storage Ext Event)

/-- A successful `swap0for1` does not decrease the product of the two reserves.
The stored protocol share of the swap fee must be at most 100% (`BPS`), which
the pool maintains after construction and `setProtocolShare`. That bound makes
the protocol take no larger than the 0.3% fee, so the input reserve grows by
at least the fee-less notional used to compute the output. Word overflow in
the `mulDiv` intermediates reverts; that is not a 512-bit `mulDiv`. -/
theorem swap0for1_k (dx : Amount token0) (minOut : Amount token1)
    {out : Amount token1} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap0for1_k ctx w dx minOut h hps

/-- A successful `swap1for0` does not decrease the product of the two reserves.
Same protocol-share bound as `swap0for1_k`. -/
theorem swap1for0_k (dx : Amount token1) (minOut : Amount token0)
    {out : Amount token0} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  Proof.swap1for0_k ctx w dx minOut h hps

/-- On a successful `swap0for1`, the token0 protocol bucket grows by exactly
`proto` (zero when `feeTo = 0`, otherwise `⌊fee · protocolShareBps / BPS⌋` of
the 0.3% swap fee) and the token1 bucket is unchanged. -/
theorem swap0_protocol_fee (dx : Amount token0) (minOut : Amount token1)
    {out : Amount token1} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees0 =
      w.self.protocolFees0 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.swap0_protocol_fee ctx w dx minOut h

/-- On a successful `swap1for0`, the token1 protocol bucket grows by exactly
`proto` and the token0 bucket is unchanged. -/
theorem swap1_protocol_fee (dx : Amount token1) (minOut : Amount token0)
    {out : Amount token0} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees1 =
      w.self.protocolFees1 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees0 = w.self.protocolFees0 :=
  Proof.swap1_protocol_fee ctx w dx minOut h

/-- Success of `collectProtocolFees` means the caller is the `feeTo` address,
both protocol buckets become 0, and the curve reserves do not move. -/
theorem collect_only_feeTo {p : Amount token0 × Amount token1}
    {w' : World Storage Ext Event}
    (h : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    ctx.sender = w.self.feeTo ∧
      w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 :=
  Proof.collect_only_feeTo ctx w h

/-- `addLiquidity` does not touch either protocol-fee bucket. -/
theorem addLiquidity_buckets (a0 : Amount token0) (a1 : Amount token1)
    {n : Amount lpShare} {w' : World Storage Ext Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.addLiquidity_buckets ctx w a0 a1 h

/-- `removeLiquidity` does not touch either protocol-fee bucket. -/
theorem removeLiquidity_buckets (s : Amount lpShare)
    {p : Amount token0 × Amount token1} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.removeLiquidity_buckets ctx w s h

/-- `setProtocolShare` does not touch either protocol-fee bucket. -/
theorem setProtocolShare_buckets (bps : Word) {w' : World Storage Ext Event}
    (h : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setProtocolShare_buckets ctx w bps h

/-- `setFeeTo` does not touch either protocol-fee bucket. -/
theorem setFeeTo_buckets (recipient : Address) {w' : World Storage Ext Event}
    (h : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.setFeeTo_buckets ctx w recipient h

/-- A successful `removeLiquidity s` pays `⌊reserve_i · s / totalShares⌋` of
each token. Success already implies a positive share supply and a positive
payout. -/
theorem removeLiquidity_pro_rata (s : Amount lpShare)
    {p : Amount token0 × Amount token1} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p.1.raw = w.self.reserve0.raw * s.raw / w.self.totalShares.raw ∧
      p.2.raw = w.self.reserve1.raw * s.raw / w.self.totalShares.raw :=
  Proof.removeLiquidity_pro_rata ctx w s h

end Tx

/-- After any well-formed sequence of pool calls, LP pro-rata claims plus
protocol-fee buckets remain covered by the pool's token balances. The
starting world must already satisfy `Inv`, and between calls neither
pool balance may fall. Callers must not be the pool itself. This is
about redeemable reserves and protocol buckets, not share count; it is
not lifted to bytecode. -/
theorem cpamm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (cpammRely self) tr w) (h : Inv self w) :
    CoversLpsAndProtocol self (run tr w) :=
  Proof.cpamm_solvent self tr w hW hR h

/-- No sequence of calls by other users can reduce Alice's LP share count
without a `removeLiquidity` she signed. Swaps, protocol-fee collection,
other LPs adding or removing, and views cannot burn her shares; she may
lose shares only through her own removals. This does not protect her
against impermanent loss — her redeemable token amounts can move when
the pool is traded. Both tokens must behave like conforming ERC-20s;
between calls neither pool balance may fall. Callers must not be the
pool itself. -/
theorem cpamm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (cpammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.cpamm_no_unauthorized_extraction self tr w a hw hW hR hA

end Cpamm
