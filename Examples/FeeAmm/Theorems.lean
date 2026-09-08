import Examples.FeeAmm.Spec
import Examples.FeeAmm.Proofs.Tx
import Examples.FeeAmm.Contract

set_option linter.unusedVariables false

/-!
FeeAmm theorems: swap `k` non-decrease, protocol-fee accounting, pro-rata
redemption, and (later) anti-extraction / solvency.
-/

open Lsc Lsc.Stdlib FeeAmm

namespace FeeAmm

variable (ctx : Ctx) (w : World Storage Ext Event)

/-- A successful `swap0for1` does not decrease the product of the two reserves.
The stored protocol share of the swap fee must be at most 100% (`BPS`), which
the pool maintains after construction and `setProtocolShare`. That bound makes
the protocol take no larger than the 0.3% fee, so the input reserve grows by
at least the fee-less notional used to compute the output. Word overflow in
the `mulDiv` intermediates reverts; that is not a 512-bit `mulDiv`. -/
theorem swap0for1_k (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0 * w'.self.reserve1 ≥ w.self.reserve0 * w.self.reserve1 :=
  Proof.swap0for1_k ctx w dx minOut h hps

/-- A successful `swap1for0` does not decrease the product of the two reserves.
Same protocol-share bound as `swap0for1_k`. -/
theorem swap1for0_k (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0 * w'.self.reserve1 ≥ w.self.reserve0 * w.self.reserve1 :=
  Proof.swap1for0_k ctx w dx minOut h hps

/-- On a successful `swap0for1`, the token0 protocol bucket grows by exactly
`proto` (zero when `feeTo = 0`, otherwise `⌊fee · protocolShareBps / BPS⌋` of
the 0.3% swap fee) and the token1 bucket is unchanged. -/
theorem swap0_protocol_fee (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 + protoOf w.self dx.toNat ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.swap0_protocol_fee ctx w dx minOut h

/-- On a successful `swap1for0`, the token1 protocol bucket grows by exactly
`proto` and the token0 bucket is unchanged. -/
theorem swap1_protocol_fee (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees1 = w.self.protocolFees1 + protoOf w.self dx.toNat ∧
      w'.self.protocolFees0 = w.self.protocolFees0 :=
  Proof.swap1_protocol_fee ctx w dx minOut h

/-- Success of `collectProtocolFees` means the caller is the `feeTo` address,
both protocol buckets become 0, and the curve reserves do not move. -/
theorem collect_only_feeTo {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    ctx.sender = w.self.feeTo ∧
      w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 :=
  Proof.collect_only_feeTo ctx w h

/-- `addLiquidity` does not touch either protocol-fee bucket. -/
theorem addLiquidity_buckets (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
    {n : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.addLiquidity_buckets ctx w a0 a1 h

/-- `removeLiquidity` does not touch either protocol-fee bucket. -/
theorem removeLiquidity_buckets (s : Amount SHARE shareScale)
    {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 :=
  Proof.removeLiquidity_buckets ctx w s h

/-- `setProtocolShare` does not touch either protocol-fee bucket. -/
theorem setProtocolShare_buckets (bps : Nat) {w' : World Storage Ext Event}
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

/-- A successful `removeLiquidity s` pays `⌊s · reserve_i / totalShares⌋` of each
token. Success already implies a positive share supply and a positive payout. -/
theorem removeLiquidity_pro_rata (s : Amount SHARE shareScale)
    {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p.1 = s.toNat * w.self.reserve0 / w.self.totalShares ∧
      p.2 = s.toNat * w.self.reserve1 / w.self.totalShares :=
  Proof.removeLiquidity_pro_rata ctx w s h

end FeeAmm
