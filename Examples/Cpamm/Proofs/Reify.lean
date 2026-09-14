import Examples.Cpamm.Contract
import Lsc.Lang.Reify

/-!
LANGUAGE GAP: `Amount × Amount` certificates on CALL-bodies do not auto-close.
The reifier wraps with an anonymous `fun v => (ofWord v.1, ofWord v.2) <$>`
that `map_denote_*` does not push through a long `callAsNat` spine (simple pair
views such as `getReserves` are fine). Word-returning copies below reify;
`*.core` / `*.core_denote` for the surface pair functions are recovered from them.
`lsc_contract` lives here so it can see those cores (it cannot sit in
`Contract.lean` until pair+CALL certificates close).
-/

set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

open Lsc Lsc.Syntax Lsc.Stdlib Cpamm

namespace Cpamm

/-- Word-returning copy of `removeLiquidity` (Reify workaround). -/
def removeLiquidityW (s : Amount lpShare) : M (Nat × Nat) := do
  Tx.require (0 < s) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s ≤ bal) .InsufficientShares
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  Tx.require (0 < ts) .Zero
  let out0 ← r0 mulDiv↓ s / ts
  let out1 ← r1 mulDiv↓ s / ts
  Tx.require (0 < out0) .ZeroOut
  Tx.require (0 < out1) .ZeroOut
  let bal' ← bal -? s
  write shares[who] bal'
  let ts' ← ts -? s
  write totalShares ts'
  let r0' ← r0 -? out0
  write reserve0 r0'
  let r1' ← r1 -? out1
  write reserve1 r1'
  let t0 ← read token0
  let t1 ← read token1
  safeTransfer t0 who out0 .TransferFailed
  safeTransfer t1 who out1 .TransferFailed
  Tx.emit (.RemoveLiquidity who out0 out1 s)
  pure (out0.raw, out1.raw)

/-- Word-returning copy of `collectProtocolFees` (Reify workaround). -/
def collectProtocolFeesW : M (Nat × Nat) := do
  let who ← Tx.sender
  let ft ← read feeTo
  Tx.require (ft ≠ 0) .NoFeeTo
  Tx.require (who = ft) .NotOwner
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  write protocolFees0 0
  write protocolFees1 0
  let t0 ← read token0
  let t1 ← read token1
  safeTransfer t0 who p0 .TransferFailed
  safeTransfer t1 who p1 .TransferFailed
  Tx.emit (.ProtocolFeesCollected who p0 p1)
  pure (p0.raw, p1.raw)

end Cpamm

lsc_reify Cpamm.removeLiquidityW Cpamm.collectProtocolFeesW

namespace Cpamm

/-- Surface pair wrap used by `lsc_contract` / `core_denote`. -/
def wrapPair (v : Nat × Nat) : Amount asset0 × Amount asset1 :=
  (Amount.ofWord v.1, Amount.ofWord v.2)

set_option maxHeartbeats 8000000 in
theorem removeLiquidity_eq (s : Amount lpShare) :
    removeLiquidity s = wrapPair <$> removeLiquidityW s := by
  funext ctx w
  unfold removeLiquidity removeLiquidityW wrapPair
  simp [Tx.run_map]
  repeat' (first | rfl | split)

set_option maxHeartbeats 8000000 in
theorem collectProtocolFees_eq :
    collectProtocolFees = wrapPair <$> collectProtocolFeesW := by
  funext ctx w
  unfold collectProtocolFees collectProtocolFeesW wrapPair
  simp [Tx.run_map]
  repeat' (first | rfl | split)

abbrev removeLiquidity.core := removeLiquidityW.core
abbrev collectProtocolFees.core := collectProtocolFeesW.core

theorem removeLiquidity.core_denote (s : Amount lpShare) :
    (fun v => (Amount.ofWord (a := asset0) v.1,
        Amount.ofWord (a := asset1) v.2)) <$>
      Core.denote schema removeLiquidity.core [s.raw] =
      removeLiquidity s := by
  rw [removeLiquidity_eq]
  unfold removeLiquidity.core wrapPair
  exact congrArg
    (fun x => (fun v => (Amount.ofWord (a := asset0) v.1,
        Amount.ofWord (a := asset1) v.2)) <$> x)
    (removeLiquidityW.core_denote s)

theorem collectProtocolFees.core_denote :
    (fun v => (Amount.ofWord (a := asset0) v.1,
        Amount.ofWord (a := asset1) v.2)) <$>
      Core.denote schema collectProtocolFees.core [] =
      collectProtocolFees := by
  rw [collectProtocolFees_eq]
  unfold collectProtocolFees.core wrapPair
  exact congrArg
    (fun x => (fun v => (Amount.ofWord (a := asset0) v.1,
        Amount.ofWord (a := asset1) v.2)) <$> x)
    collectProtocolFeesW.core_denote

end Cpamm

lsc_contract Cpamm constructor addLiquidity removeLiquidity swap0for1 swap1for0
  setProtocolShare setFeeTo collectProtocolFees getReserves sharesOf protocolFees
