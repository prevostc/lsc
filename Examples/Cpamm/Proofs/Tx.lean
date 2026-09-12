import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Examples.Cpamm.Spec
import Examples.Cpamm.Contract
import Examples.Cpamm.Proofs.Math
import Stdlib.SafeERC20

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
# CPAMM — functional lemmas

`Tx.run` statements. Storage is `Nat`; ABI amounts use `toNat` / `ofNat`.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm

namespace Cpamm

variable (ctx : Ctx) (w : World Storage Ext Event)

/-! ### Pure arithmetic (rounding toward the pool, `k` monotone on swaps) -/

/-- Floor share-then-redeem of a deposit cannot exceed the deposited amount. -/
theorem lp_round_favors_pool (a r S : Nat) (_hr : 0 < r) (hS : 0 < S) :
    (a * S / r) * r / S ≤ a := by
  have hchop : (a * S / r) * r ≤ a * S := by
    rw [Nat.mul_comm (a * S / r)]
    exact Nat.mul_div_le (a * S) r
  have hdiv : (a * S / r) * r / S ≤ a * S / S := Nat.div_le_div_right hchop
  have hcancel : a * S / S = a := by
    rw [Nat.mul_comm a S]
    exact Nat.mul_div_cancel_left a hS
  rwa [hcancel] at hdiv

/-- `simp` unfolds `Tx.require (0 < a / b)` to `0 < b ∧ b ≤ a`. -/
theorem pos_div_iff {a b : Nat} : 0 < a / b ↔ 0 < b ∧ b ≤ a := by
  rw [Nat.pos_iff_ne_zero, ne_eq, Nat.div_eq_zero_iff]
  omega

/-! ### Share accounting -/

theorem shares_conserved (σ : Storage) (h : InvStorage σ) :
    ∃ H : Finset Address,
      (∀ a, a ∉ H → σ.shares a = 0) ∧
      H.sum (fun a => σ.shares a) = σ.totalShares :=
  h

/-! ### Post-states -/

def mintedShares (σ : Storage) (a0 a1 : Nat) : Nat :=
  if σ.totalShares = 0 then a0
  else if a0 * σ.totalShares / σ.reserve0 ≤ a1 * σ.totalShares / σ.reserve1 then
    a0 * σ.totalShares / σ.reserve0
  else
    a1 * σ.totalShares / σ.reserve1

private theorem not_side0 {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares ≠ 0) (hr0 : 0 < σ.reserve0)
    (hle : a0 * σ.totalShares / σ.reserve0 ≤ a1 * σ.totalShares / σ.reserve1)
    (hminted : ¬ 0 < mintedShares σ a0 a1) :
    ¬ σ.reserve0 ≤ a0 * σ.totalShares := by
  intro h
  refine hminted ?_
  simp [mintedShares, hts, hle, pos_div_iff]
  exact ⟨hr0, h⟩

private theorem not_side1 {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares ≠ 0) (hr1 : 0 < σ.reserve1)
    (hle : ¬ a0 * σ.totalShares / σ.reserve0 ≤ a1 * σ.totalShares / σ.reserve1)
    (hminted : ¬ 0 < mintedShares σ a0 a1) :
    ¬ σ.reserve1 ≤ a1 * σ.totalShares := by
  intro h
  refine hminted ?_
  simp [mintedShares, hts, hle, pos_div_iff]
  exact ⟨hr1, h⟩

def addLiquidityPost (σ : Storage) (who : Address) (a0 a1 : Nat) : Storage :=
  let n := mintedShares σ a0 a1
  { σ with
    reserve0 := σ.reserve0 + a0
    reserve1 := σ.reserve1 + a1
    totalShares := n + σ.totalShares
    shares := Function.update σ.shares who (n + σ.shares who) }

def redeemed (σ : Storage) (s : Nat) : Nat × Nat :=
  (s * σ.reserve0 / σ.totalShares, s * σ.reserve1 / σ.totalShares)

def removeLiquidityPost (σ : Storage) (who : Address) (s : Nat) : Storage :=
  let out := redeemed σ s
  { σ with
    reserve0 := σ.reserve0 - out.1
    reserve1 := σ.reserve1 - out.2
    totalShares := σ.totalShares - s
    shares := Function.update σ.shares who (σ.shares who - s) }

def swap0Post (σ : Storage) (dx proto out : Nat) : Storage :=
  { σ with
    reserve0 := σ.reserve0 + (dx - proto)
    reserve1 := σ.reserve1 - out
    protocolFees0 := σ.protocolFees0 + proto }

def swap1Post (σ : Storage) (dx proto out : Nat) : Storage :=
  { σ with
    reserve1 := σ.reserve1 + (dx - proto)
    reserve0 := σ.reserve0 - out
    protocolFees1 := σ.protocolFees1 + proto }

/-- Same as `amountOutF` (fee-less notional `dxF`). -/
def amountOut (rIn rOut dx : Nat) : Nat := amountOutF rIn rOut dx

def coeffOf (σ : Storage) : Nat := if σ.feeTo = 0 then 0 else σ.protocolShareBps

def protoOf (σ : Storage) (dx : Nat) : Nat :=
  protoTake σ.feeTo σ.protocolShareBps (swapFee dx)

theorem BPS_eq : BPS = 10000 := rfl

attribute [local simp] BPS

theorem dxFeeLess_lit (dx : Nat) : dxFeeLess dx = dx * 9970 / 10000 := rfl

theorem BPS_pos : 0 < BPS := by decide

theorem dxFeeLess_le (dx : Nat) : dxFeeLess dx ≤ dx := by
  simpa [dxFeeLess, Nat.mul_comm dx] using
    remove_le_reserves (BPS - FEE_BPS) dx BPS (Nat.sub_le _ _) BPS_pos

theorem protoOf_le_dx (σ : Storage) (dx : Nat) (h : σ.protocolShareBps ≤ BPS) :
    protoOf σ dx ≤ dx := by
  have hfee : protoOf σ dx ≤ swapFee dx := protoTake_le_fee σ.feeTo σ.protocolShareBps (swapFee dx) h
  have hdx : swapFee dx ≤ dx := Nat.sub_le _ _
  exact Nat.le_trans hfee hdx

theorem coeffOf_le_BPS (σ : Storage) (h : σ.protocolShareBps ≤ BPS) :
    coeffOf σ ≤ BPS := by
  unfold coeffOf
  split_ifs
  · exact Nat.zero_le _
  · exact h

def extAfterPull (x : Ext) (src dst : Address) (a0 a1 : Nat) : Ext :=
  { token0 := move x.token0 src dst a0
    token1 := move x.token1 src dst a1 }

def extAfterPush (x : Ext) (src dst : Address) (a0 a1 : Nat) : Ext :=
  { token0 := move x.token0 src dst a0
    token1 := move x.token1 src dst a1 }

def extAfterSwap0 (x : Ext) (user self : Address) (dx out : Nat) : Ext :=
  { token0 := move x.token0 user self dx
    token1 := move x.token1 self user out }

def extAfterSwap1 (x : Ext) (user self : Address) (dx out : Nat) : Ext :=
  { token0 := move x.token0 self user out
    token1 := move x.token1 user self dx }

theorem minted_le_side0 (σ : Storage) (a0 a1 : Nat)
    (hS : 0 < σ.totalShares) (hr0 : 0 < σ.reserve0) :
    mintedShares σ a0 a1 * σ.reserve0 / σ.totalShares ≤ a0 := by
  have hne : σ.totalShares ≠ 0 := Nat.ne_of_gt hS
  have hmin : mintedShares σ a0 a1 ≤ a0 * σ.totalShares / σ.reserve0 := by
    unfold mintedShares
    rw [if_neg hne]
    split_ifs with h
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_not_le h)
  have hfav := lp_round_favors_pool a0 σ.reserve0 σ.totalShares hr0 hS
  have hmono : mintedShares σ a0 a1 * σ.reserve0 / σ.totalShares ≤
      (a0 * σ.totalShares / σ.reserve0) * σ.reserve0 / σ.totalShares :=
    Nat.div_le_div_right (Nat.mul_le_mul_right σ.reserve0 hmin)
  exact Nat.le_trans hmono hfav

theorem minted_le_side1 (σ : Storage) (a0 a1 : Nat)
    (hS : 0 < σ.totalShares) (hr1 : 0 < σ.reserve1) :
    mintedShares σ a0 a1 * σ.reserve1 / σ.totalShares ≤ a1 := by
  have hne : σ.totalShares ≠ 0 := Nat.ne_of_gt hS
  have hmin : mintedShares σ a0 a1 ≤ a1 * σ.totalShares / σ.reserve1 := by
    unfold mintedShares
    rw [if_neg hne]
    split_ifs with h
    · exact h
    · exact Nat.le_refl _
  have hfav := lp_round_favors_pool a1 σ.reserve1 σ.totalShares hr1 hS
  have hmono : mintedShares σ a0 a1 * σ.reserve1 / σ.totalShares ≤
      (a1 * σ.totalShares / σ.reserve1) * σ.reserve1 / σ.totalShares :=
    Nat.div_le_div_right (Nat.mul_le_mul_right σ.reserve1 hmin)
  exact Nat.le_trans hmono hfav

/-! ### Success bundles -/

structure AddLiqOk (w : World Storage Ext Event) (ctx : Ctx)
    (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1) : Prop where
  pos0 : 0 < a0.toNat
  pos1 : 0 < a1.toNat
  minted : 0 < mintedShares w.self a0.toNat a1.toNat
  prod :
    w.self.totalShares = 0 ∨
      (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
        a0.toNat * w.self.totalShares < wordBound ∧
        a1.toNat * w.self.totalShares < wordBound)
  add0 : w.self.reserve0 + a0.toNat < wordBound
  add1 : w.self.reserve1 + a1.toNat < wordBound
  addS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound
  addB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  cov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender
  cov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender

structure RemoveOk (w : World Storage Ext Event) (ctx : Ctx)
    (s : Amount SHARE shareScale) : Prop where
  pos : 0 < s.toNat
  bal : s.toNat ≤ w.self.shares ctx.sender
  ts : 0 < w.self.totalShares
  sLe : s.toNat ≤ w.self.totalShares
  out0 : 0 < (redeemed w.self s.toNat).1
  out1 : 0 < (redeemed w.self s.toNat).2
  le0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0
  le1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1
  mul0 : s.toNat * w.self.reserve0 < wordBound
  mul1 : s.toNat * w.self.reserve1 < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  cov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self
  cov1 : (redeemed w.self s.toNat).2 ≤ w.ext.token1.balances ctx.self

structure Swap0Ok (w : World Storage Ext Event) (ctx : Ctx)
    (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1) : Prop where
  pos : 0 < dx.toNat
  r0 : 0 < w.self.reserve0
  r1 : 0 < w.self.reserve1
  dxF_mul : dx.toNat * 9970 < wordBound
  den : w.self.reserve0 + dxFeeLess dx.toNat < wordBound
  out_mul : dxFeeLess dx.toNat * w.self.reserve1 < wordBound
  min : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  out : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  proto_mul : swapFee dx.toNat * coeffOf w.self < wordBound
  taken : protoOf w.self dx.toNat ≤ dx.toNat
  add : w.self.reserve0 + (dx.toNat - protoOf w.self dx.toNat) < wordBound
  acc : w.self.feeTo ≠ 0 →
    w.self.protocolFees0 + protoOf w.self dx.toNat < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  covIn : dx.toNat ≤ w.ext.token0.balances ctx.sender
  covOut : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
    w.ext.token1.balances ctx.self

structure Swap1Ok (w : World Storage Ext Event) (ctx : Ctx)
    (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0) : Prop where
  pos : 0 < dx.toNat
  r0 : 0 < w.self.reserve0
  r1 : 0 < w.self.reserve1
  dxF_mul : dx.toNat * 9970 < wordBound
  den : w.self.reserve1 + dxFeeLess dx.toNat < wordBound
  out_mul : dxFeeLess dx.toNat * w.self.reserve0 < wordBound
  min : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  out : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  proto_mul : swapFee dx.toNat * coeffOf w.self < wordBound
  taken : protoOf w.self dx.toNat ≤ dx.toNat
  add : w.self.reserve1 + (dx.toNat - protoOf w.self dx.toNat) < wordBound
  acc : w.self.feeTo ≠ 0 →
    w.self.protocolFees1 + protoOf w.self dx.toNat < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  covIn : dx.toNat ≤ w.ext.token1.balances ctx.sender
  covOut : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
    w.ext.token0.balances ctx.self

/-! ### Views -/

theorem getReserves_ok :
    Tx.run getReserves ctx w = .ok ((w.self.reserve0, w.self.reserve1), w) := by
  simp [getReserves]

theorem sharesOf_ok (who : Address) :
    Tx.run (sharesOf who) ctx w = .ok (w.self.shares who, w) := by
  simp [sharesOf]

theorem protocolFees_ok :
    Tx.run protocolFees ctx w =
      .ok ((w.self.protocolFees0, w.self.protocolFees1), w) := by
  simp [protocolFees]

/-! ### Owner / protocol-fee admin -/

theorem setProtocolShare_ok (bps : Nat)
    (hown : ctx.sender = w.self.owner) (hle : bps ≤ 10000) :
    Tx.run (setProtocolShare bps) ctx w =
      .ok ((), { w with
        self := { w.self with protocolShareBps := bps }
        log := w.log ++ [.ProtocolShareSet bps] }) := by
  simp [setProtocolShare, hown, hle]

theorem setProtocolShare_ok_of_run {bps : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    ctx.sender = w.self.owner ∧ bps ≤ 10000 ∧
      w' = { w with
        self := { w.self with protocolShareBps := bps }
        log := w.log ++ [.ProtocolShareSet bps] } := by
  have hown : ctx.sender = w.self.owner := by
    by_contra h; simp [setProtocolShare, h] at hrun
  have hle : bps ≤ 10000 := by
    by_contra h; simp [setProtocolShare, hown, h] at hrun
  refine ⟨hown, hle, ?_⟩
  cases hrun.symm.trans (setProtocolShare_ok ctx w bps hown hle); rfl

theorem setFeeTo_ok (recipient : Address) (hown : ctx.sender = w.self.owner) :
    Tx.run (setFeeTo recipient) ctx w =
      .ok ((), { w with
        self := { w.self with feeTo := recipient }
        log := w.log ++ [.FeeToSet recipient] }) := by
  simp [setFeeTo, hown]

theorem setFeeTo_ok_of_run {recipient : Address} {w' : World Storage Ext Event}
    (hrun : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    ctx.sender = w.self.owner ∧
      w' = { w with
        self := { w.self with feeTo := recipient }
        log := w.log ++ [.FeeToSet recipient] } := by
  have hown : ctx.sender = w.self.owner := by
    by_contra h; simp [setFeeTo, h] at hrun
  refine ⟨hown, ?_⟩
  cases hrun.symm.trans (setFeeTo_ok ctx w recipient hown); rfl

structure CollectOk (w : World Storage Ext Event) (ctx : Ctx) : Prop where
  ft : w.self.feeTo ≠ 0
  who : ctx.sender = w.self.feeTo
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  cov0 : w.self.protocolFees0 ≤ w.ext.token0.balances ctx.self
  cov1 : w.self.protocolFees1 ≤ w.ext.token1.balances ctx.self

def collectPost (σ : Storage) : Storage :=
  { σ with protocolFees0 := 0, protocolFees1 := 0 }

def extAfterCollect (x : Ext) (self who : Address) (p0 p1 : Nat) : Ext :=
  { token0 := move x.token0 self who p0
    token1 := move x.token1 self who p1 }

theorem collectProtocolFees_ok (h : CollectOk w ctx) :
    Tx.run collectProtocolFees ctx w =
      .ok ((w.self.protocolFees0, w.self.protocolFees1),
        World.mk (collectPost w.self)
          (extAfterCollect w.ext ctx.self ctx.sender
            w.self.protocolFees0 w.self.protocolFees1)
          (w.log ++ [.ProtocolFeesCollected ctx.sender
            (Amount.ofNat w.self.protocolFees0)
            (Amount.ofNat w.self.protocolFees1)])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hft, hwho, hnf0, hnf1, hcov0, hcov1⟩
  have hx0 : model .transfer ctx.self [w.self.feeTo, w.self.protocolFees0] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self w.self.feeTo w.self.protocolFees0) := by
    simpa [hwho] using model_transfer (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees0) (g := w.ext.token0) hcov0
  have hx1 : model .transfer ctx.self [w.self.feeTo, w.self.protocolFees1] w.ext.token1 =
      some (1, move w.ext.token1 ctx.self w.self.feeTo w.self.protocolFees1) := by
    simpa [hwho] using model_transfer (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees1) (g := w.ext.token1) hcov1
  simp [collectProtocolFees, hft, hwho]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
  simp [extAfterCollect, collectPost, hwho]

theorem collectProtocolFees_reverts_on_fault0
    (hft : w.self.feeTo ≠ 0) (hwho : ctx.sender = w.self.feeTo)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run collectProtocolFees ctx w = .error .callFailed := by
  simp [collectProtocolFees, hft, hwho]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0]

theorem collectProtocolFees_reverts_on_no_cover0
    (hft : w.self.feeTo ≠ 0) (hwho : ctx.sender = w.self.feeTo)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : ¬ w.self.protocolFees0 ≤ w.ext.token0.balances ctx.self) :
    Tx.run collectProtocolFees ctx w = .error .callFailed := by
  simp [collectProtocolFees, hft, hwho]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, model, hcov0]

theorem collectProtocolFees_reverts_on_fault1
    (hft : w.self.feeTo ≠ 0) (hwho : ctx.sender = w.self.feeTo)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : w.self.protocolFees0 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run collectProtocolFees ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [w.self.feeTo, w.self.protocolFees0] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self w.self.feeTo w.self.protocolFees0) := by
    simpa [hwho] using model_transfer (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees0) (g := w.ext.token0) hcov0
  simp [collectProtocolFees, hft, hwho]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1]

theorem collectProtocolFees_reverts_on_no_cover1
    (hft : w.self.feeTo ≠ 0) (hwho : ctx.sender = w.self.feeTo)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : w.self.protocolFees0 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcov1 : ¬ w.self.protocolFees1 ≤ w.ext.token1.balances ctx.self) :
    Tx.run collectProtocolFees ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [w.self.feeTo, w.self.protocolFees0] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self w.self.feeTo w.self.protocolFees0) := by
    simpa [hwho] using model_transfer (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees0) (g := w.ext.token0) hcov0
  simp [collectProtocolFees, hft, hwho]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1, model, hcov1]

theorem collectProtocolFees_ok_of_run {p : Nat × Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    CollectOk w ctx := by
  have hft : w.self.feeTo ≠ 0 := by
    by_contra h; simp [collectProtocolFees, h] at hrun
  have hwho : ctx.sender = w.self.feeTo := by
    by_contra h; simp [collectProtocolFees, hft, h] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (collectProtocolFees_reverts_on_fault0 ctx w hft hwho hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov0 : w.self.protocolFees0 ≤ w.ext.token0.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (collectProtocolFees_reverts_on_no_cover0 ctx w hft hwho hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun
        (collectProtocolFees_reverts_on_fault1 ctx w hft hwho hnf0 hcov0 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov1 : w.self.protocolFees1 ≤ w.ext.token1.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun
      (collectProtocolFees_reverts_on_no_cover1 ctx w hft hwho hnf0 hcov0 hnf1 h)
  exact ⟨hft, hwho, hnf0, hnf1, hcov0, hcov1⟩

/-! ### `addLiquidity` -/

theorem addLiquidity_ok (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
    (h : AddLiqOk w ctx a0 a1) :
    Tx.run (addLiquidity a0 a1) ctx w =
      .ok (mintedShares w.self a0.toNat a1.toNat,
        World.mk (addLiquidityPost w.self ctx.sender a0.toNat a1.toNat)
          (extAfterPull w.ext ctx.sender ctx.self a0.toNat a1.toNat)
          (w.log ++ [.AddLiquidity ctx.sender a0 a1
            (Amount.ofNat (mintedShares w.self a0.toNat a1.toNat))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hnf0, hnf1, hcov0, hcov1⟩
  have hx0 : model .transferFrom ctx.self [ctx.sender, ctx.self, a0.toNat] w.ext.token0 =
      some (1, move w.ext.token0 ctx.sender ctx.self a0.toNat) :=
    model_transferFrom hcov0
  have hx1 : model .transferFrom ctx.self [ctx.sender, ctx.self, a1.toNat] w.ext.token1 =
      some (1, move w.ext.token1 ctx.sender ctx.self a1.toNat) :=
    model_transferFrom hcov1
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call
    dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
    simp [extAfterPull, addLiquidityPost, mintedShares, hts]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call
        dsimp only [Tx.run]
        simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
        simp [extAfterPull, addLiquidityPost, mintedShares, hts, hle]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call
        dsimp only [Tx.run]
        simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
        simp [extAfterPull, addLiquidityPost, mintedShares, hts, hle]

theorem addLiquidity_reverts_on_fault0 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound)
    (haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [hf0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [hf0]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [hf0]

theorem addLiquidity_reverts_on_no_cover0 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound)
    (haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : ¬ a0.toNat ≤ w.ext.token0.balances ctx.sender) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, model, hcov0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, model, hcov0]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, model, hcov0]

theorem addLiquidity_reverts_on_fault1 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound)
    (haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  have hx0 := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := a0.toNat) (callee := ctx.self) hcov0
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, hx0]
    simp [hf1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [hf1]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [hf1]

theorem addLiquidity_reverts_on_no_cover1 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound)
    (haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcov1 : ¬ a1.toNat ≤ w.ext.token1.balances ctx.sender) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  have hx0 := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := a0.toNat) (callee := ctx.self) hcov0
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, hx0]
    simp [token1B, IERC20.model_eq, hf1, model, hcov1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [token1B, IERC20.model_eq, hf1, model, hcov1]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [token1B, IERC20.model_eq, hf1, model, hcov1]

theorem addLiquidity_reverts_on_add_r0 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : ¬ w.self.reserve0 + a0.toNat < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at hminted
    simp [hts, hadd0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0]

theorem addLiquidity_reverts_on_add_r1 (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : ¬ w.self.reserve1 + a1.toNat < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp [hts, mintedShares] at hminted
    simp [hts, hadd0, hadd1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1]

theorem addLiquidity_reverts_on_add_shares (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : ¬ mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp only [mintedShares, hts] at haddS hminted
    have hS : ¬ a0.toNat < wordBound := by simpa [Nat.add_zero] using haddS
    simp [hts, hadd0, hadd1, hS]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        have hS :
            ¬ a0.toNat * w.self.totalShares / w.self.reserve0 + w.self.totalShares
                < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_pos hle] at haddS
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        have hS :
            ¬ a1.toNat * w.self.totalShares / w.self.reserve1 + w.self.totalShares
                < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_neg hle] at haddS
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS]

theorem addLiquidity_reverts_on_add_bal (a0 : Amount TOKEN0 scale0)
    (a1 : Amount TOKEN1 scale1)
    (hpos0 : 0 < a0.toNat) (hpos1 : 0 < a1.toNat)
    (hminted : 0 < mintedShares w.self a0.toNat a1.toNat)
    (hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound))
    (hadd0 : w.self.reserve0 + a0.toNat < wordBound)
    (hadd1 : w.self.reserve1 + a1.toNat < wordBound)
    (haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound)
    (haddB : ¬ mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1]
  by_cases hts : w.self.totalShares = 0
  · simp only [mintedShares, hts] at haddS haddB hminted
    have hS : a0.toNat < wordBound := by simpa [Nat.add_zero] using haddS
    have hB : ¬ a0.toNat + w.self.shares ctx.sender < wordBound := by
      simpa using haddB
    simp [hts, hadd0, hadd1, hS, hB]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hminted' : 0 < a0.toNat * w.self.totalShares / w.self.reserve0 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0 ≤ a0.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        have hS :
            a0.toNat * w.self.totalShares / w.self.reserve0 + w.self.totalShares
              < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_pos hle] at haddS
        have hB :
            ¬ a0.toNat * w.self.totalShares / w.self.reserve0 + w.self.shares ctx.sender
                < wordBound := by
          unfold mintedShares at haddB
          rwa [if_neg hts, if_pos hle] at haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS, hB]
      · have hminted' : 0 < a1.toNat * w.self.totalShares / w.self.reserve1 := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1 ≤ a1.toNat * w.self.totalShares :=
          (pos_div_iff.mp hminted').2
        have hS :
            a1.toNat * w.self.totalShares / w.self.reserve1 + w.self.totalShares
              < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_neg hle] at haddS
        have hB :
            ¬ a1.toNat * w.self.totalShares / w.self.reserve1 + w.self.shares ctx.sender
                < wordBound := by
          unfold mintedShares at haddB
          rwa [if_neg hts, if_neg hle] at haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS, hB]

/-- Success of `addLiquidity` implies the `AddLiqOk` bundle. -/
theorem addLiquidity_ok_of_run {a0 : Amount TOKEN0 scale0} {a1 : Amount TOKEN1 scale1}
    {n : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    AddLiqOk w ctx a0 a1 := by
  have hpos0 : 0 < a0.toNat := by
    by_contra hp; simp [addLiquidity, hp] at hrun
  have hpos1 : 0 < a1.toNat := by
    by_contra hp; simp [addLiquidity, hpos0, hp] at hrun
  have hprod :
      w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound) := by
    by_cases hts : w.self.totalShares = 0
    · exact Or.inl hts
    · by_cases hr0 : 0 < w.self.reserve0
      · by_cases hr1 : 0 < w.self.reserve1
        · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
          have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
          by_cases hm0 : a0.toNat * w.self.totalShares < wordBound
          · by_cases hm1 : a1.toNat * w.self.totalShares < wordBound
            · exact Or.inr ⟨hr0, hr1, hm0, hm1⟩
            · simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1] at hrun
          · simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0] at hrun
        · have hz : w.self.reserve1 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr1)
          have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hz] at hrun
      · have hz : w.self.reserve0 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr0)
        simp [addLiquidity, hpos0, hpos1, hts, hz] at hrun
  have hminted : 0 < mintedShares w.self a0.toNat a1.toNat := by
    by_contra hm
    by_cases hts : w.self.totalShares = 0
    · simp [mintedShares, hts] at hm
      omega
    · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
      · exact hts h0
      · have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
        have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
        by_cases hle :
            a0.toNat * w.self.totalShares / w.self.reserve0 ≤
              a1.toNat * w.self.totalShares / w.self.reserve1
        · have hreq := not_side0 hts hr0 hle hm
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq] at hrun
        · have hreq := not_side1 hts hr1 hle hm
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq] at hrun
  have hadd0 : w.self.reserve0 + a0.toNat < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_r0 ctx w a0 a1
      hpos0 hpos1 hminted hprod h)
  have hadd1 : w.self.reserve1 + a1.toNat < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_r1 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 h)
  have haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_shares ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 h)
  have haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_bal ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS h)
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (addLiquidity_reverts_on_fault0 ctx w a0 a1
        hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_no_cover0 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (addLiquidity_reverts_on_fault1 ctx w a0 a1
        hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 hcov0 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_no_cover1 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 hcov0 hnf1 h)
  exact ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hnf0, hnf1, hcov0, hcov1⟩

/-! ### `removeLiquidity` -/

theorem removeLiquidity_ok (s : Amount SHARE shareScale) (h : RemoveOk w ctx s) :
    Tx.run (removeLiquidity s) ctx w =
      .ok (redeemed w.self s.toNat,
        World.mk (removeLiquidityPost w.self ctx.sender s.toNat)
          (extAfterPush w.ext ctx.self ctx.sender
            (redeemed w.self s.toNat).1 (redeemed w.self s.toNat).2)
          (w.log ++ [.RemoveLiquidity ctx.sender
            (Amount.ofNat (redeemed w.self s.toNat).1)
            (Amount.ofNat (redeemed w.self s.toNat).2) s])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1,
    hnf0, hnf1, hcov0, hcov1⟩
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.toNat).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.toNat).1) :=
    model_transfer hcov0
  have hx1 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.toNat).2]
      w.ext.token1 = some (1, move w.ext.token1 ctx.self ctx.sender (redeemed w.self s.toNat).2) :=
    model_transfer hcov1
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed]
    at hout0 hout1 hle0 hle1 hsLe hx0 hx1 ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hx0]
  simp [hnf1, hx1, extAfterPush, removeLiquidityPost, redeemed]

theorem removeLiquidity_reverts_on_mul0 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares)
    (hmul0 : ¬ s.toNat * w.self.reserve0 < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0]

theorem removeLiquidity_reverts_on_mul1 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : ¬ s.toNat * w.self.reserve1 < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1]

theorem removeLiquidity_reverts_on_zeroOut0 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hout0 : ¬ 0 < (redeemed w.self s.toNat).1) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have hreq : ¬ w.self.totalShares ≤ s.toNat * w.self.reserve0 := by
    intro h
    apply hout0
    simp [redeemed, pos_div_iff]
    exact ⟨hts, h⟩
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1, hreq]

theorem removeLiquidity_reverts_on_zeroOut1 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hout0 : 0 < (redeemed w.self s.toNat).1)
    (hout1 : ¬ 0 < (redeemed w.self s.toNat).2) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have hreq0 : w.self.totalShares ≤ s.toNat * w.self.reserve0 :=
    (pos_div_iff.mp (by simpa [redeemed] using hout0)).2
  have hreq : ¬ w.self.totalShares ≤ s.toNat * w.self.reserve1 := by
    intro h
    apply hout1
    simp [redeemed, pos_div_iff]
    exact ⟨hts, h⟩
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1, hreq0, hreq]

theorem removeLiquidity_reverts_on_fault0 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares) (hsLe : s.toNat ≤ w.self.totalShares)
    (hout0 : 0 < (redeemed w.self s.toNat).1)
    (hout1 : 0 < (redeemed w.self s.toNat).2)
    (hle0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0)
    (hle1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed]
    at hout0 hout1 hle0 hle1 hsLe ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0]

theorem removeLiquidity_reverts_on_no_cover0 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares) (hsLe : s.toNat ≤ w.self.totalShares)
    (hout0 : 0 < (redeemed w.self s.toNat).1)
    (hout1 : 0 < (redeemed w.self s.toNat).2)
    (hle0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0)
    (hle1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : ¬ (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed]
    at hout0 hout1 hle0 hle1 hsLe ⊢
  simp only [redeemed] at hcov0
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, model, hcov0]

theorem removeLiquidity_reverts_on_fault1 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares) (hsLe : s.toNat ≤ w.self.totalShares)
    (hout0 : 0 < (redeemed w.self s.toNat).1)
    (hout1 : 0 < (redeemed w.self s.toNat).2)
    (hle0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0)
    (hle1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.toNat).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.toNat).1) :=
    model_transfer hcov0
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed]
    at hout0 hout1 hle0 hle1 hsLe hx0 ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1]

theorem removeLiquidity_reverts_on_no_cover1 (s : Amount SHARE shareScale)
    (hpos : 0 < s.toNat) (hbal : s.toNat ≤ w.self.shares ctx.sender)
    (hts : 0 < w.self.totalShares) (hsLe : s.toNat ≤ w.self.totalShares)
    (hout0 : 0 < (redeemed w.self s.toNat).1)
    (hout1 : 0 < (redeemed w.self s.toNat).2)
    (hle0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0)
    (hle1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1)
    (hmul0 : s.toNat * w.self.reserve0 < wordBound)
    (hmul1 : s.toNat * w.self.reserve1 < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcov1 : ¬ (redeemed w.self s.toNat).2 ≤ w.ext.token1.balances ctx.self) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.toNat).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.toNat).1) :=
    model_transfer hcov0
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed]
    at hout0 hout1 hle0 hle1 hsLe hx0 ⊢
  simp only [redeemed] at hcov1
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1, model, hcov1]

/-- Success of `removeLiquidity` implies the `RemoveOk` bundle. -/
theorem removeLiquidity_ok_of_run {s : Amount SHARE shareScale} {n : Nat × Nat}
    {w' : World Storage Ext Event}
    (hrun : Tx.run (removeLiquidity s) ctx w = .ok (n, w')) :
    RemoveOk w ctx s := by
  have hpos : 0 < s.toNat := by
    by_contra hp; simp [removeLiquidity, hp] at hrun
  have hbal : s.toNat ≤ w.self.shares ctx.sender := by
    by_contra h
    simp [removeLiquidity, hpos, h] at hrun
  have hts : 0 < w.self.totalShares := by
    by_contra h
    simp [removeLiquidity, hpos, hbal, h] at hrun
  have hmul0 : s.toNat * w.self.reserve0 < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul0 ctx w s hpos hbal hts h)
  have hmul1 : s.toNat * w.self.reserve1 < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul1 ctx w s hpos hbal hts hmul0 h)
  have hout0 : 0 < (redeemed w.self s.toNat).1 := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_zeroOut0 ctx w s
      hpos hbal hts hmul0 hmul1 h)
  have hout1 : 0 < (redeemed w.self s.toNat).2 := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_zeroOut1 ctx w s
      hpos hbal hts hmul0 hmul1 hout0 h)
  have hsLe : s.toNat ≤ w.self.totalShares := by
    by_contra h
    have hreq0 : w.self.totalShares ≤ s.toNat * w.self.reserve0 :=
      (pos_div_iff.mp (by simpa [redeemed] using hout0)).2
    have hreq1 : w.self.totalShares ≤ s.toNat * w.self.reserve1 :=
      (pos_div_iff.mp (by simpa [redeemed] using hout1)).2
    simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1,
      hreq0, hreq1, h] at hrun
  have hle0 : (redeemed w.self s.toNat).1 ≤ w.self.reserve0 :=
    remove_le_reserves s.toNat w.self.reserve0 w.self.totalShares hsLe hts
  have hle1 : (redeemed w.self s.toNat).2 ≤ w.self.reserve1 :=
    remove_le_reserves s.toNat w.self.reserve1 w.self.totalShares hsLe hts
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (removeLiquidity_reverts_on_fault0 ctx w s
        hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_no_cover0 ctx w s
      hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (removeLiquidity_reverts_on_fault1 ctx w s
        hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 hcov0 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov1 : (redeemed w.self s.toNat).2 ≤ w.ext.token1.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_no_cover1 ctx w s
      hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 hcov0 hnf1 h)
  exact ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1, hnf0, hnf1, hcov0, hcov1⟩

/-! ### Swaps -/

theorem run_swapOut (rIn rOut dx : Nat) :
    Tx.run (swapOut rIn rOut dx) ctx w =
      if dx * 9970 < wordBound then
        if rIn + dx * 9970 / 10000 < wordBound then
          if rIn + dx * 9970 / 10000 = 0 then .error (.arith .divByZero)
          else if (dx * 9970 / 10000) * rOut < wordBound then
            .ok ((dx * 9970 / 10000) * rOut / (rIn + dx * 9970 / 10000), w)
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  simp [swapOut]
  by_cases h1 : dx * 9970 < wordBound
  · simp [h1]
    by_cases h2 : rIn + dx * 9970 / 10000 < wordBound <;> simp [h2]
  · simp [h1]

theorem run_swapProto (dx coeff : Nat) :
    Tx.run (swapProto dx coeff) ctx w =
      if dx * 9970 < wordBound then
        if dx * 9970 / 10000 ≤ dx then
          if (dx - dx * 9970 / 10000) * coeff < wordBound then
            .ok ((dx - dx * 9970 / 10000) * coeff / 10000, w)
          else .error (.arith .overflow)
        else .error (.arith .underflow)
      else .error (.arith .overflow) := by
  simp [swapProto]
  by_cases h1 : dx * 9970 < wordBound
  · simp [h1]
    by_cases h2 : dx * 9970 / 10000 ≤ dx <;> simp [h2]
  · simp [h1]

private theorem swap0_out_le (w : World Storage Ext Event)
    (dx : Amount TOKEN0 scale0) (h0 : 0 < w.self.reserve0) :
    amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤ w.self.reserve1 :=
  remove_le_reserves (dxFeeLess dx.toNat) w.self.reserve1
    (w.self.reserve0 + dxFeeLess dx.toNat) (Nat.le_add_left _ _)
    (Nat.add_pos_left h0 _)

private theorem swap1_out_le (w : World Storage Ext Event)
    (dx : Amount TOKEN1 scale1) (h1 : 0 < w.self.reserve1) :
    amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤ w.self.reserve0 :=
  remove_le_reserves (dxFeeLess dx.toNat) w.self.reserve0
    (w.self.reserve1 + dxFeeLess dx.toNat) (Nat.le_add_left _ _)
    (Nat.add_pos_left h1 _)

set_option maxHeartbeats 400000 in
theorem swap0for1_ok (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    (h : Swap0Ok w ctx dx minOut) :
    Tx.run (swap0for1 dx minOut) ctx w =
      .ok (amountOut w.self.reserve0 w.self.reserve1 dx.toNat,
        World.mk (swap0Post w.self dx.toNat (protoOf w.self dx.toNat)
            (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))
          (extAfterSwap0 w.ext ctx.sender ctx.self dx.toNat
            (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))
          (w.log ++ [.Swap0for1 ctx.sender dx
            (Amount.ofNat (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hdxF, hden, houtm, hmin, hout, hpmul, htaken, hadd, hacc,
    hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.toNat] w.ext.token0 =
      some (1, move w.ext.token0 ctx.sender ctx.self dx.toNat) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve0 w.self.reserve1 dx.toNat] w.ext.token1 =
      some (1, move w.ext.token1 ctx.self ctx.sender
        (amountOut w.self.reserve0 w.self.reserve1 dx.toNat)) :=
    model_transfer hcovOut
  have hout_le := swap0_out_le w dx hr0
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  have hdxFle := dxFeeLess_le dx.toNat
  simp only [amountOut, amountOutF] at hmin hout hout_le houtm hden hxOut
  have hout' := pos_div_iff.mp hout
  simp only [dxFeeLess_lit] at hmin hout hout_le houtm hden hout' hxOut hdxFle
  have hden0 : w.self.reserve0 + dx.toNat * 9970 / 10000 ≠ 0 := Nat.ne_of_gt hout'.1
  simp [protoOf, protoTake, coeffOf, swapFee, dxFeeLess_lit, BPS] at hpmul htaken hadd
  by_cases hft : w.self.feeTo = 0
  · have hadd' : w.self.reserve0 + dx.toNat < wordBound := by
      simpa [hft, Nat.sub_zero] using hadd
    simp only [swap0for1, run_swapOut, Tx.run_bind, Tx.run_require, Tx.run_load,
      Tx.run_sender, Tx.run_selfAddress, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm,
      hmin, hout, hout_le, hft, hadd']
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
    simp [extAfterSwap0, swap0Post, protoOf, protoTake, hft, Nat.add_zero, Nat.sub_zero,
      amountOut, amountOutF, dxFeeLess_lit]
  · have hacc' := hacc hft
    have hpmul' : (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps < wordBound := by
      simpa [coeffOf, swapFee, dxFeeLess_lit, if_neg hft] using hpmul
    have htaken' : (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000 ≤
        dx.toNat := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using htaken
    have hadd' : w.self.reserve0 +
        (dx.toNat - (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000) <
          wordBound := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using hadd
    have hacc'' : w.self.protocolFees0 +
        (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000 < wordBound := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using hacc'
    simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft]
    simp [run_swapProto, hdxF, hdxFle, hpmul', htaken', hadd', hacc'', hout_le]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
    simp [extAfterSwap0, swap0Post, protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft,
      amountOut, amountOutF]

set_option maxHeartbeats 400000 in
theorem swap1for0_ok (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    (h : Swap1Ok w ctx dx minOut) :
    Tx.run (swap1for0 dx minOut) ctx w =
      .ok (amountOut w.self.reserve1 w.self.reserve0 dx.toNat,
        World.mk (swap1Post w.self dx.toNat (protoOf w.self dx.toNat)
            (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))
          (extAfterSwap1 w.ext ctx.sender ctx.self dx.toNat
            (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))
          (w.log ++ [.Swap1for0 ctx.sender dx
            (Amount.ofNat (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hdxF, hden, houtm, hmin, hout, hpmul, htaken, hadd, hacc,
    hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.toNat] w.ext.token1 =
      some (1, move w.ext.token1 ctx.sender ctx.self dx.toNat) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve1 w.self.reserve0 dx.toNat] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self ctx.sender
        (amountOut w.self.reserve1 w.self.reserve0 dx.toNat)) :=
    model_transfer hcovOut
  have hout_le := swap1_out_le w dx hr1
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  have hdxFle := dxFeeLess_le dx.toNat
  simp only [amountOut, amountOutF] at hmin hout hout_le houtm hden hxOut
  have hout' := pos_div_iff.mp hout
  simp only [dxFeeLess_lit] at hmin hout hout_le houtm hden hout' hxOut hdxFle
  have hden0 : w.self.reserve1 + dx.toNat * 9970 / 10000 ≠ 0 := Nat.ne_of_gt hout'.1
  simp [protoOf, protoTake, coeffOf, swapFee, dxFeeLess_lit, BPS] at hpmul htaken hadd
  by_cases hft : w.self.feeTo = 0
  · have hadd' : w.self.reserve1 + dx.toNat < wordBound := by
      simpa [hft, Nat.sub_zero] using hadd
    simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hden, hden0, houtm, hmin, hout,
      hout'.1, hout'.2, hout_le, hft, hadd']
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
    simp [extAfterSwap1, swap1Post, protoOf, protoTake, hft, Nat.add_zero, Nat.sub_zero,
      amountOut, amountOutF, dxFeeLess_lit]
  · have hacc' := hacc hft
    have hpmul' : (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps < wordBound := by
      simpa [coeffOf, swapFee, dxFeeLess_lit, if_neg hft] using hpmul
    have htaken' : (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000 ≤
        dx.toNat := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using htaken
    have hadd' : w.self.reserve1 +
        (dx.toNat - (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000) <
          wordBound := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using hadd
    have hacc'' : w.self.protocolFees1 +
        (dx.toNat - dx.toNat * 9970 / 10000) * w.self.protocolShareBps / 10000 < wordBound := by
      simpa [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] using hacc'
    simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hden, hden0, houtm, hmin, hout, hft]
    simp [run_swapProto, hdxF, hdxFle, hpmul', htaken', hadd', hacc'', hout_le]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
    simp [extAfterSwap1, swap1Post, protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft,
      amountOut, amountOutF]

set_option maxHeartbeats 2000000 in
theorem swap0for1_ok_of_run {dx : Amount TOKEN0 scale0} {minOut : Amount TOKEN1 scale1}
    {n : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (n, w')) :
    Swap0Ok w ctx dx minOut := by
  have hpos : 0 < dx.toNat := by
    by_contra hp; simp [swap0for1, run_swapOut, run_swapProto, hp] at hrun
  have hr0 : 0 < w.self.reserve0 := by
    by_contra h; simp [swap0for1, run_swapOut, run_swapProto, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1 := by
    by_contra h; simp [swap0for1, run_swapOut, run_swapProto, hpos, hr0, h] at hrun
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  have hdxF : dx.toNat * 9970 < wordBound := by
    by_contra h; simp [swap0for1, run_swapOut, run_swapProto, hpos, hr0, hr0n, hr1, h] at hrun
  have hdxFle := dxFeeLess_le dx.toNat
  have hden0 : w.self.reserve0 + dxFeeLess dx.toNat ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left hr0 _)
  simp only [dxFeeLess_lit] at hden0
  have hden : w.self.reserve0 + dxFeeLess dx.toNat < wordBound := by
    by_contra h
    simp only [dxFeeLess_lit] at h
    simp [swap0for1, run_swapOut, run_swapProto, dxFeeLess_lit, hpos, hr0, hr0n, hr1, hdxF, hdxFle, hden0, h] at hrun
  have houtm : dxFeeLess dx.toNat * w.self.reserve1 < wordBound := by
    by_contra h
    simp only [dxFeeLess_lit] at h
    simp [swap0for1, run_swapOut, run_swapProto, dxFeeLess_lit, hpos, hr0, hr0n, hr1, hdxF, hdxFle, hden0, hden, h] at hrun
  have hdenLit : w.self.reserve0 + dx.toNat * 9970 / 10000 < wordBound := by
    simpa [dxFeeLess_lit] using hden
  have houtmLit : dx.toNat * 9970 / 10000 * w.self.reserve1 < wordBound := by
    simpa [dxFeeLess_lit] using houtm
  have hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat := by
    by_contra h
    simp only [amountOut, amountOutF, dxFeeLess_lit] at h
    simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit] at hrun
    simp [h] at hrun
  have hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat := by
    by_contra h
    simp only [amountOut, amountOutF, dxFeeLess_lit] at h
    simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit, hmin] at hrun
    simp [h] at hrun
  have hout_amt : 0 < amountOutF w.self.reserve0 w.self.reserve1 dx.toNat := by
    simpa only [amountOut] using hout
  have hout' := pos_div_iff.mp hout_amt
  have hout_le := swap0_out_le w dx hr0
  have hpmul : swapFee dx.toNat * coeffOf w.self < wordBound := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [coeffOf, swapFee, dxFeeLess_lit, hft] at h
    · simp only [coeffOf, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, h] at hrun
  have htaken : protoOf w.self dx.toNat ≤ dx.toNat := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [protoOf, protoTake, hft] at h
    · simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, h] at hrun
  have hadd : w.self.reserve0 + (dx.toNat - protoOf w.self dx.toNat) < wordBound := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp only [protoOf, protoTake, if_pos hft, Nat.sub_zero] at h
      simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft, h] at hrun
    · simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, h] at hrun
  have hacc : w.self.feeTo ≠ 0 →
      w.self.protocolFees0 + protoOf w.self dx.toNat < wordBound := by
    intro hft
    by_contra h
    simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
    simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
    simp [run_swapProto, hdxF, hdxFle, h] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · by_cases hft : w.self.feeTo = 0
      · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle, hf] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token0B, IERC20.model_eq, hf] at hrun
      · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle, hf] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token0B, IERC20.model_eq, hf] at hrun
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token0B, IERC20.model_eq, hnf0, model, h] at hrun
    · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token0B, IERC20.model_eq, hnf0, model, h] at hrun
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
        (amt := dx.toNat) (callee := ctx.self) hcovIn
      by_cases hft : w.self.feeTo = 0
      · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token0B, IERC20.model_eq, hnf0, hxIn, token1B, hf] at hrun
      · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token0B, IERC20.model_eq, hnf0, hxIn, token1B, hf] at hrun
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
      w.ext.token1.balances ctx.self := by
    by_contra h
    have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.toNat) (callee := ctx.self) hcovIn
    by_cases hft : w.self.feeTo = 0
    · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token0B, IERC20.model_eq, hnf0, hxIn, token1B, IERC20.model_eq, hnf1, model, h] at hrun
    · simp [swap0for1, run_swapOut, hpos, hr0, hr1, hr0n, hdxF, hden, hden0, houtm, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token0B, IERC20.model_eq, hnf0, hxIn, token1B, IERC20.model_eq, hnf1, model, h] at hrun
  exact ⟨hpos, hr0, hr1, hdxF, hden, houtm, hmin, hout, hpmul, htaken, hadd, hacc,
    hnf0, hnf1, hcovIn, hcovOut⟩

set_option maxHeartbeats 2000000 in
theorem swap1for0_ok_of_run {dx : Amount TOKEN1 scale1} {minOut : Amount TOKEN0 scale0}
    {n : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (n, w')) :
    Swap1Ok w ctx dx minOut := by
  have hpos : 0 < dx.toNat := by
    by_contra hp; simp [swap1for0, run_swapOut, run_swapProto, hp] at hrun
  have hr0 : 0 < w.self.reserve0 := by
    by_contra h; simp [swap1for0, run_swapOut, run_swapProto, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1 := by
    by_contra h; simp [swap1for0, run_swapOut, run_swapProto, hpos, hr0, h] at hrun
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  have hdxF : dx.toNat * 9970 < wordBound := by
    by_contra h; simp [swap1for0, run_swapOut, run_swapProto, hpos, hr0, hr1, hr1n, h] at hrun
  have hdxFle := dxFeeLess_le dx.toNat
  have hden0 : w.self.reserve1 + dxFeeLess dx.toNat ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left hr1 _)
  simp only [dxFeeLess_lit] at hden0
  have hden : w.self.reserve1 + dxFeeLess dx.toNat < wordBound := by
    by_contra h
    simp only [dxFeeLess_lit] at h
    simp [swap1for0, run_swapOut, run_swapProto, dxFeeLess_lit, hpos, hr0, hr1, hr1n, hdxF, hdxFle, hden0, h] at hrun
  have houtm : dxFeeLess dx.toNat * w.self.reserve0 < wordBound := by
    by_contra h
    simp only [dxFeeLess_lit] at h
    simp [swap1for0, run_swapOut, run_swapProto, dxFeeLess_lit, hpos, hr0, hr1, hr1n, hdxF, hdxFle, hden0, hden, h] at hrun
  have hdenLit : w.self.reserve1 + dx.toNat * 9970 / 10000 < wordBound := by
    simpa [dxFeeLess_lit] using hden
  have houtmLit : dx.toNat * 9970 / 10000 * w.self.reserve0 < wordBound := by
    simpa [dxFeeLess_lit] using houtm
  have hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat := by
    by_contra h
    simp only [amountOut, amountOutF, dxFeeLess_lit] at h
    simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit] at hrun
    simp [h] at hrun
  have hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat := by
    by_contra h
    simp only [amountOut, amountOutF, dxFeeLess_lit] at h
    simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin] at hrun
    simp [h] at hrun
  have hout_amt : 0 < amountOutF w.self.reserve1 w.self.reserve0 dx.toNat := by
    simpa only [amountOut] using hout
  have hout' := pos_div_iff.mp hout_amt
  have hout_le := swap1_out_le w dx hr1
  have hpmul : swapFee dx.toNat * coeffOf w.self < wordBound := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [coeffOf, swapFee, dxFeeLess_lit, hft] at h
    · simp only [coeffOf, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, h] at hrun
  have htaken : protoOf w.self dx.toNat ≤ dx.toNat := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [protoOf, protoTake, hft] at h
    · simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, h] at hrun
  have hadd : w.self.reserve1 + (dx.toNat - protoOf w.self dx.toNat) < wordBound := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp only [protoOf, protoTake, if_pos hft, Nat.sub_zero] at h
      simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, h] at hrun
    · simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
      simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, h] at hrun
  have hacc : w.self.feeTo ≠ 0 →
      w.self.protocolFees1 + protoOf w.self dx.toNat < wordBound := by
    intro hft
    by_contra h
    simp only [protoOf, protoTake, swapFee, dxFeeLess_lit, if_neg hft] at h
    simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
    simp [run_swapProto, hdxF, hdxFle, h] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · by_cases hft : w.self.feeTo = 0
      · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token1B, IERC20.model_eq, hf] at hrun
      · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token1B, IERC20.model_eq, hf] at hrun
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender := by
    by_contra h
    by_cases hft : w.self.feeTo = 0
    · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token1B, IERC20.model_eq, hnf0, model, h] at hrun
    · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token1B, IERC20.model_eq, hnf0, model, h] at hrun
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
        (amt := dx.toNat) (callee := ctx.self) hcovIn
      by_cases hft : w.self.feeTo = 0
      · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token1B, IERC20.model_eq, hnf0, hxIn, token0B, hf] at hrun
      · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
        simp [run_swapProto, hdxF, hdxFle] at hrun
        unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
        simp [token1B, IERC20.model_eq, hnf0, hxIn, token0B, hf] at hrun
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
      w.ext.token0.balances ctx.self := by
    by_contra h
    have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.toNat) (callee := ctx.self) hcovIn
    by_cases hft : w.self.feeTo = 0
    · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token1B, IERC20.model_eq, hnf0, hxIn, token0B, IERC20.model_eq, hnf1, model, h] at hrun
    · simp [swap1for0, run_swapOut, hpos, hr0, hr1, hr1n, hdxF, hdenLit, hden0, houtmLit, hmin, hout, hft] at hrun
      simp [run_swapProto, hdxF, hdxFle,
        hft, hpmul, htaken, hadd, hacc] at hrun
      unfold Tx.call at hrun; dsimp only [Tx.run] at hrun
      simp [token1B, IERC20.model_eq, hnf0, hxIn, token0B, IERC20.model_eq, hnf1, model, h] at hrun
  exact ⟨hpos, hr0, hr1, hdxF, hden, houtm, hmin, hout, hpmul, htaken, hadd, hacc,
    hnf0, hnf1, hcovIn, hcovOut⟩

/-! ### Share-support preservation -/

theorem invStorage_of_addLiquidityPost (σ : Storage) (who : Address) (a0 a1 : Nat)
    (hInv : InvStorage σ) :
    InvStorage (addLiquidityPost σ who a0 a1) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  let n := mintedShares σ a0 a1
  by_cases ht : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ who := by intro h; subst h; exact ha ht
      simp [addLiquidityPost, Function.update_of_ne hne]
      exact h0 a ha
    · have hupd := sum_update_mem H σ.shares ht (n + σ.shares who)
      have hcancel :
          H.sum (Function.update σ.shares who (n + σ.shares who)) =
            H.sum σ.shares + n := by
        revert hupd
        generalize hS' : H.sum (Function.update σ.shares who (n + σ.shares who)) = S'
        generalize hS : H.sum σ.shares = S
        generalize hd : σ.shares who = d
        intro hupd
        omega
      simpa [addLiquidityPost, hcancel, hsum, n] using Nat.add_comm σ.totalShares n
  · refine ⟨insert who H, ?_, ?_⟩
    · intro a ha
      have hat : a ≠ who := by
        intro h; subst h; exact ha (Finset.mem_insert_self _ _)
      have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
      simp [addLiquidityPost, Function.update_of_ne hat]
      exact h0 a haH
    · have hframe := sum_update_not_mem H σ.shares ht (n + σ.shares who)
      have hb0 : σ.shares who = 0 := h0 who ht
      have hsum' :
          (∑ a ∈ insert who H, (addLiquidityPost σ who a0 a1).shares a) =
            H.sum σ.shares + n := by
        rw [Finset.sum_insert ht]
        simp only [addLiquidityPost, Function.update_self]
        rw [show mintedShares σ a0 a1 + σ.shares who = n + σ.shares who by simp [n]]
        rw [hframe, hb0]
        omega
      change (∑ a ∈ insert who H, (addLiquidityPost σ who a0 a1).shares a) =
        (addLiquidityPost σ who a0 a1).totalShares
      simpa [addLiquidityPost, n] using (hsum'.trans (by rw [hsum])).trans (Nat.add_comm _ _)

theorem invStorage_of_removeLiquidityPost (σ : Storage) (who : Address) (s : Nat)
    (hInv : InvStorage σ) (hn : s ≤ σ.shares who) :
    InvStorage (removeLiquidityPost σ who s) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hs : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ who := by intro h; subst h; exact ha hs
      simp [removeLiquidityPost, Function.update_of_ne ha_src]
      exact h0 a ha
    · have hs1 := sum_update_mem H σ.shares hs (σ.shares who - s)
      have hsumd :
          H.sum (Function.update σ.shares who (σ.shares who - s)) =
            H.sum σ.shares - s := by omega
      change (∑ a ∈ H, (removeLiquidityPost σ who s).shares a) =
        (removeLiquidityPost σ who s).totalShares
      simpa [removeLiquidityPost] using hsumd.trans (by rw [hsum])
  · have hb0 : σ.shares who = 0 := h0 who hs
    have hn0 : s = 0 := Nat.eq_zero_of_le_zero (hn.trans_eq hb0)
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp [removeLiquidityPost, hn0, Function.update_eq_self]
      exact h0 a ha
    · simp [removeLiquidityPost, hn0, Function.update_eq_self, hsum]


namespace Proof

/-- Successful `swap0for1` does not decrease `reserve0 · reserve1`. The protocol
share of the swap fee is at most 100%, so the protocol take never exceeds the
fee and the input reserve grows by at least the fee-less notional `dxF`. -/
theorem swap0for1_k (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0 * w'.self.reserve1 ≥ w.self.reserve0 * w.self.reserve1 := by
  have hok := swap0for1_ok_of_run ctx w h
  have hrun := swap0for1_ok ctx w dx minOut hok
  cases h.symm.trans hrun
  simp [swap0Post, protoOf, amountOut]
  simpa [swapQuote, protoOf, amountOut] using
    swapQuote_k w.self.reserve0 w.self.reserve1 dx.toNat
      w.self.feeTo w.self.protocolShareBps hok.r0 hps

/-- Successful `swap1for0` does not decrease `reserve0 · reserve1`. Same protocol-share
bound as `swap0for1_k`. -/
theorem swap1for0_k (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0 * w'.self.reserve1 ≥ w.self.reserve0 * w.self.reserve1 := by
  have hok := swap1for0_ok_of_run ctx w h
  have hrun := swap1for0_ok ctx w dx minOut hok
  cases h.symm.trans hrun
  simp [swap1Post, protoOf, amountOut]
  have hk := swapQuote_k w.self.reserve1 w.self.reserve0 dx.toNat
    w.self.feeTo w.self.protocolShareBps hok.r1 hps
  simpa [swapQuote, protoOf, amountOut, Nat.mul_comm] using hk

/-- On a successful `swap0for1`, the token0 protocol bucket grows by exactly the
protocol take and the token1 bucket is unchanged. -/
theorem swap0_protocol_fee (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 + protoOf w.self dx.toNat ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := swap0for1_ok_of_run ctx w h
  have hrun := swap0for1_ok ctx w dx minOut hok
  cases h.symm.trans hrun
  simp [swap0Post]

/-- On a successful `swap1for0`, the token1 protocol bucket grows by exactly the
protocol take and the token0 bucket is unchanged. -/
theorem swap1_protocol_fee (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    {out : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees1 = w.self.protocolFees1 + protoOf w.self dx.toNat ∧
      w'.self.protocolFees0 = w.self.protocolFees0 := by
  have hok := swap1for0_ok_of_run ctx w h
  have hrun := swap1for0_ok ctx w dx minOut hok
  cases h.symm.trans hrun
  simp [swap1Post]

/-- Success of `collectProtocolFees` means the caller is `feeTo`, both protocol
buckets are zeroed, and the curve reserves are unchanged. -/
theorem collect_only_feeTo {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    ctx.sender = w.self.feeTo ∧
      w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 := by
  have hok := collectProtocolFees_ok_of_run ctx w h
  have hrun := collectProtocolFees_ok ctx w hok
  cases h.symm.trans hrun
  exact ⟨hok.who, rfl, rfl, rfl, rfl⟩

theorem addLiquidity_buckets (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
    {n : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := addLiquidity_ok_of_run ctx w h
  have hrun := addLiquidity_ok ctx w a0 a1 hok
  cases h.symm.trans hrun
  simp [addLiquidityPost]

theorem removeLiquidity_buckets (s : Amount SHARE shareScale)
    {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := removeLiquidity_ok_of_run ctx w h
  have hrun := removeLiquidity_ok ctx w s hok
  cases h.symm.trans hrun
  simp [removeLiquidityPost]

theorem setProtocolShare_buckets (bps : Nat) {w' : World Storage Ext Event}
    (h : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  obtain ⟨_, _, rfl⟩ := setProtocolShare_ok_of_run ctx w h
  simp

theorem setFeeTo_buckets (recipient : Address) {w' : World Storage Ext Event}
    (h : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run ctx w h
  simp

/-- A successful `removeLiquidity s` pays `⌊s · reserve_i / totalShares⌋` of each token. -/
theorem removeLiquidity_pro_rata (s : Amount SHARE shareScale)
    {p : Nat × Nat} {w' : World Storage Ext Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p.1 = s.toNat * w.self.reserve0 / w.self.totalShares ∧
      p.2 = s.toNat * w.self.reserve1 / w.self.totalShares := by
  have hok := removeLiquidity_ok_of_run ctx w h
  have hrun := removeLiquidity_ok ctx w s hok
  cases h.symm.trans hrun
  simp [redeemed]

end Proof

end Cpamm
