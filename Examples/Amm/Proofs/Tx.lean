import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Examples.Amm.Spec
import Examples.Amm.Contract
import Stdlib.SafeERC20

set_option linter.unusedSimpArgs false

/-!
# Amm — functional lemmas

`Tx.run` statements. Amounts are asset-indexed; helpers project `.raw`.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

attribute [local simp] Amount.eq_iff Amount.ne_iff Amount.lt_iff Amount.le_iff

namespace Amm

variable (ctx : Ctx) (w : World Storage Ext Event)

/-! ### Pure arithmetic (rounding toward the pool, `k` monotone on swaps) -/

/-- `⌊s * r / S⌋ ≤ r` when `s ≤ S`. -/
theorem remove_le_reserves (s r S : Nat) (hs : s ≤ S) (hS : 0 < S) :
    s * r / S ≤ r := by
  have hmul : s * r ≤ S * r := Nat.mul_le_mul_right r hs
  have hdiv : s * r / S ≤ S * r / S := Nat.div_le_div_right hmul
  simpa [Nat.mul_div_right r hS] using hdiv

/-- Same as `remove_le_reserves` with the product swapped. -/
theorem remove_le_reserves_comm (s r S : Nat) (hs : s ≤ S) (hS : 0 < S) :
    r * s / S ≤ r := by
  simpa [Nat.mul_comm] using remove_le_reserves s r S hs hS

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

/-- Uniswap-style floor output: `k' ≥ k`. -/
theorem k_nondecreasing (rIn rOut dx : Nat) (hIn : 0 < rIn) :
    (rIn + dx) * (rOut - rOut * dx / (rIn + dx)) ≥ rIn * rOut := by
  set den := rIn + dx
  have hden : 0 < den := Nat.add_pos_left hIn dx
  have hout : rOut * dx / den ≤ rOut :=
    remove_le_reserves_comm dx rOut den (Nat.le_add_left dx rIn) hden
  have hchop : den * (rOut * dx / den) ≤ rOut * dx := Nat.mul_div_le (rOut * dx) den
  have hdistrib : den * (rOut - rOut * dx / den) = den * rOut - den * (rOut * dx / den) :=
    Nat.mul_sub_left_distrib den rOut (rOut * dx / den)
  have hge : den * rOut - den * (rOut * dx / den) ≥ den * rOut - rOut * dx :=
    Nat.sub_le_sub_left hchop _
  have hk : den * rOut - rOut * dx = rIn * rOut := by
    simp [den, Nat.add_mul, Nat.mul_comm dx]
  omega

theorem k_nondecreasing_0for1 (r0 r1 dx : Nat) (h0 : 0 < r0) :
    (r0 + dx) * (r1 - r1 * dx / (r0 + dx)) ≥ r0 * r1 :=
  k_nondecreasing r0 r1 dx h0

theorem k_nondecreasing_1for0 (r0 r1 dx : Nat) (h1 : 0 < r1) :
    (r1 + dx) * (r0 - r0 * dx / (r1 + dx)) ≥ r0 * r1 := by
  simpa [Nat.mul_comm r0 r1] using k_nondecreasing r1 r0 dx h1

/-! ### Share accounting -/

theorem shares_conserved (σ : Storage) (h : InvStorage σ) : InvStorage σ := h

/-! ### Post-states -/

def mintedShares (σ : Storage) (a0 a1 : Nat) : Nat :=
  if σ.totalShares.raw = 0 then a0
  else if σ.totalShares.raw * a0 / σ.reserve0.raw ≤
      σ.totalShares.raw * a1 / σ.reserve1.raw then
    σ.totalShares.raw * a0 / σ.reserve0.raw
  else
    σ.totalShares.raw * a1 / σ.reserve1.raw

private theorem not_side0 {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares.raw ≠ 0) (hr0 : 0 < σ.reserve0.raw)
    (hle : σ.totalShares.raw * a0 / σ.reserve0.raw ≤
        σ.totalShares.raw * a1 / σ.reserve1.raw)
    (hminted : ¬ 0 < mintedShares σ a0 a1) :
    ¬ σ.reserve0.raw ≤ σ.totalShares.raw * a0 := by
  intro h
  refine hminted ?_
  simp [mintedShares, hts, hle, pos_div_iff]
  exact ⟨hr0, h⟩

private theorem not_side1 {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares.raw ≠ 0) (hr1 : 0 < σ.reserve1.raw)
    (hle : ¬ σ.totalShares.raw * a0 / σ.reserve0.raw ≤
        σ.totalShares.raw * a1 / σ.reserve1.raw)
    (hminted : ¬ 0 < mintedShares σ a0 a1) :
    ¬ σ.reserve1.raw ≤ σ.totalShares.raw * a1 := by
  intro h
  refine hminted ?_
  simp [mintedShares, hts, hle, pos_div_iff]
  exact ⟨hr1, h⟩

def addLiquidityPost (σ : Storage) (who : Address) (a0 a1 : Nat) : Storage :=
  let n := mintedShares σ a0 a1
  { σ with
    reserve0 := σ.reserve0 + Amount.ofWord a0
    reserve1 := σ.reserve1 + Amount.ofWord a1
    totalShares := Amount.ofWord n + σ.totalShares
    shares := Function.update σ.shares who (Amount.ofWord n + σ.shares who) }

def redeemed (σ : Storage) (s : Nat) : Nat × Nat :=
  (σ.reserve0.raw * s / σ.totalShares.raw, σ.reserve1.raw * s / σ.totalShares.raw)

def removeLiquidityPost (σ : Storage) (who : Address) (s : Nat) : Storage :=
  let out := redeemed σ s
  { σ with
    reserve0 := σ.reserve0 - Amount.ofWord out.1
    reserve1 := σ.reserve1 - Amount.ofWord out.2
    totalShares := σ.totalShares - Amount.ofWord s
    shares := Function.update σ.shares who (σ.shares who - Amount.ofWord s) }

def swap0Post (σ : Storage) (dx out : Nat) : Storage :=
  { σ with
    reserve0 := σ.reserve0 + Amount.ofWord dx
    reserve1 := σ.reserve1 - Amount.ofWord out }

def swap1Post (σ : Storage) (dx out : Nat) : Storage :=
  { σ with
    reserve1 := σ.reserve1 + Amount.ofWord dx
    reserve0 := σ.reserve0 - Amount.ofWord out }

def amountOut (rIn rOut dx : Nat) : Nat :=
  rOut * dx / (rIn + dx)

theorem amountOut_comm (rIn rOut dx : Nat) :
    amountOut rIn rOut dx = dx * rOut / (rIn + dx) := by
  simp [amountOut, Nat.mul_comm rOut]

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
    (hS : 0 < σ.totalShares.raw) (hr0 : 0 < σ.reserve0.raw) :
    mintedShares σ a0 a1 * σ.reserve0.raw / σ.totalShares.raw ≤ a0 := by
  have hne : σ.totalShares.raw ≠ 0 := Nat.ne_of_gt hS
  have hmin : mintedShares σ a0 a1 ≤ a0 * σ.totalShares.raw / σ.reserve0.raw := by
    unfold mintedShares
    rw [if_neg hne]
    rw [Nat.mul_comm a0]
    split_ifs with h
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_not_le h)
  have hfav := lp_round_favors_pool a0 σ.reserve0.raw σ.totalShares.raw hr0 hS
  have hmono : mintedShares σ a0 a1 * σ.reserve0.raw / σ.totalShares.raw ≤
      (a0 * σ.totalShares.raw / σ.reserve0.raw) * σ.reserve0.raw / σ.totalShares.raw :=
    Nat.div_le_div_right (Nat.mul_le_mul_right σ.reserve0.raw hmin)
  exact Nat.le_trans hmono hfav

theorem minted_le_side1 (σ : Storage) (a0 a1 : Nat)
    (hS : 0 < σ.totalShares.raw) (hr1 : 0 < σ.reserve1.raw) :
    mintedShares σ a0 a1 * σ.reserve1.raw / σ.totalShares.raw ≤ a1 := by
  have hne : σ.totalShares.raw ≠ 0 := Nat.ne_of_gt hS
  have hmin : mintedShares σ a0 a1 ≤ a1 * σ.totalShares.raw / σ.reserve1.raw := by
    unfold mintedShares
    rw [if_neg hne]
    rw [Nat.mul_comm a1]
    split_ifs with h
    · exact h
    · exact Nat.le_refl _
  have hfav := lp_round_favors_pool a1 σ.reserve1.raw σ.totalShares.raw hr1 hS
  have hmono : mintedShares σ a0 a1 * σ.reserve1.raw / σ.totalShares.raw ≤
      (a1 * σ.totalShares.raw / σ.reserve1.raw) * σ.reserve1.raw / σ.totalShares.raw :=
    Nat.div_le_div_right (Nat.mul_le_mul_right σ.reserve1.raw hmin)
  exact Nat.le_trans hmono hfav

/-! ### Success bundles -/

structure AddLiqOk (w : World Storage Ext Event) (ctx : Ctx)
    (a0 : Amount token0) (a1 : Amount token1) : Prop where
  pos0 : 0 < a0.raw
  pos1 : 0 < a1.raw
  minted : 0 < mintedShares w.self a0.raw a1.raw
  prod :
    w.self.totalShares.raw = 0 ∨
      (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
        w.self.totalShares.raw * a0.raw < wordBound ∧
        w.self.totalShares.raw * a1.raw < wordBound)
  add0 : w.self.reserve0.raw + a0.raw < wordBound
  add1 : w.self.reserve1.raw + a1.raw < wordBound
  addS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound
  addB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  cov0 : a0.raw ≤ w.ext.token0.balances ctx.sender
  cov1 : a1.raw ≤ w.ext.token1.balances ctx.sender

structure RemoveOk (w : World Storage Ext Event) (ctx : Ctx)
    (s : Amount lpShare) : Prop where
  pos : 0 < s.raw
  bal : s.raw ≤ (w.self.shares ctx.sender).raw
  ts : 0 < w.self.totalShares.raw
  sLe : s.raw ≤ w.self.totalShares.raw
  out0 : 0 < (redeemed w.self s.raw).1
  out1 : 0 < (redeemed w.self s.raw).2
  le0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw
  le1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw
  mul0 : w.self.reserve0.raw * s.raw < wordBound
  mul1 : w.self.reserve1.raw * s.raw < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  cov0 : (redeemed w.self s.raw).1 ≤ w.ext.token0.balances ctx.self
  cov1 : (redeemed w.self s.raw).2 ≤ w.ext.token1.balances ctx.self

structure Swap0Ok (w : World Storage Ext Event) (ctx : Ctx)
    (dx : Amount token0) (minOut : Amount token1) : Prop where
  pos : 0 < dx.raw
  r0 : 0 < w.self.reserve0.raw
  r1 : 0 < w.self.reserve1.raw
  den : w.self.reserve0.raw + dx.raw < wordBound
  mul : w.self.reserve1.raw * dx.raw < wordBound
  min : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw
  out : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw
  add : w.self.reserve0.raw + dx.raw < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  covIn : dx.raw ≤ w.ext.token0.balances ctx.sender
  covOut : amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw ≤
    w.ext.token1.balances ctx.self

structure Swap1Ok (w : World Storage Ext Event) (ctx : Ctx)
    (dx : Amount token1) (minOut : Amount token0) : Prop where
  pos : 0 < dx.raw
  r0 : 0 < w.self.reserve0.raw
  r1 : 0 < w.self.reserve1.raw
  den : w.self.reserve1.raw + dx.raw < wordBound
  mul : w.self.reserve0.raw * dx.raw < wordBound
  min : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw
  out : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw
  add : w.self.reserve1.raw + dx.raw < wordBound
  nf0 : w.faults w.ncalls = false
  nf1 : w.faults (w.ncalls + 1) = false
  covIn : dx.raw ≤ w.ext.token1.balances ctx.sender
  covOut : amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw ≤
    w.ext.token0.balances ctx.self

/-! ### Views -/

theorem getReserves_ok :
    Tx.run getReserves ctx w = .ok ((w.self.reserve0, w.self.reserve1), w) := by
  simp [getReserves]

theorem sharesOf_ok (who : Address) :
    Tx.run (sharesOf who) ctx w = .ok (w.self.shares who, w) := by
  simp [sharesOf]

theorem quote0for1_ok (dx : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : w.self.reserve1.raw * dx.raw < wordBound) :
    Tx.run (quote0for1 dx) ctx w =
      .ok (Amount.ofWord (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw), w) := by
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, amountOut, hpos, hr0, hr0n, hden, hmul]

theorem quote0for1_reverts_on_add (dx : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw)
    (hden : ¬ w.self.reserve0.raw + dx.raw < wordBound) :
    Tx.run (quote0for1 dx) ctx w = .error (.arith .overflow) := by
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, hpos, hr0, hr0n, hden]

theorem quote0for1_reverts_on_mul (dx : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : ¬ w.self.reserve1.raw * dx.raw < wordBound) :
    Tx.run (quote0for1 dx) ctx w = .error (.arith .overflow) := by
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, hpos, hr0, hr0n, hden, hmul]

theorem quote0for1_same_world {dx : Amount token0} {n : Amount token1}
    {w' : World Storage Ext Event}
    (hrun : Tx.run (quote0for1 dx) ctx w = .ok (n, w')) : w' = w := by
  have hpos : 0 < dx.raw := by
    by_contra hp; simp [quote0for1, hp] at hrun
  have hr0 : 0 < w.self.reserve0.raw := by
    by_contra h; simp [quote0for1, hpos, h] at hrun
  have hden : w.self.reserve0.raw + dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (quote0for1_reverts_on_add ctx w dx hpos hr0 h)
  have hmul : w.self.reserve1.raw * dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (quote0for1_reverts_on_mul ctx w dx hpos hr0 hden h)
  cases hrun.symm.trans (quote0for1_ok ctx w dx hpos hr0 hden hmul); rfl

/-! ### `addLiquidity` -/

theorem addLiquidity_ok (a0 : Amount token0) (a1 : Amount token1)
    (h : AddLiqOk w ctx a0 a1) :
    Tx.run (addLiquidity a0 a1) ctx w =
      .ok (Amount.ofWord (mintedShares w.self a0.raw a1.raw),
        World.mk (addLiquidityPost w.self ctx.sender a0.raw a1.raw)
          (extAfterPull w.ext ctx.sender ctx.self a0.raw a1.raw)
          (w.log ++ [.AddLiquidity ctx.sender a0 a1
            (Amount.ofWord (mintedShares w.self a0.raw a1.raw))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hnf0, hnf1, hcov0, hcov1⟩
  have hx0 : model .transferFrom ctx.self [ctx.sender, ctx.self, a0.raw] w.ext.token0 =
      some (1, move w.ext.token0 ctx.sender ctx.self a0.raw) :=
    model_transferFrom hcov0
  have hx1 : model .transferFrom ctx.self [ctx.sender, ctx.self, a1.raw] w.ext.token1 =
      some (1, move w.ext.token1 ctx.sender ctx.self a1.raw) :=
    model_transferFrom hcov1
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, hts0, mintedShares, hadd0, hadd1, haddS, haddB, Binding.safeTransferFrom]
    unfold Tx.call
    dsimp only [Tx.run]
    simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
    simp [extAfterPull, addLiquidityPost, mintedShares, hts, Amount.ofWord_add_right,
      Amount.ofWord_add_left, Amount.ofWord_add, Amount.update_raw, Amount.ofWord_raw,
      Amount.raw_add]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB,
          Binding.safeTransferFrom]
        unfold Tx.call
        dsimp only [Tx.run]
        simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
        simp [extAfterPull, addLiquidityPost, mintedShares, hts, hle,
          Amount.ofWord_add, Amount.ofWord_add_left, Amount.ofWord_add_right,
          Amount.ofWord_raw, Amount.raw_add, Amount.update_raw]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB,
          Binding.safeTransferFrom]
        unfold Tx.call
        dsimp only [Tx.run]
        simp [token0B, token1B, IERC20.model_eq, hnf0, hx0, hnf1, hx1]
        simp [extAfterPull, addLiquidityPost, mintedShares, hts, hle,
          Amount.ofWord_add, Amount.ofWord_add_left, Amount.ofWord_add_right,
          Amount.ofWord_raw, Amount.raw_add, Amount.update_raw]

theorem addLiquidity_reverts_on_fault0 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [hf0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [hf0]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [hf0]

theorem addLiquidity_reverts_on_no_cover0 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : ¬ a0.raw ≤ w.ext.token0.balances ctx.sender) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, model, hcov0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, model, hcov0]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, model, hcov0]

theorem addLiquidity_reverts_on_fault1 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : a0.raw ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  have hx0 := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := a0.raw) (callee := ctx.self) hcov0
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, hx0]
    simp [hf1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [hf1]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [hf1]

theorem addLiquidity_reverts_on_no_cover1 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : a0.raw ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcov1 : ¬ a1.raw ≤ w.ext.token1.balances ctx.sender) :
    Tx.run (addLiquidity a0 a1) ctx w = .error .callFailed := by
  have hx0 := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := a0.raw) (callee := ctx.self) hcov0
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at haddS haddB hminted
    simp [hts, mintedShares, hadd0, hadd1, haddS, haddB]
    unfold Tx.call; dsimp only [Tx.run]
    simp [token0B, IERC20.model_eq, hf0, hx0]
    simp [token1B, IERC20.model_eq, hf1, model, hcov1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [token1B, IERC20.model_eq, hf1, model, hcov1]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [mintedShares, hts, hle] at haddS haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, haddS, haddB]
        unfold Tx.call; dsimp only [Tx.run]
        simp [token0B, IERC20.model_eq, hf0, hx0]
        simp [token1B, IERC20.model_eq, hf1, model, hcov1]

theorem addLiquidity_reverts_on_add_r0 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : ¬ w.self.reserve0.raw + a0.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at hminted
    simp [hts, hadd0]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0]

theorem addLiquidity_reverts_on_add_r1 (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : ¬ w.self.reserve1.raw + a1.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp [hts, mintedShares] at hminted
    simp [hts, hadd0, hadd1]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1]

theorem addLiquidity_reverts_on_add_shares (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : ¬ mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp only [mintedShares, hts] at haddS hminted
    have hS : ¬ a0.raw < wordBound := by simpa [Nat.add_zero] using haddS
    simp [hts, hadd0, hadd1, hS]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        have hS :
            ¬ w.self.totalShares.raw * a0.raw / w.self.reserve0.raw + w.self.totalShares.raw
                < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_pos hle] at haddS
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        have hS :
            ¬ w.self.totalShares.raw * a1.raw / w.self.reserve1.raw + w.self.totalShares.raw
                < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_neg hle] at haddS
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS]

theorem addLiquidity_reverts_on_add_bal (a0 : Amount token0)
    (a1 : Amount token1)
    (hpos0 : 0 < a0.raw) (hpos1 : 0 < a1.raw)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (haddB : ¬ mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  simp [addLiquidity, hpos0, hpos1, Binding.safeTransferFrom]
  by_cases hts : w.self.totalShares.raw = 0
  · have hts0 : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts
    simp [hts0]
    simp only [mintedShares, hts] at haddS haddB hminted
    have hS : a0.raw < wordBound := by simpa [Nat.add_zero] using haddS
    have hB : ¬ a0.raw + (w.self.shares ctx.sender).raw < wordBound := by
      simpa using haddB
    simp [hts, hadd0, hadd1, hS, hB]
  · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (hts h0).elim
    · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      by_cases hle :
          w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
      · have hminted' : 0 < w.self.totalShares.raw * a0.raw / w.self.reserve0.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve0.raw ≤ w.self.totalShares.raw * a0.raw :=
          (pos_div_iff.mp hminted').2
        have hS :
            w.self.totalShares.raw * a0.raw / w.self.reserve0.raw + w.self.totalShares.raw
              < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_pos hle] at haddS
        have hB :
            ¬ w.self.totalShares.raw * a0.raw / w.self.reserve0.raw + (w.self.shares ctx.sender).raw
                < wordBound := by
          unfold mintedShares at haddB
          rwa [if_neg hts, if_pos hle] at haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS, hB]
      · have hminted' : 0 < w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [mintedShares, hts, hle] using hminted
        have hreq : w.self.reserve1.raw ≤ w.self.totalShares.raw * a1.raw :=
          (pos_div_iff.mp hminted').2
        have hS :
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw + w.self.totalShares.raw
              < wordBound := by
          unfold mintedShares at haddS
          rwa [if_neg hts, if_neg hle] at haddS
        have hB :
            ¬ w.self.totalShares.raw * a1.raw / w.self.reserve1.raw + (w.self.shares ctx.sender).raw
                < wordBound := by
          unfold mintedShares at haddB
          rwa [if_neg hts, if_neg hle] at haddB
        simp [hts, hr0, hr1, hr0n, hr1n, hm0, hm1, hle, hreq, hadd0, hadd1, hS, hB]

/-- Success of `addLiquidity` implies the `AddLiqOk` bundle. -/
theorem addLiquidity_ok_of_run {a0 : Amount token0} {a1 : Amount token1}
    {n : Amount lpShare} {w' : World Storage Ext Event}
    (hrun : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    AddLiqOk w ctx a0 a1 := by
  have hpos0 : 0 < a0.raw := by
    by_contra hp; simp [addLiquidity, hp] at hrun
  have hpos1 : 0 < a1.raw := by
    by_contra hp; simp [addLiquidity, hpos0, hp] at hrun
  have hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound) := by
    by_cases hts : w.self.totalShares.raw = 0
    · exact Or.inl hts
    · by_cases hr0 : 0 < w.self.reserve0.raw
      · by_cases hr1 : 0 < w.self.reserve1.raw
        · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
          have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
          by_cases hm0 : w.self.totalShares.raw * a0.raw < wordBound
          · by_cases hm1 : w.self.totalShares.raw * a1.raw < wordBound
            · exact Or.inr ⟨hr0, hr1, hm0, hm1⟩
            · simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1] at hrun
          · simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0] at hrun
        · have hz : w.self.reserve1.raw = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr1)
          have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hz] at hrun
      · have hz : w.self.reserve0.raw = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr0)
        simp [addLiquidity, hpos0, hpos1, hts, hz] at hrun
  have hminted : 0 < mintedShares w.self a0.raw a1.raw := by
    by_contra hm
    by_cases hts : w.self.totalShares.raw = 0
    · simp [mintedShares, hts] at hm
      exact Nat.ne_of_gt hpos0 hm
    · rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
      · exact hts h0
      · have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
        have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
        by_cases hle :
            w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
              w.self.totalShares.raw * a1.raw / w.self.reserve1.raw
        · have hreq := not_side0 hts hr0 hle hm
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq] at hrun
        · have hreq := not_side1 hts hr1 hle hm
          simp [addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq] at hrun
  have hadd0 : w.self.reserve0.raw + a0.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_r0 ctx w a0 a1
      hpos0 hpos1 hminted hprod h)
  have hadd1 : w.self.reserve1.raw + a1.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_r1 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 h)
  have haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_shares ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 h)
  have haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_add_bal ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS h)
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (addLiquidity_reverts_on_fault0 ctx w a0 a1
        hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov0 : a0.raw ≤ w.ext.token0.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_no_cover0 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (addLiquidity_reverts_on_fault1 ctx w a0 a1
        hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 hcov0 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov1 : a1.raw ≤ w.ext.token1.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_no_cover1 ctx w a0 a1
      hpos0 hpos1 hminted hprod hadd0 hadd1 haddS haddB hnf0 hcov0 hnf1 h)
  exact ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hnf0, hnf1, hcov0, hcov1⟩

/-! ### `removeLiquidity` -/

theorem removeLiquidity_ok (s : Amount lpShare) (h : RemoveOk w ctx s) :
    Tx.run (removeLiquidity s) ctx w =
      .ok ((Amount.ofWord (redeemed w.self s.raw).1,
            Amount.ofWord (redeemed w.self s.raw).2),
        World.mk (removeLiquidityPost w.self ctx.sender s.raw)
          (extAfterPush w.ext ctx.self ctx.sender
            (redeemed w.self s.raw).1 (redeemed w.self s.raw).2)
          (w.log ++ [.RemoveLiquidity ctx.sender
            (Amount.ofWord (redeemed w.self s.raw).1)
            (Amount.ofWord (redeemed w.self s.raw).2) s])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1,
    hnf0, hnf1, hcov0, hcov1⟩
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.raw).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.raw).1) :=
    model_transfer hcov0
  have hx1 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.raw).2]
      w.ext.token1 = some (1, move w.ext.token1 ctx.self ctx.sender (redeemed w.self s.raw).2) :=
    model_transfer hcov1
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed, Binding.safeTransfer]
    at hout0 hout1 hle0 hle1 hsLe hx0 hx1 ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hx0]
  simp [hnf1, hx1, extAfterPush, removeLiquidityPost, redeemed,
    Amount.ofWord_sub, Amount.ofWord_sub_left, Amount.ofWord_raw,
    Amount.raw_sub, Amount.update_raw]

theorem removeLiquidity_reverts_on_mul0 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw)
    (hmul0 : ¬ w.self.reserve0.raw * s.raw < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, Binding.safeTransfer]

theorem removeLiquidity_reverts_on_mul1 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : ¬ w.self.reserve1.raw * s.raw < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1]

theorem removeLiquidity_reverts_on_zeroOut0 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : ¬ 0 < (redeemed w.self s.raw).1) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have hreq : ¬ w.self.totalShares.raw ≤ w.self.reserve0.raw * s.raw := by
    intro h
    apply hout0
    simp [redeemed, pos_div_iff]
    exact ⟨hts, h⟩
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1, hreq]

theorem removeLiquidity_reverts_on_zeroOut1 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : ¬ 0 < (redeemed w.self s.raw).2) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have hreq0 : w.self.totalShares.raw ≤ w.self.reserve0.raw * s.raw :=
    (pos_div_iff.mp (by simpa [redeemed] using hout0)).2
  have hreq : ¬ w.self.totalShares.raw ≤ w.self.reserve1.raw * s.raw := by
    intro h
    apply hout1
    simp [redeemed, pos_div_iff]
    exact ⟨hts, h⟩
  simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1, hreq0, hreq]

theorem removeLiquidity_reverts_on_fault0 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw) (hsLe : s.raw ≤ w.self.totalShares.raw)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw)
    (hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed, Binding.safeTransfer]
    at hout0 hout1 hle0 hle1 hsLe ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0]

theorem removeLiquidity_reverts_on_no_cover0 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw) (hsLe : s.raw ≤ w.self.totalShares.raw)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw)
    (hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : ¬ (redeemed w.self s.raw).1 ≤ w.ext.token0.balances ctx.self) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed, Binding.safeTransfer]
    at hout0 hout1 hle0 hle1 hsLe ⊢
  simp only [redeemed] at hcov0
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, model, hcov0]

theorem removeLiquidity_reverts_on_fault1 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw) (hsLe : s.raw ≤ w.self.totalShares.raw)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw)
    (hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : (redeemed w.self s.raw).1 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.raw).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.raw).1) :=
    model_transfer hcov0
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed, Binding.safeTransfer]
    at hout0 hout1 hle0 hle1 hsLe hx0 ⊢
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1]

theorem removeLiquidity_reverts_on_no_cover1 (s : Amount lpShare)
    (hpos : 0 < s.raw) (hbal : s.raw ≤ (w.self.shares ctx.sender).raw)
    (hts : 0 < w.self.totalShares.raw) (hsLe : s.raw ≤ w.self.totalShares.raw)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw)
    (hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hf0 : w.faults w.ncalls = false)
    (hcov0 : (redeemed w.self s.raw).1 ≤ w.ext.token0.balances ctx.self)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcov1 : ¬ (redeemed w.self s.raw).2 ≤ w.ext.token1.balances ctx.self) :
    Tx.run (removeLiquidity s) ctx w = .error .callFailed := by
  have hx0 : model .transfer ctx.self [ctx.sender, (redeemed w.self s.raw).1]
      w.ext.token0 = some (1, move w.ext.token0 ctx.self ctx.sender (redeemed w.self s.raw).1) :=
    model_transfer hcov0
  simp [removeLiquidity, hpos, hbal, Nat.ne_of_gt hts, hmul0, hmul1, redeemed, Binding.safeTransfer]
    at hout0 hout1 hle0 hle1 hsLe hx0 ⊢
  simp only [redeemed] at hcov1
  simp [hts, hout0.2, hout1.2, hle0, hle1, hsLe]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hx0]
  simp [token1B, IERC20.model_eq, hf1, model, hcov1]

/-- Success of `removeLiquidity` implies the `RemoveOk` bundle. -/
theorem removeLiquidity_ok_of_run {s : Amount lpShare} {n : Amount token0 × Amount token1}
    {w' : World Storage Ext Event}
    (hrun : Tx.run (removeLiquidity s) ctx w = .ok (n, w')) :
    RemoveOk w ctx s := by
  have hpos : 0 < s.raw := by
    by_contra hp; simp [removeLiquidity, hp] at hrun
  have hbal : s.raw ≤ (w.self.shares ctx.sender).raw := by
    by_contra h
    simp [removeLiquidity, hpos, h] at hrun
  have hts : 0 < w.self.totalShares.raw := by
    by_contra h
    simp [removeLiquidity, hpos, hbal, h] at hrun
  have hmul0 : w.self.reserve0.raw * s.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul0 ctx w s hpos hbal hts h)
  have hmul1 : w.self.reserve1.raw * s.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul1 ctx w s hpos hbal hts hmul0 h)
  have hout0 : 0 < (redeemed w.self s.raw).1 := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_zeroOut0 ctx w s
      hpos hbal hts hmul0 hmul1 h)
  have hout1 : 0 < (redeemed w.self s.raw).2 := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_zeroOut1 ctx w s
      hpos hbal hts hmul0 hmul1 hout0 h)
  have hsLe : s.raw ≤ w.self.totalShares.raw := by
    by_contra h
    have hreq0 : w.self.totalShares.raw ≤ w.self.reserve0.raw * s.raw :=
      (pos_div_iff.mp (by simpa [redeemed] using hout0)).2
    have hreq1 : w.self.totalShares.raw ≤ w.self.reserve1.raw * s.raw :=
      (pos_div_iff.mp (by simpa [redeemed] using hout1)).2
    simp [removeLiquidity, hpos, hbal, hts, Nat.ne_of_gt hts, hmul0, hmul1,
      hreq0, hreq1, h] at hrun
  have hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw :=
    remove_le_reserves_comm s.raw w.self.reserve0.raw w.self.totalShares.raw hsLe hts
  have hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw :=
    remove_le_reserves_comm s.raw w.self.reserve1.raw w.self.totalShares.raw hsLe hts
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (removeLiquidity_reverts_on_fault0 ctx w s
        hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov0 : (redeemed w.self s.raw).1 ≤ w.ext.token0.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_no_cover0 ctx w s
      hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (removeLiquidity_reverts_on_fault1 ctx w s
        hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 hcov0 hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcov1 : (redeemed w.self s.raw).2 ≤ w.ext.token1.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_no_cover1 ctx w s
      hpos hbal hts hsLe hout0 hout1 hle0 hle1 hmul0 hmul1 hnf0 hcov0 hnf1 h)
  exact ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1, hnf0, hnf1, hcov0, hcov1⟩

/-! ### Swaps -/

theorem swap0for1_ok (dx : Amount token0) (minOut : Amount token1)
    (h : Swap0Ok w ctx dx minOut) :
    Tx.run (swap0for1 dx minOut) ctx w =
      .ok (Amount.ofWord (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw),
        World.mk (swap0Post w.self dx.raw
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw))
          (extAfterSwap0 w.ext ctx.sender ctx.self dx.raw
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw))
          (w.log ++ [.Swap0for1 ctx.sender dx
            (Amount.ofWord (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hadd, hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.raw] w.ext.token0 =
      some (1, move w.ext.token0 ctx.sender ctx.self dx.raw) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw] w.ext.token1 =
      some (1, move w.ext.token1 ctx.self ctx.sender
        (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)) :=
    model_transfer hcovOut
  have hout_le : amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw ≤ w.self.reserve1.raw :=
    remove_le_reserves_comm dx.raw w.self.reserve1.raw (w.self.reserve0.raw + dx.raw)
      (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le hxOut
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
  simp [extAfterSwap0, swap0Post, Amount.ofWord_add_left, Amount.ofWord_sub_left,
    Amount.ofWord_raw, Amount.raw_add, Amount.raw_sub]

theorem swap1for0_ok (dx : Amount token1) (minOut : Amount token0)
    (h : Swap1Ok w ctx dx minOut) :
    Tx.run (swap1for0 dx minOut) ctx w =
      .ok (Amount.ofWord (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw),
        World.mk (swap1Post w.self dx.raw
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw))
          (extAfterSwap1 w.ext ctx.sender ctx.self dx.raw
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw))
          (w.log ++ [.Swap1for0 ctx.sender dx
            (Amount.ofWord (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hadd, hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.raw] w.ext.token1 =
      some (1, move w.ext.token1 ctx.sender ctx.self dx.raw) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self ctx.sender
        (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)) :=
    model_transfer hcovOut
  have hout_le : amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw ≤ w.self.reserve0.raw :=
    remove_le_reserves_comm dx.raw w.self.reserve0.raw (w.self.reserve1.raw + dx.raw)
      (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le hxOut
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
  simp [extAfterSwap1, swap1Post, Amount.ofWord_add_left, Amount.ofWord_sub_left,
    Amount.ofWord_raw, Amount.raw_add, Amount.raw_sub]

theorem swap0for1_reverts_on_fault0 (dx : Amount token0)
    (minOut : Amount token1)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : w.self.reserve1.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve1.raw (w.self.reserve0.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0]

theorem swap0for1_reverts_on_no_cover_in (dx : Amount token0)
    (minOut : Amount token1)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : w.self.reserve1.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : ¬ dx.raw ≤ w.ext.token0.balances ctx.sender) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve1.raw (w.self.reserve0.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, model, hcovIn]

theorem swap0for1_reverts_on_fault1 (dx : Amount token0)
    (minOut : Amount token1)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : w.self.reserve1.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.raw ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.raw) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve1.raw (w.self.reserve0.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hxIn]
  simp [token1B, IERC20.model_eq, hf1]

theorem swap0for1_reverts_on_no_cover_out (dx : Amount token0)
    (minOut : Amount token1)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve0.raw + dx.raw < wordBound)
    (hmul : w.self.reserve1.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.raw ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcovOut : ¬ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw ≤
      w.ext.token1.balances ctx.self) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.raw) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve1.raw (w.self.reserve0.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le hcovOut
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hxIn]
  simp [token1B, IERC20.model_eq, hf1, model, hcovOut]

theorem swap1for0_reverts_on_fault0 (dx : Amount token1)
    (minOut : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve1.raw + dx.raw < wordBound)
    (hmul : w.self.reserve0.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve0.raw (w.self.reserve1.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0]

theorem swap1for0_reverts_on_no_cover_in (dx : Amount token1)
    (minOut : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve1.raw + dx.raw < wordBound)
    (hmul : w.self.reserve0.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : ¬ dx.raw ≤ w.ext.token1.balances ctx.sender) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve0.raw (w.self.reserve1.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, model, hcovIn]

theorem swap1for0_reverts_on_fault1 (dx : Amount token1)
    (minOut : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve1.raw + dx.raw < wordBound)
    (hmul : w.self.reserve0.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.raw ≤ w.ext.token1.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.raw) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve0.raw (w.self.reserve1.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, hxIn]
  simp [token0B, IERC20.model_eq, hf1]

theorem swap1for0_reverts_on_no_cover_out (dx : Amount token1)
    (minOut : Amount token0)
    (hpos : 0 < dx.raw) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hden : w.self.reserve1.raw + dx.raw < wordBound)
    (hmul : w.self.reserve0.raw * dx.raw < wordBound)
    (hmin : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hout : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.raw ≤ w.ext.token1.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcovOut : ¬ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw ≤
      w.ext.token0.balances ctx.self) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.raw) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves_comm dx.raw w.self.reserve0.raw (w.self.reserve1.raw + dx.raw)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le hcovOut
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le, Binding.safeTransferFrom, Binding.safeTransfer]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, hxIn]
  simp [token0B, IERC20.model_eq, hf1, model, hcovOut]

/-- Success of `swap0for1` implies the `Swap0Ok` bundle. -/
theorem swap0for1_ok_of_run {dx : Amount token0} {minOut : Amount token1}
    {n : Amount token1} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (n, w')) :
    Swap0Ok w ctx dx minOut := by
  have hpos : 0 < dx.raw := by
    by_contra hp; simp [swap0for1, hp] at hrun
  have hr0 : 0 < w.self.reserve0.raw := by
    by_contra h; simp [swap0for1, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1.raw := by
    by_contra h; simp [swap0for1, hpos, hr0, h] at hrun
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  have hden : w.self.reserve0.raw + dx.raw < wordBound := by
    by_contra h; simp [swap0for1, hpos, hr0, hr0n, hr1, h] at hrun
  have hmul : w.self.reserve1.raw * dx.raw < wordBound := by
    by_contra h; simp [swap0for1, hpos, hr0, hr0n, hr1, hden, h] at hrun
  have hmin : minOut.raw ≤ amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw := by
    by_contra h
    simp only [amountOut] at h
    simp [swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, h] at hrun
  have hout : 0 < amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw := by
    by_contra h
    have hreq : ¬ w.self.reserve0.raw + dx.raw ≤ w.self.reserve1.raw * dx.raw := by
      intro hle
      apply h
      simp only [amountOut, pos_div_iff]
      exact ⟨Nat.add_pos_left hr0 dx.raw, hle⟩
    simp only [amountOut] at hmin
    simp [swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin, hreq] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (swap0for1_reverts_on_fault0 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.raw ≤ w.ext.token0.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_no_cover_in ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (swap0for1_reverts_on_fault1 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw ≤
      w.ext.token1.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_no_cover_out ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hnf1 h)
  exact ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hnf0, hnf1, hcovIn, hcovOut⟩

/-- Success of `swap1for0` implies the `Swap1Ok` bundle. -/
theorem swap1for0_ok_of_run {dx : Amount token1} {minOut : Amount token0}
    {n : Amount token0} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (n, w')) :
    Swap1Ok w ctx dx minOut := by
  have hpos : 0 < dx.raw := by
    by_contra hp; simp [swap1for0, hp] at hrun
  have hr0 : 0 < w.self.reserve0.raw := by
    by_contra h; simp [swap1for0, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1.raw := by
    by_contra h; simp [swap1for0, hpos, hr0, h] at hrun
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  have hden : w.self.reserve1.raw + dx.raw < wordBound := by
    by_contra h; simp [swap1for0, hpos, hr0, hr1, hr1n, h] at hrun
  have hmul : w.self.reserve0.raw * dx.raw < wordBound := by
    by_contra h; simp [swap1for0, hpos, hr0, hr1, hr1n, hden, h] at hrun
  have hmin : minOut.raw ≤ amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw := by
    by_contra h
    simp only [amountOut] at h
    simp [swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, h] at hrun
  have hout : 0 < amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw := by
    by_contra h
    have hreq : ¬ w.self.reserve1.raw + dx.raw ≤ w.self.reserve0.raw * dx.raw := by
      intro hle
      apply h
      simp only [amountOut, pos_div_iff]
      exact ⟨Nat.add_pos_left hr1 dx.raw, hle⟩
    simp only [amountOut] at hmin
    simp [swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hreq] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (swap1for0_reverts_on_fault0 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.raw ≤ w.ext.token1.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_no_cover_in ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (swap1for0_reverts_on_fault1 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw ≤
      w.ext.token0.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_no_cover_out ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hnf1 h)
  exact ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hnf0, hnf1, hcovIn, hcovOut⟩

theorem swap0for1_k (dx : Amount token0) (minOut : Amount token1)
    (h : Swap0Ok w ctx dx minOut) :
    let out := amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw
    (w.self.reserve0.raw + dx.raw) * (w.self.reserve1.raw - out) ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  k_nondecreasing_0for1 w.self.reserve0.raw w.self.reserve1.raw dx.raw h.r0

theorem swap1for0_k (dx : Amount token1) (minOut : Amount token0)
    (h : Swap1Ok w ctx dx minOut) :
    let out := amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw
    (w.self.reserve1.raw + dx.raw) * (w.self.reserve0.raw - out) ≥
      w.self.reserve0.raw * w.self.reserve1.raw :=
  k_nondecreasing_1for0 w.self.reserve0.raw w.self.reserve1.raw dx.raw h.r1

/-! ### Share-support preservation -/

private abbrev rawShares (shares : Address → Amount lpShare) : Address → Nat :=
  fun a => (shares a).raw

private theorem rawShares_update (shares : Address → Amount lpShare) (who : Address)
    (n : Amount lpShare) :
    rawShares (Function.update shares who n) =
      Function.update (rawShares shares) who n.raw := by
  funext a
  by_cases h : a = who <;> simp [rawShares, Function.update, h]

private theorem nat_sum_update_add (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i (f i + n)) = H.sum f + n := by
  have hS := sum_update_mem H f hi (f i + n)
  omega

private theorem nat_sum_update_sub (H : Finset Address) (f : Address → Nat)
    {i : Address} (hi : i ∈ H) {n : Nat} (hn : n ≤ f i) :
    H.sum (Function.update f i (f i - n)) = H.sum f - n := by
  have hS := sum_update_mem H f hi (f i - n)
  omega

theorem invStorage_of_addLiquidityPost (σ : Storage) (who : Address) (a0 a1 : Nat)
    (hInv : InvStorage σ) :
    InvStorage (addLiquidityPost σ who a0 a1) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  let n := mintedShares σ a0 a1
  by_cases ht : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ who := by intro h; subst h; exact ha ht
      simp only [addLiquidityPost, Function.update_of_ne hne]
      exact h0 a ha
    · have hsum' :
          H.sum (rawShares (addLiquidityPost σ who a0 a1).shares) =
            H.sum (rawShares σ.shares) + n := by
        simp only [addLiquidityPost, rawShares_update, Amount.raw_add, Amount.raw_ofWord, n]
        convert nat_sum_update_add H (rawShares σ.shares) ht n using 1
        simp [rawShares, Nat.add_comm, n]
      change H.sum (rawShares (addLiquidityPost σ who a0 a1).shares) =
        (addLiquidityPost σ who a0 a1).totalShares.raw
      rw [hsum', hsumr]
      simp [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord, Nat.add_comm, n]
  · refine ⟨insert who H, ?_, ?_⟩
    · intro a ha
      have hat : a ≠ who := by
        intro h; subst h; exact ha (Finset.mem_insert_self _ _)
      have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
      simp only [addLiquidityPost, Function.update_of_ne hat]
      exact h0 a haH
    · have hb0 : σ.shares who = 0 := h0 who ht
      have hwho0 : (σ.shares who).raw = 0 := by
        simpa [Amount.raw_zero] using congrArg Amount.raw hb0
      have hupd :
          (fun x =>
            (Function.update σ.shares who (Amount.ofWord n + σ.shares who) x).raw) =
            Function.update (rawShares σ.shares) who (n + (σ.shares who).raw) := by
        funext x
        by_cases hx : x = who <;>
          simp [rawShares, Function.update, hx, Amount.raw_add, Amount.raw_ofWord, n]
      have hframe :=
        sum_update_not_mem H (rawShares σ.shares) ht (n + (σ.shares who).raw)
      have hframe' :
          H.sum (Function.update (rawShares σ.shares) who n) =
            H.sum (rawShares σ.shares) := by
        simpa [hwho0] using hframe
      have hsum' :
          (∑ a ∈ insert who H, rawShares (addLiquidityPost σ who a0 a1).shares a) =
            H.sum (rawShares σ.shares) + n := by
        rw [Finset.sum_insert ht]
        simp only [addLiquidityPost, Function.update_self, rawShares, Amount.raw_add,
          Amount.raw_ofWord, n]
        simp [hupd, hframe', hwho0, Nat.add_comm, n]
      change (∑ a ∈ insert who H, ((addLiquidityPost σ who a0 a1).shares a).raw) =
        (addLiquidityPost σ who a0 a1).totalShares.raw
      rw [hsum', hsumr]
      simp [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord, Nat.add_comm, n]

theorem invStorage_of_removeLiquidityPost (σ : Storage) (who : Address) (s : Nat)
    (hInv : InvStorage σ) (hn : s ≤ (σ.shares who).raw) :
    InvStorage (removeLiquidityPost σ who s) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  by_cases hs : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ who := by intro h; subst h; exact ha hs
      simp only [removeLiquidityPost, Function.update_of_ne ha_src]
      exact h0 a ha
    · have hsumd :
          H.sum (rawShares (removeLiquidityPost σ who s).shares) =
            H.sum (rawShares σ.shares) - s := by
        simp only [removeLiquidityPost, rawShares_update, Amount.raw_sub, Amount.raw_ofWord]
        exact nat_sum_update_sub H (rawShares σ.shares) hs hn
      change H.sum (rawShares (removeLiquidityPost σ who s).shares) =
        (removeLiquidityPost σ who s).totalShares.raw
      rw [hsumd, hsumr]
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
  · have hb0 : σ.shares who = 0 := h0 who hs
    have hwho0 : (σ.shares who).raw = 0 := by
      simpa [Amount.raw_zero] using congrArg Amount.raw hb0
    have hn0 : s = 0 := Nat.eq_zero_of_le_zero (hn.trans_eq hwho0)
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp only [removeLiquidityPost, hn0, Amount.ofWord_zero, Amount.sub_zero,
        Function.update_eq_self]
      exact h0 a ha
    · simp [removeLiquidityPost, hn0, Amount.ofWord_zero, Amount.sub_zero,
        Function.update_eq_self, hsumr]

end Amm
