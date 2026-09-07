import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Examples.Amm

set_option linter.unusedSimpArgs false

/-!
# Amm — functional lemmas

`Tx.run` statements. Storage is `Nat`; ABI amounts use `toNat` / `ofNat`.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

variable (ctx : Ctx) (w : World Storage Ext Event)

/-! ### Pure arithmetic (rounding toward the pool, `k` monotone on swaps) -/

/-- `⌊s * r / S⌋ ≤ r` when `s ≤ S`. -/
theorem remove_le_reserves (s r S : Nat) (hs : s ≤ S) (hS : 0 < S) :
    s * r / S ≤ r := by
  have hmul : s * r ≤ S * r := Nat.mul_le_mul_right r hs
  have hdiv : s * r / S ≤ S * r / S := Nat.div_le_div_right hmul
  simpa [Nat.mul_div_right r hS] using hdiv

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
    (rIn + dx) * (rOut - dx * rOut / (rIn + dx)) ≥ rIn * rOut := by
  set den := rIn + dx
  have hden : 0 < den := Nat.add_pos_left hIn dx
  have hout : dx * rOut / den ≤ rOut :=
    remove_le_reserves dx rOut den (Nat.le_add_left dx rIn) hden
  have hchop : den * (dx * rOut / den) ≤ dx * rOut := Nat.mul_div_le (dx * rOut) den
  have hdistrib : den * (rOut - dx * rOut / den) = den * rOut - den * (dx * rOut / den) :=
    Nat.mul_sub_left_distrib den rOut (dx * rOut / den)
  have hge : den * rOut - den * (dx * rOut / den) ≥ den * rOut - dx * rOut :=
    Nat.sub_le_sub_left hchop _
  have hk : den * rOut - dx * rOut = rIn * rOut := by
    simp [den, Nat.add_mul]
  omega

theorem k_nondecreasing_0for1 (r0 r1 dx : Nat) (h0 : 0 < r0) :
    (r0 + dx) * (r1 - dx * r1 / (r0 + dx)) ≥ r0 * r1 :=
  k_nondecreasing r0 r1 dx h0

theorem k_nondecreasing_1for0 (r0 r1 dx : Nat) (h1 : 0 < r1) :
    (r1 + dx) * (r0 - dx * r0 / (r1 + dx)) ≥ r0 * r1 := by
  simpa [Nat.mul_comm r0 r1] using k_nondecreasing r1 r0 dx h1

/-! ### Share accounting -/

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => σ.shares a) = σ.totalShares

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

def swap0Post (σ : Storage) (dx out : Nat) : Storage :=
  { σ with reserve0 := σ.reserve0 + dx, reserve1 := σ.reserve1 - out }

def swap1Post (σ : Storage) (dx out : Nat) : Storage :=
  { σ with reserve1 := σ.reserve1 + dx, reserve0 := σ.reserve0 - out }

def amountOut (rIn rOut dx : Nat) : Nat :=
  dx * rOut / (rIn + dx)

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
  den : w.self.reserve0 + dx.toNat < wordBound
  mul : dx.toNat * w.self.reserve1 < wordBound
  min : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  out : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  add : w.self.reserve0 + dx.toNat < wordBound
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
  den : w.self.reserve1 + dx.toNat < wordBound
  mul : dx.toNat * w.self.reserve0 < wordBound
  min : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  out : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  add : w.self.reserve1 + dx.toNat < wordBound
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

theorem quote0for1_ok (dx : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve1 < wordBound) :
    Tx.run (quote0for1 dx) ctx w =
      .ok (amountOut w.self.reserve0 w.self.reserve1 dx.toNat, w) := by
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, amountOut, hpos, hr0, hr0n, hden, hmul]

theorem quote0for1_reverts_on_add (dx : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0)
    (hden : ¬ w.self.reserve0 + dx.toNat < wordBound) :
    Tx.run (quote0for1 dx) ctx w = .error (.arith .overflow) := by
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, hpos, hr0, hr0n, hden]

theorem quote0for1_reverts_on_mul (dx : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : ¬ dx.toNat * w.self.reserve1 < wordBound) :
    Tx.run (quote0for1 dx) ctx w = .error (.arith .overflow) := by
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp [quote0for1, hpos, hr0, hr0n, hden, hmul]

theorem quote0for1_same_world {dx : Amount TOKEN0 scale0} {n : Nat}
    {w' : World Storage Ext Event}
    (hrun : Tx.run (quote0for1 dx) ctx w = .ok (n, w')) : w' = w := by
  have hpos : 0 < dx.toNat := by
    by_contra hp; simp [quote0for1, hp] at hrun
  have hr0 : 0 < w.self.reserve0 := by
    by_contra h; simp [quote0for1, hpos, h] at hrun
  have hden : w.self.reserve0 + dx.toNat < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (quote0for1_reverts_on_add ctx w dx hpos hr0 h)
  have hmul : dx.toNat * w.self.reserve1 < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (quote0for1_reverts_on_mul ctx w dx hpos hr0 hden h)
  cases hrun.symm.trans (quote0for1_ok ctx w dx hpos hr0 hden hmul); rfl

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

theorem swap0for1_ok (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    (h : Swap0Ok w ctx dx minOut) :
    Tx.run (swap0for1 dx minOut) ctx w =
      .ok (amountOut w.self.reserve0 w.self.reserve1 dx.toNat,
        World.mk (swap0Post w.self dx.toNat
            (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))
          (extAfterSwap0 w.ext ctx.sender ctx.self dx.toNat
            (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))
          (w.log ++ [.Swap0for1 ctx.sender dx
            (Amount.ofNat (amountOut w.self.reserve0 w.self.reserve1 dx.toNat))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hadd, hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.toNat] w.ext.token0 =
      some (1, move w.ext.token0 ctx.sender ctx.self dx.toNat) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve0 w.self.reserve1 dx.toNat] w.ext.token1 =
      some (1, move w.ext.token1 ctx.self ctx.sender
        (amountOut w.self.reserve0 w.self.reserve1 dx.toNat)) :=
    model_transfer hcovOut
  have hout_le : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤ w.self.reserve1 :=
    remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
      (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le hxOut
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
  simp [extAfterSwap0, swap0Post]

theorem swap1for0_ok (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    (h : Swap1Ok w ctx dx minOut) :
    Tx.run (swap1for0 dx minOut) ctx w =
      .ok (amountOut w.self.reserve1 w.self.reserve0 dx.toNat,
        World.mk (swap1Post w.self dx.toNat
            (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))
          (extAfterSwap1 w.ext ctx.sender ctx.self dx.toNat
            (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))
          (w.log ++ [.Swap1for0 ctx.sender dx
            (Amount.ofNat (amountOut w.self.reserve1 w.self.reserve0 dx.toNat))])
          w.faults (w.ncalls + 2)) := by
  rcases h with ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hadd, hnf0, hnf1, hcovIn, hcovOut⟩
  have hxIn : model .transferFrom ctx.self [ctx.sender, ctx.self, dx.toNat] w.ext.token1 =
      some (1, move w.ext.token1 ctx.sender ctx.self dx.toNat) :=
    model_transferFrom hcovIn
  have hxOut : model .transfer ctx.self
      [ctx.sender, amountOut w.self.reserve1 w.self.reserve0 dx.toNat] w.ext.token0 =
      some (1, move w.ext.token0 ctx.self ctx.sender
        (amountOut w.self.reserve1 w.self.reserve0 dx.toNat)) :=
    model_transfer hcovOut
  have hout_le : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤ w.self.reserve0 :=
    remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
      (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le hxOut
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call
  dsimp only [Tx.run]
  simp [token0B, token1B, IERC20.model_eq, hnf0, hxIn, hnf1, hxOut]
  simp [extAfterSwap1, swap1Post]

theorem swap0for1_reverts_on_fault0 (dx : Amount TOKEN0 scale0)
    (minOut : Amount TOKEN1 scale1)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve1 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0]

theorem swap0for1_reverts_on_no_cover_in (dx : Amount TOKEN0 scale0)
    (minOut : Amount TOKEN1 scale1)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve1 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : ¬ dx.toNat ≤ w.ext.token0.balances ctx.sender) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, model, hcovIn]

theorem swap0for1_reverts_on_fault1 (dx : Amount TOKEN0 scale0)
    (minOut : Amount TOKEN1 scale1)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve1 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.toNat) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hxIn]
  simp [token1B, IERC20.model_eq, hf1]

theorem swap0for1_reverts_on_no_cover_out (dx : Amount TOKEN0 scale0)
    (minOut : Amount TOKEN1 scale1)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve0 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve1 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcovOut : ¬ amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
      w.ext.token1.balances ctx.self) :
    Tx.run (swap0for1 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.toNat) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr0 _)
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  simp only [amountOut] at hmin hout hout_le hcovOut
  have hout' := pos_div_iff.mp hout
  simp [swap0for1, amountOut, hpos, hr0, hr1, hr0n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token0B, IERC20.model_eq, hf0, hxIn]
  simp [token1B, IERC20.model_eq, hf1, model, hcovOut]

theorem swap1for0_reverts_on_fault0 (dx : Amount TOKEN1 scale1)
    (minOut : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve1 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve0 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hf0 : w.faults w.ncalls = true) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0]

theorem swap1for0_reverts_on_no_cover_in (dx : Amount TOKEN1 scale1)
    (minOut : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve1 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve0 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : ¬ dx.toNat ≤ w.ext.token1.balances ctx.sender) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hout_le := remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, model, hcovIn]

theorem swap1for0_reverts_on_fault1 (dx : Amount TOKEN1 scale1)
    (minOut : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve1 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve0 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = true) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.toNat) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, hxIn]
  simp [token0B, IERC20.model_eq, hf1]

theorem swap1for0_reverts_on_no_cover_out (dx : Amount TOKEN1 scale1)
    (minOut : Amount TOKEN0 scale0)
    (hpos : 0 < dx.toNat) (hr0 : 0 < w.self.reserve0) (hr1 : 0 < w.self.reserve1)
    (hden : w.self.reserve1 + dx.toNat < wordBound)
    (hmul : dx.toNat * w.self.reserve0 < wordBound)
    (hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat)
    (hf0 : w.faults w.ncalls = false)
    (hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender)
    (hf1 : w.faults (w.ncalls + 1) = false)
    (hcovOut : ¬ amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
      w.ext.token0.balances ctx.self) :
    Tx.run (swap1for0 dx minOut) ctx w = .error .callFailed := by
  have hxIn := model_transferFrom (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
    (amt := dx.toNat) (callee := ctx.self) hcovIn
  have hout_le := remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
    (Nat.le_add_left _ _) (Nat.add_pos_left hr1 _)
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  simp only [amountOut] at hmin hout hout_le hcovOut
  have hout' := pos_div_iff.mp hout
  simp [swap1for0, amountOut, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hout'.1, hout'.2, hout_le]
  unfold Tx.call; dsimp only [Tx.run]
  simp [token1B, IERC20.model_eq, hf0, hxIn]
  simp [token0B, IERC20.model_eq, hf1, model, hcovOut]

/-- Success of `swap0for1` implies the `Swap0Ok` bundle. -/
theorem swap0for1_ok_of_run {dx : Amount TOKEN0 scale0} {minOut : Amount TOKEN1 scale1}
    {n : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (n, w')) :
    Swap0Ok w ctx dx minOut := by
  have hpos : 0 < dx.toNat := by
    by_contra hp; simp [swap0for1, hp] at hrun
  have hr0 : 0 < w.self.reserve0 := by
    by_contra h; simp [swap0for1, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1 := by
    by_contra h; simp [swap0for1, hpos, hr0, h] at hrun
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  have hden : w.self.reserve0 + dx.toNat < wordBound := by
    by_contra h; simp [swap0for1, hpos, hr0, hr0n, hr1, h] at hrun
  have hmul : dx.toNat * w.self.reserve1 < wordBound := by
    by_contra h; simp [swap0for1, hpos, hr0, hr0n, hr1, hden, h] at hrun
  have hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat := by
    by_contra h
    simp only [amountOut] at h
    simp [swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, h] at hrun
  have hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat := by
    by_contra h
    have hreq : ¬ w.self.reserve0 + dx.toNat ≤ dx.toNat * w.self.reserve1 := by
      intro hle
      apply h
      simp [amountOut, pos_div_iff]
      exact ⟨Nat.add_pos_left hr0 _, hle⟩
    simp only [amountOut] at hmin
    simp [swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin, hreq] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (swap0for1_reverts_on_fault0 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_no_cover_in ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (swap0for1_reverts_on_fault1 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
      w.ext.token1.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_no_cover_out ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hnf1 h)
  exact ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hnf0, hnf1, hcovIn, hcovOut⟩

/-- Success of `swap1for0` implies the `Swap1Ok` bundle. -/
theorem swap1for0_ok_of_run {dx : Amount TOKEN1 scale1} {minOut : Amount TOKEN0 scale0}
    {n : Nat} {w' : World Storage Ext Event}
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (n, w')) :
    Swap1Ok w ctx dx minOut := by
  have hpos : 0 < dx.toNat := by
    by_contra hp; simp [swap1for0, hp] at hrun
  have hr0 : 0 < w.self.reserve0 := by
    by_contra h; simp [swap1for0, hpos, h] at hrun
  have hr1 : 0 < w.self.reserve1 := by
    by_contra h; simp [swap1for0, hpos, hr0, h] at hrun
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  have hden : w.self.reserve1 + dx.toNat < wordBound := by
    by_contra h; simp [swap1for0, hpos, hr0, hr1, hr1n, h] at hrun
  have hmul : dx.toNat * w.self.reserve0 < wordBound := by
    by_contra h; simp [swap1for0, hpos, hr0, hr1, hr1n, hden, h] at hrun
  have hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat := by
    by_contra h
    simp only [amountOut] at h
    simp [swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, h] at hrun
  have hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat := by
    by_contra h
    have hreq : ¬ w.self.reserve1 + dx.toNat ≤ dx.toNat * w.self.reserve0 := by
      intro hle
      apply h
      simp [amountOut, pos_div_iff]
      exact ⟨Nat.add_pos_left hr1 _, hle⟩
    simp only [amountOut] at hmin
    simp [swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hreq] at hrun
  have hnf0 : w.faults w.ncalls = false := by
    by_cases hf : w.faults w.ncalls = true
    · exact (Tx.run_ok_error hrun (swap1for0_reverts_on_fault0 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_no_cover_in ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 h)
  have hnf1 : w.faults (w.ncalls + 1) = false := by
    by_cases hf : w.faults (w.ncalls + 1) = true
    · exact (Tx.run_ok_error hrun (swap1for0_reverts_on_fault1 ctx w dx minOut
        hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hf)).elim
    · exact (Bool.not_eq_true _).mp hf
  have hcovOut : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
      w.ext.token0.balances ctx.self := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_no_cover_out ctx w dx minOut
      hpos hr0 hr1 hden hmul hmin hout hnf0 hcovIn hnf1 h)
  exact ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hnf0, hnf1, hcovIn, hcovOut⟩

theorem swap0for1_k (dx : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1)
    (h : Swap0Ok w ctx dx minOut) :
    let out := amountOut w.self.reserve0 w.self.reserve1 dx.toNat
    (w.self.reserve0 + dx.toNat) * (w.self.reserve1 - out) ≥
      w.self.reserve0 * w.self.reserve1 :=
  k_nondecreasing_0for1 w.self.reserve0 w.self.reserve1 dx.toNat h.r0

theorem swap1for0_k (dx : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0)
    (h : Swap1Ok w ctx dx minOut) :
    let out := amountOut w.self.reserve1 w.self.reserve0 dx.toNat
    (w.self.reserve1 + dx.toNat) * (w.self.reserve0 - out) ≥
      w.self.reserve0 * w.self.reserve1 :=
  k_nondecreasing_1for0 w.self.reserve0 w.self.reserve1 dx.toNat h.r1

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

end Amm
