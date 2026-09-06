import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lsc.Security.Wealth
import Lsc.Examples.AmmProofs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
Security obligations for the AMM. `Inv` is indexed by the pool address because
holdings read the IERC20 ghosts. `k` is a swap theorem, not `Inv`:
`removeLiquidity` may decrease `k` by flooring.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

def claim (a : Address) (σ : Storage) : Nat := σ.shares a

def claim0 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.reserve0 / σ.totalShares

def claim1 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.reserve1 / σ.totalShares

def Auth (a : Address) (c : Call spec) (_s : Storage) : Prop :=
  match c.fn, c.args with
  | .removeLiquidity, _ => c.sender = a
  | _, _ => False

def inflow (c : Call spec) (w : World Storage Ext Event) : Nat :=
  match c.fn, c.args with
  | .addLiquidity, (a0, a1) =>
    match Tx.run (addLiquidity a0 a1) c.toCtx w with
    | .ok (n, _) => n
    | .error _ => 0
  | _, _ => 0

def holdings0 (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.token0.balances self

def holdings1 (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.token1.balances self

def holdings (self : Address) (w : World Storage Ext Event) : Nat :=
  holdings0 self w

def Inv (self : Address) (w : World Storage Ext Event) : Prop :=
  w.self.reserve0 ≤ holdings0 self w ∧
  w.self.reserve1 ≤ holdings1 self w ∧
  InvStorage w.self

def ammRely (self : Address) (x x' : Ext) : Prop :=
  Rely self x.token0 x'.token0 ∧ Rely self x.token1 x'.token1

theorem inv_rely (self : Address) :
    PreservesInvEnv spec (Inv self) (ammRely self) := by
  intro w x' ⟨h0, h1, hinv⟩ ⟨hR0, hR1⟩
  obtain ⟨hb0, _⟩ := hR0
  obtain ⟨hb1, _⟩ := hR1
  refine ⟨Nat.le_trans h0 hb0, Nat.le_trans h1 hb1, hinv⟩

private theorem invStorage_shares_le (σ : Storage) (hInv : InvStorage σ) (x : Address) :
    σ.shares x ≤ σ.totalShares := by
  obtain ⟨H, h0, hsum⟩ := hInv
  by_cases hx : x ∈ H
  · have hsplit := Finset.sum_erase_add (s := H) (f := fun a => σ.shares a) hx
    have : σ.shares x ≤ H.sum (fun a => σ.shares a) := by omega
    simpa [hsum] using this
  · simp [h0 x hx]

private theorem inv_solvent0 (self : Address) (w : World Storage Ext Event)
    (h : Inv self w) : Solvent claim0 holdings0 self w := by
  obtain ⟨hta, _, ⟨H, h0, hs⟩⟩ := h
  by_cases hts : w.self.totalShares = 0
  · refine ⟨H, fun a ha => by simp [claim0, hts], by simp [claim0, hts]⟩
  · refine ⟨H, ?_, ?_⟩
    · intro a ha; simp [claim0, hts, h0 a ha]
    · have hpos : 0 < w.self.totalShares := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim0 a w.self) =
          H.sum (fun a => w.self.shares a * w.self.reserve0 / w.self.totalShares) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim0, hts]
      exact Nat.le_trans (hcl.symm ▸ sum_mul_div_le H (fun a => w.self.shares a)
        w.self.reserve0 w.self.totalShares hs hpos) hta

private theorem inv_solvent1 (self : Address) (w : World Storage Ext Event)
    (h : Inv self w) : Solvent claim1 holdings1 self w := by
  obtain ⟨_, hta, ⟨H, h0, hs⟩⟩ := h
  by_cases hts : w.self.totalShares = 0
  · refine ⟨H, fun a ha => by simp [claim1, hts], by simp [claim1, hts]⟩
  · refine ⟨H, ?_, ?_⟩
    · intro a ha; simp [claim1, hts, h0 a ha]
    · have hpos : 0 < w.self.totalShares := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim1 a w.self) =
          H.sum (fun a => w.self.shares a * w.self.reserve1 / w.self.totalShares) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim1, hts]
      exact Nat.le_trans (hcl.symm ▸ sum_mul_div_le H (fun a => w.self.shares a)
        w.self.reserve1 w.self.totalShares hs hpos) hta

private theorem add_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {a0 : Amount TOKEN0 scale0} {a1 : Amount TOKEN1 scale1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : AddLiqOk w ctx a0 a1) :
    Inv self (worldAfter (addLiquidity a0 a1) ctx w) := by
  have hrun := addLiquidity_ok ctx w a0 a1 h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_addLiquidityPost w.self ctx.sender a0.toNat a1.toNat hst⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := a0.toNat) hsne
    simp [holdings0, extAfterPull, addLiquidityPost] at h0 ⊢
    rw [hb]; omega
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := a1.toNat) hsne
    simp [holdings1, extAfterPull, addLiquidityPost] at h1 ⊢
    rw [hb]; omega

private theorem remove_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {s : Amount SHARE shareScale}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : RemoveOk w ctx s) :
    Inv self (worldAfter (removeLiquidity s) ctx w) := by
  have hrun := removeLiquidity_ok ctx w s h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_removeLiquidityPost w.self ctx.sender s.toNat hst h.bal⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.toNat).1) hsne.symm
    simp [holdings0, extAfterPush, removeLiquidityPost] at h0 ⊢
    rw [hb]
    have hle := h.le0
    simp [redeemed] at hle ⊢
    omega
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.toNat).2) hsne.symm
    simp [holdings1, extAfterPush, removeLiquidityPost] at h1 ⊢
    rw [hb]
    have hle := h.le1
    simp [redeemed] at hle ⊢
    omega

private theorem swap0_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount TOKEN0 scale0} {minOut : Amount TOKEN1 scale1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap0Ok w ctx dx minOut) :
    Inv self (worldAfter (swap0for1 dx minOut) ctx w) := by
  have hrun := swap0for1_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, ?_⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.toNat) hsne
    simp [holdings0, extAfterSwap0, swap0Post] at h0 ⊢
    rw [hb]; omega
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve0 w.self.reserve1 dx.toNat) hsne.symm
    simp [holdings1, extAfterSwap0, swap0Post] at h1 ⊢
    rw [hb]
    have hout := remove_le_reserves dx.toNat w.self.reserve1 (w.self.reserve0 + dx.toNat)
      (Nat.le_add_left _ _) (Nat.add_pos_left h.r0 _)
    omega
  · obtain ⟨H, h0, hs⟩ := hst
    exact ⟨H, h0, hs⟩

private theorem swap1_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount TOKEN1 scale1} {minOut : Amount TOKEN0 scale0}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap1Ok w ctx dx minOut) :
    Inv self (worldAfter (swap1for0 dx minOut) ctx w) := by
  have hrun := swap1for0_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, ?_⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve1 w.self.reserve0 dx.toNat) hsne.symm
    simp [holdings0, extAfterSwap1, swap1Post] at h0 ⊢
    rw [hb]
    have hout := remove_le_reserves dx.toNat w.self.reserve0 (w.self.reserve1 + dx.toNat)
      (Nat.le_add_left _ _) (Nat.add_pos_left h.r1 _)
    omega
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.toNat) hsne
    simp [holdings1, extAfterSwap1, swap1Post] at h1 ⊢
    rw [hb]; omega
  · obtain ⟨H, h0, hs⟩ := hst
    exact ⟨H, h0, hs⟩

private theorem later_minted_req {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares ≠ 0)
    (hle : a0 * σ.totalShares / σ.reserve0 ≤ a1 * σ.totalShares / σ.reserve1)
    (hminted : 0 < mintedShares σ a0 a1) :
    σ.reserve0 ≤ a0 * σ.totalShares :=
  (pos_div_iff.mp (by simpa [mintedShares, hts, hle] using hminted)).2

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

private theorem later_minted_req' {σ : Storage} {a0 a1 : Nat}
    (hts : σ.totalShares ≠ 0)
    (hle : ¬ a0 * σ.totalShares / σ.reserve0 ≤ a1 * σ.totalShares / σ.reserve1)
    (hminted : 0 < mintedShares σ a0 a1) :
    σ.reserve1 ≤ a1 * σ.totalShares :=
  (pos_div_iff.mp (by simpa [mintedShares, hts, hle] using hminted)).2

theorem addLiquidity_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .addLiquidity := by
  intro ⟨a0, a1⟩ ctx w hself hsne hInv
  by_cases hpos0 : 0 < a0.toNat
  case neg => simp [worldAfter, addLiquidity, hpos0]; exact hInv
  by_cases hpos1 : 0 < a1.toNat
  case neg => simp [worldAfter, addLiquidity, hpos0, hpos1]; exact hInv
  by_cases hts : w.self.totalShares = 0
  · by_cases hminted : 0 < mintedShares w.self a0.toNat a1.toNat
    case neg =>
      simp [mintedShares, hts] at hminted
      omega
    by_cases hadd0 : w.self.reserve0 + a0.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0
      simp [worldAfter, hrun]; exact hInv
    by_cases hadd1 : w.self.reserve1 + a1.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1
      simp [worldAfter, hrun]; exact hInv
    by_cases haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_shares ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS
      simp [worldAfter, hrun]; exact hInv
    by_cases haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_bal ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB
      simp [worldAfter, hrun]; exact hInv
    by_cases hf0 : w.faults w.ncalls = true
    · have hrun := addLiquidity_reverts_on_fault0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0
      simp [worldAfter, hrun]; exact hInv
    have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
    by_cases hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0
      simp [worldAfter, hrun]; exact hInv
    by_cases hf1 : w.faults (w.ncalls + 1) = true
    · have hrun := addLiquidity_reverts_on_fault1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0 hf1
      simp [worldAfter, hrun]; exact hInv
    have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
    by_cases hcov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0 hf1' hcov1
      simp [worldAfter, hrun]; exact hInv
    exact add_ok_inv self hself hsne hInv
      ⟨hpos0, hpos1, hminted, Or.inl hts, hadd0, hadd1, haddS, haddB, hf0', hf1', hcov0, hcov1⟩
  · by_cases hr0 : 0 < w.self.reserve0
    case neg =>
      have hz : w.self.reserve0 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr0)
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hz]; exact hInv
    by_cases hr1 : 0 < w.self.reserve1
    case neg =>
      have hz : w.self.reserve1 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr1)
      have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hz]; exact hInv
    have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
    have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
    by_cases hm0 : a0.toNat * w.self.totalShares < wordBound
    case neg =>
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0]; exact hInv
    by_cases hm1 : a1.toNat * w.self.totalShares < wordBound
    case neg =>
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1]; exact hInv
    by_cases hminted : 0 < mintedShares w.self a0.toNat a1.toNat
    case neg =>
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hreq := not_side0 hts hr0 hle hminted
        simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq]
        exact hInv
      · have hreq := not_side1 hts hr1 hle hminted
        simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq]
        exact hInv
    have hprod : w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound) :=
      Or.inr ⟨hr0, hr1, hm0, hm1⟩
    by_cases hadd0 : w.self.reserve0 + a0.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r0 ctx w a0 a1 hpos0 hpos1 hminted hprod hadd0
      simp [worldAfter, hrun]; exact hInv
    by_cases hadd1 : w.self.reserve1 + a1.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r1 ctx w a0 a1 hpos0 hpos1 hminted hprod hadd0 hadd1
      simp [worldAfter, hrun]; exact hInv
    by_cases haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_shares ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS
      simp [worldAfter, hrun]; exact hInv
    by_cases haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_bal ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB
      simp [worldAfter, hrun]; exact hInv
    by_cases hf0 : w.faults w.ncalls = true
    · have hrun := addLiquidity_reverts_on_fault0 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0
      simp [worldAfter, hrun]; exact hInv
    have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
    by_cases hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover0 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0
      simp [worldAfter, hrun]; exact hInv
    by_cases hf1 : w.faults (w.ncalls + 1) = true
    · have hrun := addLiquidity_reverts_on_fault1 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0 hf1
      simp [worldAfter, hrun]; exact hInv
    have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
    by_cases hcov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover1 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0 hf1' hcov1
      simp [worldAfter, hrun]; exact hInv
    exact add_ok_inv self hself hsne hInv
      ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hf0', hf1', hcov0, hcov1⟩

theorem removeLiquidity_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .removeLiquidity := by
  intro s ctx w hself hsne hInv
  by_cases hpos : 0 < s.toNat
  case neg => simp [worldAfter, removeLiquidity, hpos]; exact hInv
  by_cases hbal : s.toNat ≤ w.self.shares ctx.sender
  case neg => simp [worldAfter, removeLiquidity, hpos, hbal]; exact hInv
  by_cases hts : 0 < w.self.totalShares
  case neg => simp [worldAfter, removeLiquidity, hpos, hbal, hts]; exact hInv
  have hsLe : s.toNat ≤ w.self.totalShares :=
    Nat.le_trans hbal (invStorage_shares_le w.self hInv.2.2 ctx.sender)
  have hle0 := remove_le_reserves s.toNat w.self.reserve0 w.self.totalShares hsLe hts
  have hle1 := remove_le_reserves s.toNat w.self.reserve1 w.self.totalShares hsLe hts
  by_cases hmul0 : s.toNat * w.self.reserve0 < wordBound
  case neg =>
    have hrun := removeLiquidity_reverts_on_mul0 ctx w s hpos hbal hts hmul0
    simp [worldAfter, hrun]; exact hInv
  by_cases hmul1 : s.toNat * w.self.reserve1 < wordBound
  case neg =>
    have hrun := removeLiquidity_reverts_on_mul1 ctx w s hpos hbal hts hmul0 hmul1
    simp [worldAfter, hrun]; exact hInv
  by_cases hout0 : 0 < (redeemed w.self s.toNat).1
  case neg =>
    have hrun := removeLiquidity_reverts_on_zeroOut0 ctx w s hpos hbal hts hmul0 hmul1 hout0
    simp [worldAfter, hrun]; exact hInv
  by_cases hout1 : 0 < (redeemed w.self s.toNat).2
  case neg =>
    have hrun := removeLiquidity_reverts_on_zeroOut1 ctx w s hpos hbal hts hmul0 hmul1 hout0 hout1
    simp [worldAfter, hrun]; exact hInv
  by_cases hf0 : w.faults w.ncalls = true
  · have hrun := removeLiquidity_reverts_on_fault0 ctx w s hpos hbal hts hsLe
      hout0 hout1 hle0 hle1 hmul0 hmul1 hf0
    simp [worldAfter, hrun]; exact hInv
  have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
  by_cases hcov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self
  case neg =>
    have hrun := removeLiquidity_reverts_on_no_cover0 ctx w s hpos hbal hts hsLe
      hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0
    simp [worldAfter, hrun]; exact hInv
  by_cases hf1 : w.faults (w.ncalls + 1) = true
  · have hrun := removeLiquidity_reverts_on_fault1 ctx w s hpos hbal hts hsLe
      hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0 hf1
    simp [worldAfter, hrun]; exact hInv
  have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
  by_cases hcov1 : (redeemed w.self s.toNat).2 ≤ w.ext.token1.balances ctx.self
  case neg =>
    have hrun := removeLiquidity_reverts_on_no_cover1 ctx w s hpos hbal hts hsLe
      hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0 hf1' hcov1
    simp [worldAfter, hrun]; exact hInv
  exact remove_ok_inv self hself hsne hInv
    ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1, hf0', hf1', hcov0, hcov1⟩

theorem swap0for1_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .swap0for1 := by
  intro ⟨dx, minOut⟩ ctx w hself hsne hInv
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, swap0for1, hpos]; exact hInv
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, swap0for1, hpos, hr0]; exact hInv
  by_cases hr1 : 0 < w.self.reserve1
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr1]; exact hInv
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  by_cases hden : w.self.reserve0 + dx.toNat < wordBound
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden]; exact hInv
  by_cases hmul : dx.toNat * w.self.reserve1 < wordBound
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul]; exact hInv
  by_cases hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  case neg =>
    simp only [amountOut] at hmin
    simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin]; exact hInv
  by_cases hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  case neg =>
    have hreq : ¬ w.self.reserve0 + dx.toNat ≤ dx.toNat * w.self.reserve1 := by
      intro h
      apply hout
      simp [amountOut, pos_div_iff]
      exact ⟨Or.inl hr0, h⟩
    simp only [amountOut] at hmin
    simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin, hreq]
    exact hInv
  by_cases hf0 : w.faults w.ncalls = true
  · have hrun := swap0for1_reverts_on_fault0 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout hf0
    simp [worldAfter, hrun]; exact hInv
  have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
  by_cases hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender
  case neg =>
    have hrun := swap0for1_reverts_on_no_cover_in ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn
    simp [worldAfter, hrun]; exact hInv
  by_cases hf1 : w.faults (w.ncalls + 1) = true
  · have hrun := swap0for1_reverts_on_fault1 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1
    simp [worldAfter, hrun]; exact hInv
  have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
  by_cases hcovOut : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
      w.ext.token1.balances ctx.self
  case neg =>
    have hrun := swap0for1_reverts_on_no_cover_out ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1' hcovOut
    simp [worldAfter, hrun]; exact hInv
  exact swap0_ok_inv self hself hsne hInv
    ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hf0', hf1', hcovIn, hcovOut⟩

theorem swap1for0_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .swap1for0 := by
  intro ⟨dx, minOut⟩ ctx w hself hsne hInv
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, swap1for0, hpos]; exact hInv
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, swap1for0, hpos, hr0]; exact hInv
  by_cases hr1 : 0 < w.self.reserve1
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1]; exact hInv
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  by_cases hden : w.self.reserve1 + dx.toNat < wordBound
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden]; exact hInv
  by_cases hmul : dx.toNat * w.self.reserve0 < wordBound
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul]; exact hInv
  by_cases hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  case neg =>
    simp only [amountOut] at hmin
    simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin]; exact hInv
  by_cases hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  case neg =>
    have hreq : ¬ w.self.reserve1 + dx.toNat ≤ dx.toNat * w.self.reserve0 := by
      intro h
      apply hout
      simp [amountOut, pos_div_iff]
      exact ⟨Or.inl hr1, h⟩
    simp only [amountOut] at hmin
    simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hreq]
    exact hInv
  by_cases hf0 : w.faults w.ncalls = true
  · have hrun := swap1for0_reverts_on_fault0 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout hf0
    simp [worldAfter, hrun]; exact hInv
  have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
  by_cases hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender
  case neg =>
    have hrun := swap1for0_reverts_on_no_cover_in ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn
    simp [worldAfter, hrun]; exact hInv
  by_cases hf1 : w.faults (w.ncalls + 1) = true
  · have hrun := swap1for0_reverts_on_fault1 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1
    simp [worldAfter, hrun]; exact hInv
  have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
  by_cases hcovOut : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
      w.ext.token0.balances ctx.self
  case neg =>
    have hrun := swap1for0_reverts_on_no_cover_out ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1' hcovOut
    simp [worldAfter, hrun]; exact hInv
  exact swap1_ok_inv self hself hsne hInv
    ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hf0', hf1', hcovIn, hcovOut⟩

theorem getReserves_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .getReserves := by
  intro u ctx w _ _ hInv
  simpa [worldAfter, getReserves_ok ctx w] using hInv

theorem sharesOf_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .sharesOf := by
  intro who ctx w _ _ hInv
  simpa [worldAfter, sharesOf_ok ctx w who] using hInv

theorem quote0for1_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .quote0for1 := by
  intro dx ctx w _ _ hInv
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, quote0for1, hpos]; exact hInv
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, quote0for1, hpos, hr0]; exact hInv
  by_cases hden : w.self.reserve0 + dx.toNat < wordBound
  case neg =>
    have hrun := quote0for1_reverts_on_add ctx w dx hpos hr0 hden
    simp [worldAfter, hrun]; exact hInv
  by_cases hmul : dx.toNat * w.self.reserve1 < wordBound
  case neg =>
    have hrun := quote0for1_reverts_on_mul ctx w dx hpos hr0 hden hmul
    simp [worldAfter, hrun]; exact hInv
  have hrun := quote0for1_ok ctx w dx hpos hr0 hden hmul
  simp [worldAfter, hrun]; exact hInv

theorem amm_preserves_inv (self : Address) :
    PreservesInvAt spec (Inv self) self :=
  PreservesInvAt.of_fns fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_preserves_inv self
    | .removeLiquidity => removeLiquidity_preserves_inv self
    | .swap0for1 => swap0for1_preserves_inv self
    | .swap1for0 => swap1for0_preserves_inv self
    | .getReserves => getReserves_preserves_inv self
    | .sharesOf => sharesOf_preserves_inv self
    | .quote0for1 => quote0for1_preserves_inv self

theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  ⟨solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent0 self) h tr hW hR,
    solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent1 self) h tr hW hR⟩

/-! ### Authorization (share balances) -/

private theorem claim_mono_add (σ : Storage) (who a : Address) (a0 a1 : Nat) :
    claim a σ ≤ claim a (addLiquidityPost σ who a0 a1) := by
  simp [claim, addLiquidityPost]
  by_cases h : a = who
  · subst h; simp [Function.update]
  · have hne : a ≠ who := h
    rw [Function.update_of_ne hne]

private theorem claim_frame_remove (σ : Storage) (who a : Address) (s : Nat)
    (hne : who ≠ a) :
    claim a (removeLiquidityPost σ who s) = claim a σ := by
  simp [claim, removeLiquidityPost]
  exact Function.update_of_ne (Ne.symm hne) _ _

private theorem claim_eq_swap0 (σ : Storage) (dx out : Nat) (a : Address) :
    claim a (swap0Post σ dx out) = claim a σ := by
  simp [claim, swap0Post]

private theorem claim_eq_swap1 (σ : Storage) (dx out : Nat) (a : Address) :
    claim a (swap1Post σ dx out) = claim a σ := by
  simp [claim, swap1Post]

theorem addLiquidity_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .addLiquidity := by
  intro ⟨a0, a1⟩ ctx w a hInv hdec
  by_cases hpos0 : 0 < a0.toNat
  case neg => simp [worldAfter, addLiquidity, hpos0, claim] at hdec
  by_cases hpos1 : 0 < a1.toNat
  case neg => simp [worldAfter, addLiquidity, hpos0, hpos1, claim] at hdec
  by_cases hts : w.self.totalShares = 0
  · by_cases hminted : 0 < mintedShares w.self a0.toNat a1.toNat
    case neg =>
      simp [mintedShares, hts] at hminted
      omega
    by_cases hadd0 : w.self.reserve0 + a0.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hadd1 : w.self.reserve1 + a1.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1
      simp [worldAfter, hrun, claim] at hdec
    by_cases haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_shares ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS
      simp [worldAfter, hrun, claim] at hdec
    by_cases haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_bal ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf0 : w.faults w.ncalls = true
    · have hrun := addLiquidity_reverts_on_fault0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0
      simp [worldAfter, hrun, claim] at hdec
    have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
    by_cases hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover0 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf1 : w.faults (w.ncalls + 1) = true
    · have hrun := addLiquidity_reverts_on_fault1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0 hf1
      simp [worldAfter, hrun, claim] at hdec
    have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
    by_cases hcov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover1 ctx w a0 a1 hpos0 hpos1 hminted
        (Or.inl hts) hadd0 hadd1 haddS haddB hf0' hcov0 hf1' hcov1
      simp [worldAfter, hrun, claim] at hdec
    have hok : AddLiqOk w ctx a0 a1 :=
      ⟨hpos0, hpos1, hminted, Or.inl hts, hadd0, hadd1, haddS, haddB, hf0', hf1', hcov0, hcov1⟩
    have hrun := addLiquidity_ok ctx w a0 a1 hok
    simp [worldAfter, hrun, claim] at hdec
    exact (Nat.not_lt.mpr (claim_mono_add w.self ctx.sender a a0.toNat a1.toNat)) hdec
  · by_cases hr0 : 0 < w.self.reserve0
    case neg =>
      have hz : w.self.reserve0 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr0)
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hz, claim] at hdec
    by_cases hr1 : 0 < w.self.reserve1
    case neg =>
      have hz : w.self.reserve1 = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hr1)
      have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hz, claim] at hdec
    have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
    have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
    by_cases hm0 : a0.toNat * w.self.totalShares < wordBound
    case neg =>
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, claim] at hdec
    by_cases hm1 : a1.toNat * w.self.totalShares < wordBound
    case neg =>
      simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, claim] at hdec
    by_cases hminted : 0 < mintedShares w.self a0.toNat a1.toNat
    case neg =>
      by_cases hle :
          a0.toNat * w.self.totalShares / w.self.reserve0 ≤
            a1.toNat * w.self.totalShares / w.self.reserve1
      · have hreq := not_side0 hts hr0 hle hminted
        simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq, claim] at hdec
      · have hreq := not_side1 hts hr1 hle hminted
        simp [worldAfter, addLiquidity, hpos0, hpos1, hts, hr0, hr0n, hr1, hr1n, hm0, hm1, hle, hreq, claim] at hdec
    have hprod : w.self.totalShares = 0 ∨
        (0 < w.self.reserve0 ∧ 0 < w.self.reserve1 ∧
          a0.toNat * w.self.totalShares < wordBound ∧
          a1.toNat * w.self.totalShares < wordBound) :=
      Or.inr ⟨hr0, hr1, hm0, hm1⟩
    by_cases hadd0 : w.self.reserve0 + a0.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r0 ctx w a0 a1 hpos0 hpos1 hminted hprod hadd0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hadd1 : w.self.reserve1 + a1.toNat < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_r1 ctx w a0 a1 hpos0 hpos1 hminted hprod hadd0 hadd1
      simp [worldAfter, hrun, claim] at hdec
    by_cases haddS : mintedShares w.self a0.toNat a1.toNat + w.self.totalShares < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_shares ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS
      simp [worldAfter, hrun, claim] at hdec
    by_cases haddB : mintedShares w.self a0.toNat a1.toNat + w.self.shares ctx.sender < wordBound
    case neg =>
      have hrun := addLiquidity_reverts_on_add_bal ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf0 : w.faults w.ncalls = true
    · have hrun := addLiquidity_reverts_on_fault0 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0
      simp [worldAfter, hrun, claim] at hdec
    have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
    by_cases hcov0 : a0.toNat ≤ w.ext.token0.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover0 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf1 : w.faults (w.ncalls + 1) = true
    · have hrun := addLiquidity_reverts_on_fault1 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0 hf1
      simp [worldAfter, hrun, claim] at hdec
    have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
    by_cases hcov1 : a1.toNat ≤ w.ext.token1.balances ctx.sender
    case neg =>
      have hrun := addLiquidity_reverts_on_no_cover1 ctx w a0 a1 hpos0 hpos1 hminted
        hprod hadd0 hadd1 haddS haddB hf0' hcov0 hf1' hcov1
      simp [worldAfter, hrun, claim] at hdec
    have hok : AddLiqOk w ctx a0 a1 :=
      ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB, hf0', hf1', hcov0, hcov1⟩
    have hrun := addLiquidity_ok ctx w a0 a1 hok
    simp [worldAfter, hrun, claim] at hdec
    exact (Nat.not_lt.mpr (claim_mono_add w.self ctx.sender a a0.toNat a1.toNat)) hdec

theorem removeLiquidity_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .removeLiquidity := by
  intro s ctx w a hInv hdec
  change ctx.sender = a
  by_cases hs : ctx.sender = a
  · exact hs
  · by_cases hpos : 0 < s.toNat
    case neg => simp [worldAfter, removeLiquidity, hpos, claim] at hdec
    by_cases hbal : s.toNat ≤ w.self.shares ctx.sender
    case neg => simp [worldAfter, removeLiquidity, hpos, hbal, claim] at hdec
    by_cases hts : 0 < w.self.totalShares
    case neg => simp [worldAfter, removeLiquidity, hpos, hbal, hts, claim] at hdec
    have hsLe : s.toNat ≤ w.self.totalShares :=
      Nat.le_trans hbal (invStorage_shares_le w.self hInv.2.2 ctx.sender)
    have hle0 := remove_le_reserves s.toNat w.self.reserve0 w.self.totalShares hsLe hts
    have hle1 := remove_le_reserves s.toNat w.self.reserve1 w.self.totalShares hsLe hts
    by_cases hmul0 : s.toNat * w.self.reserve0 < wordBound
    case neg =>
      have hrun := removeLiquidity_reverts_on_mul0 ctx w s hpos hbal hts hmul0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hmul1 : s.toNat * w.self.reserve1 < wordBound
    case neg =>
      have hrun := removeLiquidity_reverts_on_mul1 ctx w s hpos hbal hts hmul0 hmul1
      simp [worldAfter, hrun, claim] at hdec
    by_cases hout0 : 0 < (redeemed w.self s.toNat).1
    case neg =>
      have hrun := removeLiquidity_reverts_on_zeroOut0 ctx w s hpos hbal hts hmul0 hmul1 hout0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hout1 : 0 < (redeemed w.self s.toNat).2
    case neg =>
      have hrun := removeLiquidity_reverts_on_zeroOut1 ctx w s hpos hbal hts hmul0 hmul1 hout0 hout1
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf0 : w.faults w.ncalls = true
    · have hrun := removeLiquidity_reverts_on_fault0 ctx w s hpos hbal hts hsLe
        hout0 hout1 hle0 hle1 hmul0 hmul1 hf0
      simp [worldAfter, hrun, claim] at hdec
    have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
    by_cases hcov0 : (redeemed w.self s.toNat).1 ≤ w.ext.token0.balances ctx.self
    case neg =>
      have hrun := removeLiquidity_reverts_on_no_cover0 ctx w s hpos hbal hts hsLe
        hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0
      simp [worldAfter, hrun, claim] at hdec
    by_cases hf1 : w.faults (w.ncalls + 1) = true
    · have hrun := removeLiquidity_reverts_on_fault1 ctx w s hpos hbal hts hsLe
        hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0 hf1
      simp [worldAfter, hrun, claim] at hdec
    have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
    by_cases hcov1 : (redeemed w.self s.toNat).2 ≤ w.ext.token1.balances ctx.self
    case neg =>
      have hrun := removeLiquidity_reverts_on_no_cover1 ctx w s hpos hbal hts hsLe
        hout0 hout1 hle0 hle1 hmul0 hmul1 hf0' hcov0 hf1' hcov1
      simp [worldAfter, hrun, claim] at hdec
    have hok : RemoveOk w ctx s :=
      ⟨hpos, hbal, hts, hsLe, hout0, hout1, hle0, hle1, hmul0, hmul1, hf0', hf1', hcov0, hcov1⟩
    have hrun := removeLiquidity_ok ctx w s hok
    simp [worldAfter, hrun] at hdec
    have hne : ctx.sender ≠ a := hs
    simpa [claim_frame_remove w.self ctx.sender a s.toNat hne] using hdec

theorem swap0for1_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .swap0for1 := by
  intro ⟨dx, minOut⟩ ctx w a _hInv hdec
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, swap0for1, hpos, claim] at hdec
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, swap0for1, hpos, hr0, claim] at hdec
  by_cases hr1 : 0 < w.self.reserve1
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr1, claim] at hdec
  have hr0n : w.self.reserve0 ≠ 0 := Nat.ne_of_gt hr0
  by_cases hden : w.self.reserve0 + dx.toNat < wordBound
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, claim] at hdec
  by_cases hmul : dx.toNat * w.self.reserve1 < wordBound
  case neg => simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, claim] at hdec
  by_cases hmin : minOut.toNat ≤ amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  case neg =>
    simp only [amountOut] at hmin
    simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin, claim] at hdec
  by_cases hout : 0 < amountOut w.self.reserve0 w.self.reserve1 dx.toNat
  case neg =>
    have hreq : ¬ w.self.reserve0 + dx.toNat ≤ dx.toNat * w.self.reserve1 := by
      intro h
      apply hout
      simp [amountOut, pos_div_iff]
      exact ⟨Or.inl hr0, h⟩
    simp only [amountOut] at hmin
    simp [worldAfter, swap0for1, hpos, hr0, hr0n, hr1, hden, hmul, hmin, hreq, claim] at hdec
  by_cases hf0 : w.faults w.ncalls = true
  · have hrun := swap0for1_reverts_on_fault0 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout hf0
    simp [worldAfter, hrun, claim] at hdec
  have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
  by_cases hcovIn : dx.toNat ≤ w.ext.token0.balances ctx.sender
  case neg =>
    have hrun := swap0for1_reverts_on_no_cover_in ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn
    simp [worldAfter, hrun, claim] at hdec
  by_cases hf1 : w.faults (w.ncalls + 1) = true
  · have hrun := swap0for1_reverts_on_fault1 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1
    simp [worldAfter, hrun, claim] at hdec
  have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
  by_cases hcovOut : amountOut w.self.reserve0 w.self.reserve1 dx.toNat ≤
      w.ext.token1.balances ctx.self
  case neg =>
    have hrun := swap0for1_reverts_on_no_cover_out ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1' hcovOut
    simp [worldAfter, hrun, claim] at hdec
  have hok : Swap0Ok w ctx dx minOut :=
    ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hf0', hf1', hcovIn, hcovOut⟩
  have hrun := swap0for1_ok ctx w dx minOut hok
  simp [worldAfter, hrun, claim_eq_swap0] at hdec

theorem swap1for0_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .swap1for0 := by
  intro ⟨dx, minOut⟩ ctx w a _hInv hdec
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, swap1for0, hpos, claim] at hdec
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, swap1for0, hpos, hr0, claim] at hdec
  by_cases hr1 : 0 < w.self.reserve1
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1, claim] at hdec
  have hr1n : w.self.reserve1 ≠ 0 := Nat.ne_of_gt hr1
  by_cases hden : w.self.reserve1 + dx.toNat < wordBound
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, claim] at hdec
  by_cases hmul : dx.toNat * w.self.reserve0 < wordBound
  case neg => simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, claim] at hdec
  by_cases hmin : minOut.toNat ≤ amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  case neg =>
    simp only [amountOut] at hmin
    simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin, claim] at hdec
  by_cases hout : 0 < amountOut w.self.reserve1 w.self.reserve0 dx.toNat
  case neg =>
    have hreq : ¬ w.self.reserve1 + dx.toNat ≤ dx.toNat * w.self.reserve0 := by
      intro h
      apply hout
      simp [amountOut, pos_div_iff]
      exact ⟨Or.inl hr1, h⟩
    simp only [amountOut] at hmin
    simp [worldAfter, swap1for0, hpos, hr0, hr1, hr1n, hden, hmul, hmin, hreq, claim] at hdec
  by_cases hf0 : w.faults w.ncalls = true
  · have hrun := swap1for0_reverts_on_fault0 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout hf0
    simp [worldAfter, hrun, claim] at hdec
  have hf0' : w.faults w.ncalls = false := (Bool.not_eq_true _).mp hf0
  by_cases hcovIn : dx.toNat ≤ w.ext.token1.balances ctx.sender
  case neg =>
    have hrun := swap1for0_reverts_on_no_cover_in ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn
    simp [worldAfter, hrun, claim] at hdec
  by_cases hf1 : w.faults (w.ncalls + 1) = true
  · have hrun := swap1for0_reverts_on_fault1 ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1
    simp [worldAfter, hrun, claim] at hdec
  have hf1' : w.faults (w.ncalls + 1) = false := (Bool.not_eq_true _).mp hf1
  by_cases hcovOut : amountOut w.self.reserve1 w.self.reserve0 dx.toNat ≤
      w.ext.token0.balances ctx.self
  case neg =>
    have hrun := swap1for0_reverts_on_no_cover_out ctx w dx minOut hpos hr0 hr1 hden hmul hmin hout
      hf0' hcovIn hf1' hcovOut
    simp [worldAfter, hrun, claim] at hdec
  have hok : Swap1Ok w ctx dx minOut :=
    ⟨hpos, hr0, hr1, hden, hmul, hmin, hout, hden, hf0', hf1', hcovIn, hcovOut⟩
  have hrun := swap1for0_ok ctx w dx minOut hok
  simp [worldAfter, hrun, claim_eq_swap1] at hdec

theorem getReserves_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .getReserves := by
  intro u ctx w a _hInv hdec
  simp [worldAfter, getReserves_ok ctx w, claim] at hdec

theorem sharesOf_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .sharesOf := by
  intro who ctx w a _hInv hdec
  simp [worldAfter, sharesOf_ok ctx w who, claim] at hdec

theorem quote0for1_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .quote0for1 := by
  intro dx ctx w a _hInv hdec
  by_cases hpos : 0 < dx.toNat
  case neg => simp [worldAfter, quote0for1, hpos, claim] at hdec
  by_cases hr0 : 0 < w.self.reserve0
  case neg => simp [worldAfter, quote0for1, hpos, hr0, claim] at hdec
  by_cases hden : w.self.reserve0 + dx.toNat < wordBound
  case neg =>
    have hrun := quote0for1_reverts_on_add ctx w dx hpos hr0 hden
    simp [worldAfter, hrun, claim] at hdec
  by_cases hmul : dx.toNat * w.self.reserve1 < wordBound
  case neg =>
    have hrun := quote0for1_reverts_on_mul ctx w dx hpos hr0 hden hmul
    simp [worldAfter, hrun, claim] at hdec
  have hrun := quote0for1_ok ctx w dx hpos hr0 hden hmul
  simp [worldAfter, hrun, claim] at hdec

theorem amm_no_unauth (self : Address) :
    NoUnauthorizedDecrease spec (Inv self) claim Auth :=
  NoUnauthorizedDecrease.of_fns fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_auth self
    | .removeLiquidity => removeLiquidity_auth self
    | .swap0for1 => swap0for1_auth self
    | .swap1for0 => swap1for0_auth self
    | .getReserves => getReserves_auth self
    | .sharesOf => sharesOf_auth self
    | .quote0for1 => quote0for1_auth self

theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (amm_no_unauth self) (amm_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Amm

#lsc_obligations Amm

#print axioms Amm.amm_solvent
#print axioms Amm.amm_no_unauthorized_extraction
