import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Examples.AmmProofs

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

theorem inv_solvent0 (self : Address) (w : World Storage Ext Event)
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

theorem inv_solvent1 (self : Address) (w : World Storage Ext Event)
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

theorem addLiquidity_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .addLiquidity :=
  PreservesInvFnAt_of_ok fun ⟨a0, a1⟩ ctx w _n _w' hself hsne hInv hrun => by
    have hI := add_ok_inv self hself hsne hInv (addLiquidity_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem removeLiquidity_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .removeLiquidity :=
  PreservesInvFnAt_of_ok fun s ctx w _n _w' hself hsne hInv hrun => by
    have hI := remove_ok_inv self hself hsne hInv (removeLiquidity_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem swap0for1_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .swap0for1 :=
  PreservesInvFnAt_of_ok fun ⟨dx, minOut⟩ ctx w _n _w' hself hsne hInv hrun => by
    have hI := swap0_ok_inv self hself hsne hInv (swap0for1_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem swap1for0_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .swap1for0 :=
  PreservesInvFnAt_of_ok fun ⟨dx, minOut⟩ ctx w _n _w' hself hsne hInv hrun => by
    have hI := swap1_ok_inv self hself hsne hInv (swap1for0_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem getReserves_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .getReserves := by
  intro u ctx w _ _ hInv
  simpa [worldAfter, getReserves_ok ctx w] using hInv

theorem sharesOf_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .sharesOf := by
  intro who ctx w _ _ hInv
  simpa [worldAfter, sharesOf_ok ctx w who] using hInv

theorem quote0for1_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .quote0for1 :=
  PreservesInvFnAt_of_ok fun dx ctx w _n w' _ _ hInv hrun => by
    simpa [quote0for1_same_world ctx w hrun] using hInv

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
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .addLiquidity :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨a0, a1⟩ ctx w a n w' _hInv hrun hdec => by
    have hok := addLiquidity_ok_of_run ctx w hrun
    cases hrun.symm.trans (addLiquidity_ok ctx w a0 a1 hok)
    exact (Nat.not_lt.mpr (claim_mono_add w.self ctx.sender a a0.toNat a1.toNat)) hdec

theorem removeLiquidity_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .removeLiquidity :=
  NoUnauthorizedDecreaseFn_of_ok fun s ctx w a n w' _hInv hrun hdec => by
    change ctx.sender = a
    by_cases hs : ctx.sender = a
    · exact hs
    · have hok := removeLiquidity_ok_of_run ctx w hrun
      cases hrun.symm.trans (removeLiquidity_ok ctx w s hok)
      simp [claim_frame_remove w.self ctx.sender a s.toNat hs] at hdec

theorem swap0for1_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .swap0for1 :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨dx, minOut⟩ ctx w a n w' _hInv hrun hdec => by
    have hok := swap0for1_ok_of_run ctx w hrun
    cases hrun.symm.trans (swap0for1_ok ctx w dx minOut hok)
    simp [claim_eq_swap0] at hdec

theorem swap1for0_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .swap1for0 :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨dx, minOut⟩ ctx w a n w' _hInv hrun hdec => by
    have hok := swap1for0_ok_of_run ctx w hrun
    cases hrun.symm.trans (swap1for0_ok ctx w dx minOut hok)
    simp [claim_eq_swap1] at hdec

theorem getReserves_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .getReserves := by
  intro u ctx w a _hInv hdec
  simp [worldAfter, getReserves_ok ctx w, claim] at hdec

theorem sharesOf_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .sharesOf := by
  intro who ctx w a _hInv hdec
  simp [worldAfter, sharesOf_ok ctx w who, claim] at hdec

theorem quote0for1_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .quote0for1 :=
  NoUnauthorizedDecreaseFn_of_ok fun dx ctx w a _n w' _hInv hrun hdec => by
    simp [quote0for1_same_world ctx w hrun, claim] at hdec

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

end Amm

#lsc_obligations Amm
