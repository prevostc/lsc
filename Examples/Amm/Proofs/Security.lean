import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Examples.Amm.Spec
import Examples.Amm.Proofs.Tx

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
Security obligations for the AMM. `Inv` is indexed by the pool address because
holdings read the IERC20 ghosts. `k` is a swap theorem, not `Inv`:
`removeLiquidity` may decrease `k` by flooring.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

theorem inv_rely (self : Address) :
    PreservesInvEnv spec (Inv self) (ammRely self) := by
  intro w x' ⟨h0, h1, hinv⟩ ⟨hR0, hR1⟩
  obtain ⟨hb0, _⟩ := hR0
  obtain ⟨hb1, _⟩ := hR1
  refine ⟨Nat.le_trans h0 hb0, Nat.le_trans h1 hb1, hinv⟩

theorem inv_solvent0 (self : Address) (w : World Storage Ext Event)
    (h : Inv self w) : Solvent claim0 holdings0 self w := by
  obtain ⟨hta, _, ⟨H, h0, hs⟩⟩ := h
  by_cases hts : w.self.totalShares.raw = 0
  · refine ⟨H, fun a ha => by simp [claim0, hts, Amount.eq_iff],
      by simp [claim0, hts, Amount.eq_iff]⟩
  · refine ⟨H, ?_, ?_⟩
    · intro a ha; simp [claim0, hts, Amount.eq_iff, h0 a ha, Amount.raw_zero]
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim0 a w.self) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve0.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim0, hts, Amount.eq_iff]
      exact Nat.le_trans (hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve0.raw w.self.totalShares.raw hs hpos) hta

theorem inv_solvent1 (self : Address) (w : World Storage Ext Event)
    (h : Inv self w) : Solvent claim1 holdings1 self w := by
  obtain ⟨_, hta, ⟨H, h0, hs⟩⟩ := h
  by_cases hts : w.self.totalShares.raw = 0
  · refine ⟨H, fun a ha => by simp [claim1, hts, Amount.eq_iff],
      by simp [claim1, hts, Amount.eq_iff]⟩
  · refine ⟨H, ?_, ?_⟩
    · intro a ha; simp [claim1, hts, Amount.eq_iff, h0 a ha, Amount.raw_zero]
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim1 a w.self) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve1.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim1, hts, Amount.eq_iff]
      exact Nat.le_trans (hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve1.raw w.self.totalShares.raw hs hpos) hta

private theorem add_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {a0 : Amount token0} {a1 : Amount token1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : AddLiqOk w ctx a0 a1) :
    Inv self (worldAfter (addLiquidity a0 a1) ctx w) := by
  have hrun := addLiquidity_ok ctx w a0 a1 h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_addLiquidityPost w.self ctx.sender a0.raw a1.raw hst⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := a0.raw) hsne
    have h0n : w.self.reserve0.raw ≤ w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterPull, addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    exact Nat.add_le_add_right h0n _
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := a1.raw) hsne
    have h1n : w.self.reserve1.raw ≤ w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterPull, addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    exact Nat.add_le_add_right h1n _

private theorem remove_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {s : Amount lpShare}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : RemoveOk w ctx s) :
    Inv self (worldAfter (removeLiquidity s) ctx w) := by
  have hrun := removeLiquidity_ok ctx w s h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_removeLiquidityPost w.self ctx.sender s.raw hst h.bal⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.raw).1) hsne.symm
    have h0n : w.self.reserve0.raw ≤ w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterPush]
    rw [hb]
    have hr :
        (removeLiquidityPost w.self ctx.sender s.raw).reserve0.raw =
          w.self.reserve0.raw - (redeemed w.self s.raw).1 := by
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    exact Nat.sub_le_sub_right h0n _
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.raw).2) hsne.symm
    have h1n : w.self.reserve1.raw ≤ w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterPush]
    rw [hb]
    have hr :
        (removeLiquidityPost w.self ctx.sender s.raw).reserve1.raw =
          w.self.reserve1.raw - (redeemed w.self s.raw).2 := by
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    exact Nat.sub_le_sub_right h1n _

private theorem swap0_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount token0} {minOut : Amount token1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap0Ok w ctx dx minOut) :
    Inv self (worldAfter (swap0for1 dx minOut) ctx w) := by
  have hrun := swap0for1_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, ?_⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.raw) hsne
    have h0n : w.self.reserve0.raw ≤ w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterSwap0, swap0Post, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    exact Nat.add_le_add_right h0n _
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw) hsne.symm
    have h1n : w.self.reserve1.raw ≤ w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterSwap0]
    rw [hb]
    have hr :
        (swap0Post w.self dx.raw
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)).reserve1.raw =
          w.self.reserve1.raw -
            amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw := by
      simp [swap0Post, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    exact Nat.sub_le_sub_right h1n _
  · obtain ⟨H, h0, hs⟩ := hst
    exact ⟨H, h0, hs⟩

private theorem swap1_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount token1} {minOut : Amount token0}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap1Ok w ctx dx minOut) :
    Inv self (worldAfter (swap1for0 dx minOut) ctx w) := by
  have hrun := swap1for0_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst⟩ := hInv
  refine ⟨?_, ?_, ?_⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw) hsne.symm
    have h0n : w.self.reserve0.raw ≤ w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterSwap1]
    rw [hb]
    have hr :
        (swap1Post w.self dx.raw
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)).reserve0.raw =
          w.self.reserve0.raw -
            amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw := by
      simp [swap1Post, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    exact Nat.sub_le_sub_right h0n _
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.raw) hsne
    have h1n : w.self.reserve1.raw ≤ w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterSwap1, swap1Post, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    exact Nat.add_le_add_right h1n _
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
  simp [claim, addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
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
    exact (Nat.not_lt.mpr (claim_mono_add w.self ctx.sender a a0.raw a1.raw)) hdec

theorem removeLiquidity_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .removeLiquidity :=
  NoUnauthorizedDecreaseFn_of_ok fun s ctx w a n w' _hInv hrun hdec => by
    change ctx.sender = a
    by_cases hs : ctx.sender = a
    · exact hs
    · have hok := removeLiquidity_ok_of_run ctx w hrun
      cases hrun.symm.trans (removeLiquidity_ok ctx w s hok)
      simp [claim_frame_remove w.self ctx.sender a s.raw hs] at hdec

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


namespace Proof

theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  ⟨solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent0 self) h tr hW hR,
    solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent1 self) h tr hW hR⟩

theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (amm_no_unauth self) (amm_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Proof

end Amm

#lsc_obligations Amm
