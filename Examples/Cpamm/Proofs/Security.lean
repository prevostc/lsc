import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Tx

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
Security obligations for CPAMM. `Inv` is indexed by the pool address because
holdings read the IERC20 ghosts. `k` is a swap theorem, not `Inv`.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm

namespace Cpamm

private theorem sub_add_cancel_add {r dx proto fees : Nat} (h : proto ≤ dx) :
    r + (dx - proto) + (fees + proto) = r + dx + fees := by
  calc
    r + (dx - proto) + (fees + proto)
        = r + ((dx - proto) + proto) + fees := by ac_rfl
    _ = r + dx + fees := by rw [Nat.sub_add_cancel h]

private theorem sub_add_comm_le {a b c : Nat} (h : b ≤ a) : a - b + c = a + c - b := by
  omega

theorem inv_rely (self : Address) :
    PreservesInvEnv spec (Inv self) (cpammRely self) := by
  intro w x' ⟨h0, h1, hinv, hps⟩ ⟨hR0, hR1⟩
  obtain ⟨hb0, _⟩ := hR0
  obtain ⟨hb1, _⟩ := hR1
  refine ⟨Nat.le_trans h0 hb0, Nat.le_trans h1 hb1, hinv, hps⟩

theorem inv_covers (self : Address) (w : World Storage Ext Event)
    (h : Inv self w) : CoversLpsAndProtocol self w := by
  obtain ⟨hta0, hta1, ⟨H, hz, hs⟩, _hps⟩ := h
  refine ⟨H, hz, ?_, ?_⟩
  · by_cases hts : w.self.totalShares.raw = 0
    · have hcl : H.sum (fun a => claim0 a w.self) = 0 := by
        apply Finset.sum_eq_zero; intro a _; simp [claim0, hts, Amount.eq_iff]
      simp [hcl]
      exact Nat.le_trans (Nat.le_add_left _ _) hta0
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim0 a w.self) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve0.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim0, hts, Amount.eq_iff]
      have hsum := hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve0.raw w.self.totalShares.raw hs hpos
      exact Nat.le_trans (Nat.add_le_add_right hsum _) hta0
  · by_cases hts : w.self.totalShares.raw = 0
    · have hcl : H.sum (fun a => claim1 a w.self) = 0 := by
        apply Finset.sum_eq_zero; intro a _; simp [claim1, hts, Amount.eq_iff]
      simp [hcl]
      exact Nat.le_trans (Nat.le_add_left _ _) hta1
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim1 a w.self) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve1.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim1, hts, Amount.eq_iff]
      have hsum := hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve1.raw w.self.totalShares.raw hs hpos
      exact Nat.le_trans (Nat.add_le_add_right hsum _) hta1

private theorem add_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {a0 : Amount token0} {a1 : Amount token1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : AddLiqOk w ctx a0 a1) :
    Inv self (worldAfter (addLiquidity a0 a1) ctx w) := by
  have hrun := addLiquidity_ok ctx w a0 a1 h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst, hps⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_addLiquidityPost w.self ctx.sender a0.raw a1.raw hst, ?_⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := a0.raw) hsne
    have h0n : w.self.reserve0.raw + w.self.protocolFees0.raw ≤
        w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterPull, addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    have : (w.self.reserve0.raw + a0.raw) + w.self.protocolFees0.raw =
        (w.self.reserve0.raw + w.self.protocolFees0.raw) + a0.raw := by ac_rfl
    rw [this]
    exact Nat.add_le_add_right h0n _
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := a1.raw) hsne
    have h1n : w.self.reserve1.raw + w.self.protocolFees1.raw ≤
        w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterPull, addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
    rw [hb]
    have : (w.self.reserve1.raw + a1.raw) + w.self.protocolFees1.raw =
        (w.self.reserve1.raw + w.self.protocolFees1.raw) + a1.raw := by ac_rfl
    rw [this]
    exact Nat.add_le_add_right h1n _
  · simpa [addLiquidityPost] using hps

private theorem remove_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {s : Amount lpShare}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : RemoveOk w ctx s) :
    Inv self (worldAfter (removeLiquidity s) ctx w) := by
  have hrun := removeLiquidity_ok ctx w s h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst, hps⟩ := hInv
  refine ⟨?_, ?_, invStorage_of_removeLiquidityPost w.self ctx.sender s.raw hst h.bal, ?_⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.raw).1) hsne.symm
    have h0n : w.self.reserve0.raw + w.self.protocolFees0.raw ≤
        w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterPush]
    rw [hb]
    have hr :
        (removeLiquidityPost w.self ctx.sender s.raw).reserve0.raw +
          (removeLiquidityPost w.self ctx.sender s.raw).protocolFees0.raw =
          w.self.reserve0.raw - (redeemed w.self s.raw).1 + w.self.protocolFees0.raw := by
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    have hle := h.le0
    have : w.self.reserve0.raw - (redeemed w.self s.raw).1 + w.self.protocolFees0.raw =
        (w.self.reserve0.raw + w.self.protocolFees0.raw) - (redeemed w.self s.raw).1 :=
      sub_add_comm_le hle
    rw [this]
    exact Nat.sub_le_sub_right h0n _
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := (redeemed w.self s.raw).2) hsne.symm
    have h1n : w.self.reserve1.raw + w.self.protocolFees1.raw ≤
        w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterPush]
    rw [hb]
    have hr :
        (removeLiquidityPost w.self ctx.sender s.raw).reserve1.raw +
          (removeLiquidityPost w.self ctx.sender s.raw).protocolFees1.raw =
          w.self.reserve1.raw - (redeemed w.self s.raw).2 + w.self.protocolFees1.raw := by
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    have hle := h.le1
    have : w.self.reserve1.raw - (redeemed w.self s.raw).2 + w.self.protocolFees1.raw =
        (w.self.reserve1.raw + w.self.protocolFees1.raw) - (redeemed w.self s.raw).2 :=
      sub_add_comm_le hle
    rw [this]
    exact Nat.sub_le_sub_right h1n _
  · simpa [removeLiquidityPost] using hps

private theorem swap0_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount token0} {minOut : Amount token1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap0Ok w ctx dx minOut) :
    Inv self (worldAfter (swap0for1 dx minOut) ctx w) := by
  have hrun := swap0for1_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst, hps⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · subst hself
    have hb := move_dst (g := w.ext.token0) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.raw) hsne
    have h0n : w.self.reserve0.raw + w.self.protocolFees0.raw ≤
        w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterSwap0]
    rw [hb]
    have hr :
        (swap0Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)).reserve0.raw +
          (swap0Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)).protocolFees0.raw =
          w.self.reserve0.raw + dx.raw + w.self.protocolFees0.raw := by
      simp [swap0Post, Amount.raw_add, Amount.raw_ofWord]
      exact sub_add_cancel_add h.taken
    rw [hr]
    have : w.self.reserve0.raw + dx.raw + w.self.protocolFees0.raw =
        (w.self.reserve0.raw + w.self.protocolFees0.raw) + dx.raw := by ac_rfl
    rw [this]
    exact Nat.add_le_add_right h0n _
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw) hsne.symm
    have h1n : w.self.reserve1.raw + w.self.protocolFees1.raw ≤
        w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterSwap0]
    rw [hb]
    have hr :
        (swap0Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)).reserve1.raw +
          (swap0Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)).protocolFees1.raw =
          w.self.reserve1.raw -
            amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw +
            w.self.protocolFees1.raw := by
      simp [swap0Post, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    have hout :=
      remove_le_reserves_comm (dxFeeLess dx.raw) w.self.reserve1.raw
        (w.self.reserve0.raw + dxFeeLess dx.raw) (Nat.le_add_left _ _)
        (Nat.add_pos_left h.r0 _)
    have : w.self.reserve1.raw -
        amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw +
        w.self.protocolFees1.raw =
        (w.self.reserve1.raw + w.self.protocolFees1.raw) -
          amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw := by
      simpa [amountOut, amountOutF] using sub_add_comm_le hout
    rw [this]
    exact Nat.sub_le_sub_right h1n _
  · obtain ⟨H, hz, hs⟩ := hst
    exact ⟨H, hz, hs⟩
  · simpa [swap0Post] using hps

private theorem swap1_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    {dx : Amount token1} {minOut : Amount token0}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : Swap1Ok w ctx dx minOut) :
    Inv self (worldAfter (swap1for0 dx minOut) ctx w) := by
  have hrun := swap1for0_ok ctx w dx minOut h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst, hps⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw) hsne.symm
    have h0n : w.self.reserve0.raw + w.self.protocolFees0.raw ≤
        w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterSwap1]
    rw [hb]
    have hr :
        (swap1Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)).reserve0.raw +
          (swap1Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)).protocolFees0.raw =
          w.self.reserve0.raw -
            amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw +
            w.self.protocolFees0.raw := by
      simp [swap1Post, Amount.raw_sub, Amount.raw_ofWord]
    rw [hr]
    have hout :=
      remove_le_reserves_comm (dxFeeLess dx.raw) w.self.reserve0.raw
        (w.self.reserve1.raw + dxFeeLess dx.raw) (Nat.le_add_left _ _)
        (Nat.add_pos_left h.r1 _)
    have : w.self.reserve0.raw -
        amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw +
        w.self.protocolFees0.raw =
        (w.self.reserve0.raw + w.self.protocolFees0.raw) -
          amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw := by
      simpa [amountOut, amountOutF] using sub_add_comm_le hout
    rw [this]
    exact Nat.sub_le_sub_right h0n _
  · subst hself
    have hb := move_dst (g := w.ext.token1) (src := ctx.sender) (dst := ctx.self)
      (amt := dx.raw) hsne
    have h1n : w.self.reserve1.raw + w.self.protocolFees1.raw ≤
        w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterSwap1]
    rw [hb]
    have hr :
        (swap1Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)).reserve1.raw +
          (swap1Post w.self dx.raw (protoOf w.self dx.raw)
            (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)).protocolFees1.raw =
          w.self.reserve1.raw + dx.raw + w.self.protocolFees1.raw := by
      simp [swap1Post, Amount.raw_add, Amount.raw_ofWord]
      exact sub_add_cancel_add h.taken
    rw [hr]
    have : w.self.reserve1.raw + dx.raw + w.self.protocolFees1.raw =
        (w.self.reserve1.raw + w.self.protocolFees1.raw) + dx.raw := by ac_rfl
    rw [this]
    exact Nat.add_le_add_right h1n _
  · obtain ⟨H, hz, hs⟩ := hst
    exact ⟨H, hz, hs⟩
  · simpa [swap1Post] using hps

private theorem collect_ok_inv (self : Address) {ctx : Ctx} {w : World Storage Ext Event}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hInv : Inv self w) (h : CollectOk w ctx) :
    Inv self (worldAfter collectProtocolFees ctx w) := by
  have hrun := collectProtocolFees_ok ctx w h
  simp [worldAfter, hrun]
  obtain ⟨h0, h1, hst, hps⟩ := hInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · subst hself
    have hb := move_src (g := w.ext.token0) (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees0.raw) hsne.symm
    have h0n : w.self.reserve0.raw + w.self.protocolFees0.raw ≤
        w.ext.token0.balances ctx.self := h0
    simp [holdings0, extAfterCollect, collectPost, Amount.raw_zero]
    rw [hb]
    exact Nat.le_sub_of_add_le h0n
  · subst hself
    have hb := move_src (g := w.ext.token1) (src := ctx.self) (dst := ctx.sender)
      (amt := w.self.protocolFees1.raw) hsne.symm
    have h1n : w.self.reserve1.raw + w.self.protocolFees1.raw ≤
        w.ext.token1.balances ctx.self := h1
    simp [holdings1, extAfterCollect, collectPost, Amount.raw_zero]
    rw [hb]
    exact Nat.le_sub_of_add_le h1n
  · exact hst
  · simpa [collectPost] using hps

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

theorem setProtocolShare_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .setProtocolShare :=
  PreservesInvFnAt_of_ok fun bps ctx w _n _w' _hself _hsne hInv hrun => by
    obtain ⟨_, hle, rfl⟩ := setProtocolShare_ok_of_run ctx w hrun
    obtain ⟨h0, h1, hst, _⟩ := hInv
    exact ⟨h0, h1, hst, by simpa [BPS] using hle⟩

theorem setFeeTo_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .setFeeTo :=
  PreservesInvFnAt_of_ok fun recipient ctx w _n _w' _hself _hsne hInv hrun => by
    obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run ctx w hrun
    exact hInv

theorem collectProtocolFees_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .collectProtocolFees :=
  PreservesInvFnAt_of_ok fun _u ctx w _n _w' hself hsne hInv hrun => by
    have hI := collect_ok_inv self hself hsne hInv (collectProtocolFees_ok_of_run ctx w hrun)
    simpa [worldAfter, hrun] using hI

theorem getReserves_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .getReserves := by
  intro u ctx w _ _ hInv
  simpa [worldAfter, getReserves_ok ctx w] using hInv

theorem sharesOf_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .sharesOf := by
  intro who ctx w _ _ hInv
  simpa [worldAfter, sharesOf_ok ctx w who] using hInv

theorem protocolFees_preserves_inv (self : Address) :
    PreservesInvFnAt spec (Inv self) self .protocolFees := by
  intro u ctx w _ _ hInv
  simpa [worldAfter, protocolFees_ok ctx w] using hInv

theorem cpamm_preserves_inv (self : Address) :
    PreservesInvAt spec (Inv self) self :=
  PreservesInvAt.of_fns fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_preserves_inv self
    | .removeLiquidity => removeLiquidity_preserves_inv self
    | .swap0for1 => swap0for1_preserves_inv self
    | .swap1for0 => swap1for0_preserves_inv self
    | .setProtocolShare => setProtocolShare_preserves_inv self
    | .setFeeTo => setFeeTo_preserves_inv self
    | .collectProtocolFees => collectProtocolFees_preserves_inv self
    | .getReserves => getReserves_preserves_inv self
    | .sharesOf => sharesOf_preserves_inv self
    | .protocolFees => protocolFees_preserves_inv self

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

private theorem claim_eq_swap0 (σ : Storage) (dx proto out : Nat) (a : Address) :
    claim a (swap0Post σ dx proto out) = claim a σ := by
  simp [claim, swap0Post]

private theorem claim_eq_swap1 (σ : Storage) (dx proto out : Nat) (a : Address) :
    claim a (swap1Post σ dx proto out) = claim a σ := by
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

theorem setProtocolShare_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .setProtocolShare :=
  NoUnauthorizedDecreaseFn_of_ok fun bps ctx w a n w' _hInv hrun hdec => by
    obtain ⟨_, _, rfl⟩ := setProtocolShare_ok_of_run ctx w hrun
    simp [claim] at hdec

theorem setFeeTo_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .setFeeTo :=
  NoUnauthorizedDecreaseFn_of_ok fun recipient ctx w a n w' _hInv hrun hdec => by
    obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run ctx w hrun
    simp [claim] at hdec

theorem collectProtocolFees_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .collectProtocolFees :=
  NoUnauthorizedDecreaseFn_of_ok fun _u ctx w a n w' _hInv hrun hdec => by
    have hok := collectProtocolFees_ok_of_run ctx w hrun
    cases hrun.symm.trans (collectProtocolFees_ok ctx w hok)
    simp [claim, collectPost] at hdec

theorem getReserves_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .getReserves := by
  intro u ctx w a _hInv hdec
  simp [worldAfter, getReserves_ok ctx w, claim] at hdec

theorem sharesOf_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .sharesOf := by
  intro who ctx w a _hInv hdec
  simp [worldAfter, sharesOf_ok ctx w who, claim] at hdec

theorem protocolFees_auth (self : Address) :
    NoUnauthorizedDecreaseFn spec (Inv self) claim Auth .protocolFees := by
  intro u ctx w a _hInv hdec
  simp [worldAfter, protocolFees_ok ctx w, claim] at hdec

theorem cpamm_no_unauth (self : Address) :
    NoUnauthorizedDecrease spec (Inv self) claim Auth :=
  NoUnauthorizedDecrease.of_fns fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_auth self
    | .removeLiquidity => removeLiquidity_auth self
    | .swap0for1 => swap0for1_auth self
    | .swap1for0 => swap1for0_auth self
    | .setProtocolShare => setProtocolShare_auth self
    | .setFeeTo => setFeeTo_auth self
    | .collectProtocolFees => collectProtocolFees_auth self
    | .getReserves => getReserves_auth self
    | .sharesOf => sharesOf_auth self
    | .protocolFees => protocolFees_auth self

namespace Proof

theorem cpamm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (cpammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (cpamm_no_unauth self) (cpamm_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

theorem cpamm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (cpammRely self) tr w) (h : Inv self w) :
    CoversLpsAndProtocol self (run tr w) :=
  inv_covers self (run tr w)
    (inv_run_at (cpamm_preserves_inv self) (inv_rely self) h tr hW hR)

end Proof

end Cpamm
