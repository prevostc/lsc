import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Tx
import Stdlib.ERC20

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
Security obligations for CPAMM. `InvT` pins both token refs, the oracle,
`IERC20.Spec` on each, and `TokensIndependent`.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm

attribute [local simp] Claim.ofSelf AuthPred.ofSelf

namespace Cpamm

/-- Invariant plus callee promises, pinned to the starting tokens/oracle. -/
def InvT (self : Address) (t0 : IERC20.Ref asset0) (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState) (w : World) : Prop :=
  Inv self w ∧ w.self.token0 = t0 ∧ w.self.token1 = t1 ∧ w.oracle = oracle ∧
    IERC20.Spec (t0.impl : Token0Impl) ∧
    IERC20.Spec (t1.impl : Token1Impl) ∧
    TokensIndependent t0 t1 oracle

private theorem sub_add_cancel_add {r dx proto fees : Nat} (h : proto ≤ dx) :
    r + (dx - proto) + (fees + proto) = r + dx + fees := by
  calc
    r + (dx - proto) + (fees + proto)
        = r + ((dx - proto) + proto) + fees := by ac_rfl
    _ = r + dx + fees := by rw [Nat.sub_add_cancel h]

private theorem add_cover {r fees n H : Nat} (h : r + fees ≤ H) :
    r + n + fees ≤ H + n := by
  calc
    r + n + fees = r + fees + n := by ac_rfl
    _ ≤ H + n := Nat.add_le_add_right h n

private theorem sub_cover {r fees o H H' : Nat}
    (h : r + fees ≤ H) (hH : H' + o = H) (ho : o ≤ r) :
    r - o + fees ≤ H' := by
  have h' : r + fees ≤ H' + o := by rw [hH]; exact h
  have hL : r - o + fees + o = r + fees := by
    calc
      r - o + fees + o = r - o + o + fees := by ac_rfl
      _ = r + fees := by rw [Nat.sub_add_cancel ho]
  exact Nat.le_of_add_le_add_right (hL.symm ▸ h')

private theorem collect_cover {r fees H H' : Nat}
    (h : r + fees ≤ H) (hH : H' + fees = H) :
    r + 0 ≤ H' := by
  have : r + fees ≤ H' + fees := by rw [hH]; exact h
  simpa using Nat.le_of_add_le_add_right this

/-! ### Environment -/

theorem inv_rely (self : Address) (t0 : IERC20.Ref asset0) (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState) :
    PreservesInvEnv spec (InvT self t0 t1 oracle)
      (cpammRely self t0 t1 oracle) := by
  intro w x' ⟨⟨h0, h1, hinv, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ ⟨hR0, hR1, _, _⟩
  refine ⟨⟨?_, ?_, hinv, hps⟩, ht0, ht1, ho, ?_, ?_, hInd⟩
  · rw [holdings0_view, ht0, ho] at h0 ⊢
    exact Nat.le_trans h0 hR0
  · rw [holdings1_view, ht1, ho] at h1 ⊢
    exact Nat.le_trans h1 hR1
  · simpa [IERC20.Ref.impl] using hT0
  · simpa [IERC20.Ref.impl] using hT1

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

private theorem invStorage_shares_zero {σ : Storage} (h : InvStorage σ)
    (hts : σ.totalShares.raw = 0) (a : Address) : (σ.shares a).raw = 0 := by
  obtain ⟨H, h0, hsum⟩ := h
  rw [hts] at hsum
  by_cases ha : a ∈ H
  · have hle := Finset.single_le_sum (s := H) (f := fun x => (σ.shares x).raw)
      (fun _ _ => Nat.zero_le _) ha
    rw [hsum] at hle
    exact Nat.eq_zero_of_le_zero hle
  · have := h0 a ha
    simpa [Amount.eq_iff] using this

private theorem invStorage_of_addLiquidityPost (σ : Storage) (who : Address)
    (a0 a1 : Nat) (hInv : InvStorage σ) :
    InvStorage (addLiquidityPost σ who a0 a1) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  by_cases hts : σ.totalShares.raw = 0
  · have hz : ∀ a, (σ.shares a).raw = 0 :=
      invStorage_shares_zero ⟨H, h0, hsum⟩ hts
    have hdead : deadShares σ = 1000 := by simp [hts]
    have hsh0 : sharesAfterDead σ 0 = ⟨1000⟩ := by
      simp [sharesAfterDead, hts, Function.update, hz]
    by_cases hw : who = (0 : Address)
    · refine ⟨({0} : Finset Address), ?_, ?_⟩
      · intro a ha
        have hne : a ≠ (0 : Address) := by simpa [Finset.mem_singleton] using ha
        have hnew : (addLiquidityPost σ who a0 a1).shares a = σ.shares a := by
          subst hw
          simp [addLiquidityPost, sharesAfterDead, hts, Function.update, hne]
        have := hz a
        simpa [hnew, Amount.eq_iff] using this
      · subst hw
        simp [addLiquidityPost, sharesAfterDead, hts, deadShares, Function.update,
          Amount.raw_add, Amount.raw_ofWord, Finset.sum_singleton, hz, hdead,
          Nat.add_comm]
    · have hpair : (0 : Address) ≠ who := by intro h; exact hw h.symm
      refine ⟨({0, who} : Finset Address), ?_, ?_⟩
      · intro a ha
        have ha0 : a ≠ (0 : Address) := by
          intro h; subst h; exact ha (by simp)
        have haw : a ≠ who := by
          intro h; subst h; exact ha (by simp)
        have hnew : (addLiquidityPost σ who a0 a1).shares a = σ.shares a := by
          simp [addLiquidityPost, sharesAfterDead, hts, Function.update, ha0, haw]
        have := hz a
        simpa [hnew, Amount.eq_iff] using this
      · have hsum' :
            ({0, who} : Finset Address).sum
                (rawShares (addLiquidityPost σ who a0 a1).shares) =
              1000 + mintedShares σ a0 a1 := by
          rw [Finset.sum_pair hpair]
          simp [addLiquidityPost, sharesAfterDead, hts, Function.update, hw,
            Amount.raw_add, Amount.raw_ofWord, hz, hsh0, Ne.symm hw]
        change ({0, who} : Finset Address).sum
            (fun a => (addLiquidityPost σ who a0 a1).shares a |>.raw) =
          (addLiquidityPost σ who a0 a1).totalShares.raw
        rw [hsum']
        simp [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord, hts, hdead]
        exact Nat.add_comm _ _
  · have hdead : deadShares σ = 0 := by simp [hts]
    have hsh : sharesAfterDead σ = σ.shares := by simp [sharesAfterDead, hts]
    by_cases ht : who ∈ H
    · refine ⟨H, ?_, ?_⟩
      · intro a ha
        have hne : a ≠ who := by intro h; subst h; exact ha ht
        simp [addLiquidityPost, hsh, Function.update_of_ne hne]
        exact h0 a ha
      · have hsum' :
            H.sum (rawShares (addLiquidityPost σ who a0 a1).shares) =
              H.sum (rawShares σ.shares) + mintedShares σ a0 a1 := by
          simp only [addLiquidityPost, hsh, rawShares_update, Amount.raw_add,
            Amount.raw_ofWord]
          exact nat_sum_update_add H (rawShares σ.shares) ht (mintedShares σ a0 a1)
        change H.sum (rawShares (addLiquidityPost σ who a0 a1).shares) =
          (addLiquidityPost σ who a0 a1).totalShares.raw
        rw [hsum', hsumr]
        simp [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord, hdead, Nat.add_comm]
    · refine ⟨insert who H, ?_, ?_⟩
      · intro a ha
        have hat : a ≠ who := by
          intro h; subst h; exact ha (Finset.mem_insert_self _ _)
        have haH : a ∉ H := fun hH => ha (Finset.mem_insert_of_mem hH)
        simp [addLiquidityPost, hsh, Function.update_of_ne hat]
        exact h0 a haH
      · have hb0 : σ.shares who = 0 := h0 who ht
        have hwho0 : (σ.shares who).raw = 0 := by
          simpa [Amount.eq_iff] using hb0
        have hupd :
            (fun x =>
              (Function.update σ.shares who
                (σ.shares who + Amount.ofWord (mintedShares σ a0 a1)) x).raw) =
              Function.update (rawShares σ.shares) who
                ((σ.shares who).raw + mintedShares σ a0 a1) := by
          funext x
          by_cases hx : x = who <;>
            simp [rawShares, Function.update, hx, Amount.raw_add, Amount.raw_ofWord]
        have hframe :=
          sum_update_not_mem H (rawShares σ.shares) ht
            ((σ.shares who).raw + mintedShares σ a0 a1)
        have hframe' :
            H.sum (Function.update (rawShares σ.shares) who
                (mintedShares σ a0 a1)) =
              H.sum (rawShares σ.shares) := by
          simpa [hwho0, Nat.zero_add] using hframe
        have hsum' :
            (∑ a ∈ insert who H,
                rawShares (addLiquidityPost σ who a0 a1).shares a) =
              H.sum (rawShares σ.shares) + mintedShares σ a0 a1 := by
          rw [Finset.sum_insert ht]
          simp only [addLiquidityPost, hsh, Function.update_self, rawShares,
            Amount.raw_add, Amount.raw_ofWord]
          simp [hupd, hframe', hwho0, Nat.add_comm]
        change (∑ a ∈ insert who H,
            ((addLiquidityPost σ who a0 a1).shares a).raw) =
          (addLiquidityPost σ who a0 a1).totalShares.raw
        rw [hsum', hsumr]
        simp [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord, hdead, Nat.add_comm]

private theorem invStorage_of_removeLiquidityPost (σ : Storage) (who : Address)
    (s : Nat) (hInv : InvStorage σ) (hn : Amount.ofWord s ≤ σ.shares who) :
    InvStorage (removeLiquidityPost σ who s) := by
  obtain ⟨H, h0, hsum⟩ := hInv
  have hsumr : H.sum (rawShares σ.shares) = σ.totalShares.raw := hsum
  have hn' : s ≤ (σ.shares who).raw := by simpa [Amount.le_iff, Amount.raw_ofWord] using hn
  by_cases hs : who ∈ H
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      have ha_src : a ≠ who := by intro h; subst h; exact ha hs
      simp [removeLiquidityPost, Function.update_of_ne ha_src]
      exact h0 a ha
    · have hsumd :
          H.sum (rawShares (removeLiquidityPost σ who s).shares) =
            H.sum (rawShares σ.shares) - s := by
        simp only [removeLiquidityPost, rawShares_update, Amount.raw_sub, Amount.raw_ofWord]
        exact nat_sum_update_sub H (rawShares σ.shares) hs hn'
      change H.sum (rawShares (removeLiquidityPost σ who s).shares) =
        (removeLiquidityPost σ who s).totalShares.raw
      rw [hsumd, hsumr]
      simp [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
  · have hb0 : σ.shares who = 0 := h0 who hs
    have hn0 : s = 0 :=
      Nat.eq_zero_of_le_zero (by
        have hwho0 : (σ.shares who).raw = 0 := by
          simpa [Amount.raw_ofNat] using congrArg Amount.raw hb0
        exact hn'.trans_eq hwho0)
    refine ⟨H, ?_, ?_⟩
    · intro a ha
      simp [removeLiquidityPost, hn0]
      exact h0 a ha
    · simp [removeLiquidityPost, hn0, hsum]

theorem inv_covers (self : Address) (w : World)
    (h : Inv self w) : CoversLpsAndProtocol self w := by
  obtain ⟨hta0, hta1, ⟨H, hz, hs⟩, _hps⟩ := h
  refine ⟨H, hz, ?_, ?_⟩
  · by_cases hts : w.self.totalShares.raw = 0
    · have hcl : H.sum (fun a => claim0 a w) = 0 := by
        apply Finset.sum_eq_zero; intro a _; simp [claim0, hts, Amount.eq_iff]
      simp [hcl]
      exact Nat.le_trans (Nat.le_add_left _ _) hta0
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim0 a w) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve0.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim0, hts, Amount.eq_iff]
      have hsum := hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve0.raw w.self.totalShares.raw hs hpos
      exact Nat.le_trans (Nat.add_le_add_right hsum _) hta0
  · by_cases hts : w.self.totalShares.raw = 0
    · have hcl : H.sum (fun a => claim1 a w) = 0 := by
        apply Finset.sum_eq_zero; intro a _; simp [claim1, hts, Amount.eq_iff]
      simp [hcl]
      exact Nat.le_trans (Nat.le_add_left _ _) hta1
    · have hpos : 0 < w.self.totalShares.raw := Nat.pos_of_ne_zero hts
      have hcl : H.sum (fun a => claim1 a w) =
          H.sum (fun a => (w.self.shares a).raw * w.self.reserve1.raw /
            w.self.totalShares.raw) := by
        apply Finset.sum_congr rfl; intro a _; simp [claim1, hts, Amount.eq_iff]
      have hsum := hcl.symm ▸ sum_mul_div_le H (fun a => (w.self.shares a).raw)
        w.self.reserve1.raw w.self.totalShares.raw hs hpos
      exact Nat.le_trans (Nat.add_le_add_right hsum _) hta1

/-! ### Holdings along CALLs -/

private theorem holdings0_add_of_transferFrom
    (self : Address) {ctx : Ctx} {w w1 : World}
    {amt : Amount asset0}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.token0.impl : Token0Impl))
    (hcall : Tx.run (tfCall w.self.token0 ctx.sender ctx.self amt) ctx w =
      .ok (true, w1)) :
    holdings0 self w1 = holdings0 self w + amt.raw := by
  subst hself
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w.view) (w' := w1.view)
    (by
      have hopt := Tx.run_ok_toOption hcall
      have := congrArg (Option.map (Prod.map id World.view)) hopt
      simpa [impl_transferFrom] using this)
  have hdst := hmoves.2.1 hsne
  have hframe := transferFrom_frame hcall
  simp [holdings0, IERC20.Ref.impl, World.view] at hdst ⊢
  simp [hframe.1, hframe.2.1] at hdst ⊢
  simpa [Amount.raw_add] using congrArg Amount.raw hdst

private theorem holdings1_add_of_transferFrom
    (self : Address) {ctx : Ctx} {w w1 : World}
    {amt : Amount asset1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (w.self.token1.impl : Token1Impl))
    (hcall : Tx.run (tfCall w.self.token1 ctx.sender ctx.self amt) ctx w =
      .ok (true, w1)) :
    holdings1 self w1 = holdings1 self w + amt.raw := by
  subst hself
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w.view) (w' := w1.view)
    (by
      have hopt := Tx.run_ok_toOption hcall
      have := congrArg (Option.map (Prod.map id World.view)) hopt
      simpa [impl_transferFrom] using this)
  have hdst := hmoves.2.1 hsne
  have hframe := transferFrom_frame hcall
  simp [holdings1, IERC20.Ref.impl, World.view] at hdst ⊢
  simp [hframe.1, hframe.2.1] at hdst ⊢
  simpa [Amount.raw_add] using congrArg Amount.raw hdst

private theorem holdings0_sub_of_transfer
    (self : Address) {ctx : Ctx} {wCall w1 : World}
    {amt : Amount asset0}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (wCall.self.token0.impl : Token0Impl))
    (hcall : Tx.run (trCall wCall.self.token0 ctx.sender amt) ctx wCall =
      .ok (true, w1)) :
    holdings0 self w1 + amt.raw = holdings0 self wCall := by
  subst hself
  have hrunT :
      wCall.self.token0.impl.transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall.view =
        some (true, w1.view) := by
    have htr' :
        Tx.run (trCall wCall.self.token0 ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := wCall.self.token0) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      exact hcall
    have hopt := Tx.run_ok_toOption htr'
    have := congrArg (Option.map (Prod.map id World.view)) hopt
    simpa [impl_transfer (r := wCall.self.token0)
        (ctx := { ctx with sender := ctx.self }) (w := wCall)] using this
  have hmoves := hT.transfer_moves hrunT
  have hto := hmoves.2.1 hsne.symm
  have hsumr := congrArg Amount.raw hmoves.1
  rw [Amount.raw_add, Amount.raw_add] at hsumr
  simp at hsumr
  have htor := congrArg Amount.raw hto
  simp [Amount.raw_add] at htor
  have hframe := transfer_frame (w := wCall) hcall
  simp [holdings0, IERC20.Ref.impl, hframe.1, hframe.2.1, World.view] at hsumr htor ⊢
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

private theorem holdings1_sub_of_transfer
    (self : Address) {ctx : Ctx} {wCall w1 : World}
    {amt : Amount asset1}
    (hself : ctx.self = self) (hsne : ctx.sender ≠ self)
    (hT : IERC20.Spec (wCall.self.token1.impl : Token1Impl))
    (hcall : Tx.run (trCall wCall.self.token1 ctx.sender amt) ctx wCall =
      .ok (true, w1)) :
    holdings1 self w1 + amt.raw = holdings1 self wCall := by
  subst hself
  have hrunT :
      wCall.self.token1.impl.transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall.view =
        some (true, w1.view) := by
    have htr' :
        Tx.run (trCall wCall.self.token1 ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := wCall.self.token1) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      exact hcall
    have hopt := Tx.run_ok_toOption htr'
    have := congrArg (Option.map (Prod.map id World.view)) hopt
    simpa [impl_transfer (r := wCall.self.token1)
        (ctx := { ctx with sender := ctx.self }) (w := wCall)] using this
  have hmoves := hT.transfer_moves hrunT
  have hto := hmoves.2.1 hsne.symm
  have hsumr := congrArg Amount.raw hmoves.1
  rw [Amount.raw_add, Amount.raw_add] at hsumr
  simp at hsumr
  have htor := congrArg Amount.raw hto
  simp [Amount.raw_add] at htor
  have hframe := transfer_frame (w := wCall) hcall
  simp [holdings1, IERC20.Ref.impl, hframe.1, hframe.2.1, World.view] at hsumr htor ⊢
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

private theorem holdings1_frame_token0
    (self : Address) {w w1 : World}
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (hcall : ∃ sel args rets,
      w.oracle.call w.self.token0.addr sel args w.ext = some (rets, w1.ext))
    (hs : w1.self = w.self) (ho : w1.oracle = w.oracle) :
    holdings1 self w1 = holdings1 self w := by
  obtain ⟨sel, args, rets, hc⟩ := hcall
  have hview := hInd.2.1 sel args w.ext rets w1.ext hc
  rw [holdings1_view (w := w1), holdings1_view (w := w)]
  simp [viewBal1, hs, ho]
  exact congrArg (fun rets => (decodeOrDefault (α := Amount asset1) rets).raw)
    (hview balSel1 [AbiType.encode self])

private theorem holdings0_frame_token1
    (self : Address) {w w1 : World}
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (hcall : ∃ sel args rets,
      w.oracle.call w.self.token1.addr sel args w.ext = some (rets, w1.ext))
    (hs : w1.self = w.self) (ho : w1.oracle = w.oracle) :
    holdings0 self w1 = holdings0 self w := by
  obtain ⟨sel, args, rets, hc⟩ := hcall
  have hview := hInd.2.2 sel args w.ext rets w1.ext hc
  rw [holdings0_view (w := w1), holdings0_view (w := w)]
  simp [viewBal0, hs, ho]
  exact congrArg (fun rets => (decodeOrDefault (α := Amount asset0) rets).raw)
    (hview balSel0 [AbiType.encode self])

/-! ### Invariant preservation -/

variable (self : Address) (t0 : IERC20.Ref asset0) (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState)

theorem addLiquidity_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .addLiquidity :=
  PreservesInvFnAt_of_ok fun ⟨a0, a1⟩ ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨h0, h1, hst, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    have hok := addLiquidity_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := addLiquidity_post a0 a1 hok hrun
    obtain ⟨w1, w2, htf0, htf1, hs1, ho1, hl1, hs2, ho2, hext, _, hσ'⟩ :=
      addLiquidity_call a0 a1 hok hrun
    have hT0' : IERC20.Spec (w.self.token0.impl : Token0Impl) := by
      simpa [IERC20.Ref.impl, ht0] using hT0
    have hhold0 := holdings0_add_of_transferFrom self hself hsne hT0' htf0
    have hIndw : TokensIndependent w.self.token0 w.self.token1 w.oracle := by
      simpa [ht0, ht1, ho] using hInd
    have hframe1 := holdings1_frame_token0 self (w := w) (w1 := w1) hIndw
      (transferFrom_call_addr htf0) hs1 ho1
    have hT1' : IERC20.Spec (w.self.token1.impl : Token1Impl) := by
      simpa [IERC20.Ref.impl, ht1] using hT1
    have hhold1 := holdings1_add_of_transferFrom self
      (w := { w with ext := w1.ext }) hself hsne hT1' (by simpa [ht1] using htf1)
    have hw1 : w1 = { w with ext := w1.ext } :=
      eq_self_ext (σ := w.self) hs1 ho1 hl1
    have hInd1 : TokensIndependent w1.self.token0 w1.self.token1 w1.oracle := by
      simpa [hs1, ho1] using hIndw
    have hhold0_frame : holdings0 self w2 = holdings0 self w1 :=
      holdings0_frame_token1 self (w := w1) (w1 := w2) hInd1
        (by
          rw [hw1]
          exact transferFrom_call_addr (w := { w with ext := w1.ext }) htf1)
        (hs2.trans hs1.symm) (ho2.trans ho1.symm)
    have hhold0' : holdings0 self w' = holdings0 self w2 :=
      holdings0_congr self (by rw [hσ, hs2]; rfl)
        (hor.trans ho2.symm) hext
    have hhold1' : holdings1 self w' = holdings1 self w2 :=
      holdings1_congr self (by rw [hσ, hs2]; rfl)
        (hor.trans ho2.symm) hext
    refine ⟨⟨?_, ?_, hσ ▸ invStorage_of_addLiquidityPost w.self ctx.sender a0.raw a1.raw hst,
        ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ]
      simp only [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
      rw [hhold0', hhold0_frame, hhold0]
      exact add_cover (n := a0.raw) h0
    · rw [hσ]
      simp only [addLiquidityPost, Amount.raw_add, Amount.raw_ofWord]
      rw [hhold1', hhold1, ← hw1, hframe1]
      exact add_cover (n := a1.raw) h1
    · simpa [hσ, addLiquidityPost] using hps
    · simpa [hσ, addLiquidityPost] using ht0
    · simpa [hσ, addLiquidityPost] using ht1
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, addLiquidityPost, ht0] using hT0
    · simpa [IERC20.Ref.impl, hσ, addLiquidityPost, ht1] using hT1
    · simpa [ht0, ht1, ho] using hInd

theorem removeLiquidity_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .removeLiquidity :=
  PreservesInvFnAt_of_ok fun s ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨h0, h1, hst, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    have hok := removeLiquidity_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := removeLiquidity_post s hok hrun
    obtain ⟨w1, w2, htr0, htr1, hs1, ho1, hl1, hs2, ho2, hext, _, _⟩ :=
      removeLiquidity_call s hok hrun
    set out0 := Amount.ofWord (redeemed w.self s.raw).1
    set out1 := Amount.ofWord (redeemed w.self s.raw).2
    have hT0' : IERC20.Spec (w.self.token0.impl : Token0Impl) := by
      simpa [IERC20.Ref.impl, ht0] using hT0
    have hhold0 := holdings0_sub_of_transfer self hself hsne hT0'
      (wCall := w) (by simpa [out0] using htr0)
    have hT1call : IERC20.Spec (w.self.token1.impl : Token1Impl) := by
      simpa [IERC20.Ref.impl, ht1] using hT1
    have hhold1 := holdings1_sub_of_transfer self hself hsne hT1call
      (wCall := { w with ext := w1.ext }) (by simpa [out1] using htr1)
    have hIndw : TokensIndependent w.self.token0 w.self.token1 w.oracle := by
      simpa [ht0, ht1, ho] using hInd
    have hframe1 := holdings1_frame_token0 self (w := w) (w1 := w1) hIndw
      (transfer_call_addr (by simpa [out0] using htr0)) hs1 ho1
    have hw1 : w1 = { w with ext := w1.ext } :=
      eq_self_ext (σ := w.self) hs1 ho1 hl1
    have hInd1 : TokensIndependent w1.self.token0 w1.self.token1 w1.oracle := by
      simpa [hs1, ho1] using hIndw
    have hhold0_frame : holdings0 self w2 = holdings0 self w1 :=
      holdings0_frame_token1 self (w := w1) (w1 := w2) hInd1
        (by
          rw [hw1]
          exact transfer_call_addr (w := { w with ext := w1.ext }) htr1)
        (hs2.trans hs1.symm) (ho2.trans ho1.symm)
    have hhold0' : holdings0 self w' = holdings0 self w2 :=
      holdings0_congr self (by rw [hσ, hs2]; rfl)
        (hor.trans ho2.symm) hext
    have hhold1' : holdings1 self w' = holdings1 self w2 :=
      holdings1_congr self (by rw [hσ, hs2]; rfl)
        (hor.trans ho2.symm) hext
    refine ⟨⟨?_, ?_, hσ ▸ invStorage_of_removeLiquidityPost w.self ctx.sender s.raw hst
        hok.bal, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ]
      simp only [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
      have h0w : holdings0 self w' + out0.raw = holdings0 self w := by
        rw [hhold0', hhold0_frame]; exact hhold0
      exact sub_cover h0 h0w (by simpa [out0, Amount.raw_ofWord] using hok.le0)
    · rw [hσ]
      simp only [removeLiquidityPost, Amount.raw_sub, Amount.raw_ofWord]
      have h1w : holdings1 self w' + out1.raw = holdings1 self w := by
        rw [hhold1', hhold1, ← hw1, hframe1]
      exact sub_cover h1 h1w (by simpa [out1, Amount.raw_ofWord] using hok.le1)
    · simpa [hσ, removeLiquidityPost] using hps
    · simpa [hσ, removeLiquidityPost] using ht0
    · simpa [hσ, removeLiquidityPost] using ht1
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, removeLiquidityPost, ht0] using hT0
    · simpa [IERC20.Ref.impl, hσ, removeLiquidityPost, ht1] using hT1
    · simpa [ht0, ht1, ho] using hInd

theorem swap0for1_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .swap0for1 :=
  PreservesInvFnAt_of_ok fun ⟨dx, minOut⟩ ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨h0, h1, hst, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    have hok := swap0for1_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := swap0for1_post dx minOut hok hrun
    obtain ⟨w1, w2, htf0, htr1, hs1, ho1, hl1, hs2, ho2, hext, _, _⟩ :=
      swap0for1_call dx minOut hok hrun
    set amt := Amount.ofWord (amountOut w.self.reserve0.raw w.self.reserve1.raw dx.raw)
    have hT0' : IERC20.Spec (w.self.token0.impl : Token0Impl) := by
      simpa [IERC20.Ref.impl, ht0] using hT0
    have hhold0 := holdings0_add_of_transferFrom self hself hsne hT0' htf0
    have hIndw : TokensIndependent w.self.token0 w.self.token1 w.oracle := by
      simpa [ht0, ht1, ho] using hInd
    have hframe1 := holdings1_frame_token0 self (w := w) (w1 := w1) hIndw
      (transferFrom_call_addr htf0) hs1 ho1
    have hT1call : IERC20.Spec (w.self.token1.impl : Token1Impl) := by
      simpa [IERC20.Ref.impl, ht1] using hT1
    have hhold1 := holdings1_sub_of_transfer self hself hsne hT1call
      (wCall := { w with ext := w1.ext }) (by simpa [amt] using htr1)
    have hw1 : w1 = { w with ext := w1.ext } :=
      eq_self_ext (σ := w.self) hs1 ho1 hl1
    have hInd1 : TokensIndependent w1.self.token0 w1.self.token1 w1.oracle := by
      simpa [hs1, ho1] using hIndw
    have hhold0_frame : holdings0 self w2 = holdings0 self w1 :=
      holdings0_frame_token1 self (w := w1) (w1 := w2) hInd1
        (by
          rw [hw1]
          exact transfer_call_addr (w := { w with ext := w1.ext }) htr1)
        (hs2.trans hs1.symm) (ho2.trans ho1.symm)
    have hhold0' : holdings0 self w' = holdings0 self w2 :=
      holdings0_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    have hhold1' : holdings1 self w' = holdings1 self w2 :=
      holdings1_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    refine ⟨⟨?_, ?_, hσ ▸ hst, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ]
      simp only [swap0Post, Amount.raw_add, Amount.raw_ofWord]
      have htaken := hok.taken
      have hsum := sub_add_cancel_add (r := w.self.reserve0.raw) (dx := dx.raw)
          (proto := protoOf w.self dx.raw) (fees := w.self.protocolFees0.raw) htaken
      have h0w : holdings0 self w' = holdings0 self w + dx.raw := by
        rw [hhold0', hhold0_frame, hhold0]
      rw [hsum, h0w]
      exact add_cover (n := dx.raw) h0
    · have hout :=
        remove_le_reserves_comm (dxFeeLess dx.raw) w.self.reserve1.raw
          (w.self.reserve0.raw + dxFeeLess dx.raw) (Nat.le_add_left _ _)
          (Nat.add_pos_left hok.r0 _)
      rw [hσ]
      simp only [swap0Post, Amount.raw_sub, Amount.raw_ofWord]
      have h1w : holdings1 self w' + amt.raw = holdings1 self w := by
        rw [hhold1', hhold1, ← hw1, hframe1]
      have hout' : (amt.raw : Nat) ≤ w.self.reserve1.raw := by
        simp only [amt, Amount.raw_ofWord, amountOut]
        exact hout
      exact sub_cover h1 h1w hout'
    · simpa [hσ, swap0Post] using hps
    · simpa [hσ, swap0Post] using ht0
    · simpa [hσ, swap0Post] using ht1
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, swap0Post, ht0] using hT0
    · simpa [IERC20.Ref.impl, hσ, swap0Post, ht1] using hT1
    · simpa [ht0, ht1, ho] using hInd

theorem swap1for0_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .swap1for0 :=
  PreservesInvFnAt_of_ok fun ⟨dx, minOut⟩ ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨h0, h1, hst, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    have hok := swap1for0_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := swap1for0_post dx minOut hok hrun
    obtain ⟨w1, w2, htf1, htr0, hs1, ho1, hl1, hs2, ho2, hext, _, _⟩ :=
      swap1for0_call dx minOut hok hrun
    set amt := Amount.ofWord (amountOut w.self.reserve1.raw w.self.reserve0.raw dx.raw)
    have hT1' : IERC20.Spec (w.self.token1.impl : Token1Impl) := by
      simpa [IERC20.Ref.impl, ht1] using hT1
    have hhold1 := holdings1_add_of_transferFrom self hself hsne hT1' htf1
    have hIndw : TokensIndependent w.self.token0 w.self.token1 w.oracle := by
      simpa [ht0, ht1, ho] using hInd
    have hframe0 := holdings0_frame_token1 self (w := w) (w1 := w1) hIndw
      (transferFrom_call_addr htf1) hs1 ho1
    have hT0call : IERC20.Spec (w.self.token0.impl : Token0Impl) := by
      simpa [IERC20.Ref.impl, ht0] using hT0
    have hhold0 := holdings0_sub_of_transfer self hself hsne hT0call
      (wCall := { w with ext := w1.ext }) (by simpa [amt] using htr0)
    have hw1 : w1 = { w with ext := w1.ext } :=
      eq_self_ext (σ := w.self) hs1 ho1 hl1
    have hInd1 : TokensIndependent w1.self.token0 w1.self.token1 w1.oracle := by
      simpa [hs1, ho1] using hIndw
    have hhold1_frame : holdings1 self w2 = holdings1 self w1 :=
      holdings1_frame_token0 self (w := w1) (w1 := w2) hInd1
        (by
          rw [hw1]
          exact transfer_call_addr (w := { w with ext := w1.ext }) htr0)
        (hs2.trans hs1.symm) (ho2.trans ho1.symm)
    have hhold0' : holdings0 self w' = holdings0 self w2 :=
      holdings0_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    have hhold1' : holdings1 self w' = holdings1 self w2 :=
      holdings1_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    refine ⟨⟨?_, ?_, hσ ▸ hst, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hout :=
        remove_le_reserves_comm (dxFeeLess dx.raw) w.self.reserve0.raw
          (w.self.reserve1.raw + dxFeeLess dx.raw) (Nat.le_add_left _ _)
          (Nat.add_pos_left hok.r1 _)
      rw [hσ]
      simp only [swap1Post, Amount.raw_sub, Amount.raw_ofWord]
      have h0w : holdings0 self w' + amt.raw = holdings0 self w := by
        rw [hhold0', hhold0, ← hw1, hframe0]
      have hout' : (amt.raw : Nat) ≤ w.self.reserve0.raw := by
        simp only [amt, Amount.raw_ofWord, amountOut]
        exact hout
      exact sub_cover h0 h0w hout'
    · rw [hσ]
      simp only [swap1Post, Amount.raw_add, Amount.raw_ofWord]
      have htaken := hok.taken
      have hsum := sub_add_cancel_add (r := w.self.reserve1.raw) (dx := dx.raw)
          (proto := protoOf w.self dx.raw) (fees := w.self.protocolFees1.raw) htaken
      have h1w : holdings1 self w' = holdings1 self w + dx.raw := by
        rw [hhold1', hhold1_frame, hhold1]
      rw [hsum, h1w]
      exact add_cover (n := dx.raw) h1
    · simpa [hσ, swap1Post] using hps
    · simpa [hσ, swap1Post] using ht0
    · simpa [hσ, swap1Post] using ht1
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, swap1Post, ht0] using hT0
    · simpa [IERC20.Ref.impl, hσ, swap1Post, ht1] using hT1
    · simpa [ht0, ht1, ho] using hInd

theorem setProtocolShare_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .setProtocolShare :=
  PreservesInvFnAt_of_ok fun bps ctx w _n w' _hself _hsne hInvT hrun => by
    obtain ⟨_, hle, rfl⟩ := setProtocolShare_ok_of_run hrun
    obtain ⟨⟨h0, h1, hst, _⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    exact ⟨⟨h0, h1, hst, hle⟩, ht0, ht1, ho, hT0, hT1, hInd⟩

theorem setFeeTo_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .setFeeTo :=
  PreservesInvFnAt_of_ok fun recipient ctx w _n w' _hself _hsne hInvT hrun => by
    obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run hrun
    exact hInvT

theorem collectProtocolFees_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .collectProtocolFees :=
  PreservesInvFnAt_of_ok fun _u ctx w _n w' hself hsne hInvT hrun => by
    obtain ⟨⟨h0, h1, hst, hps⟩, ht0, ht1, ho, hT0, hT1, hInd⟩ := hInvT
    have hok := collectProtocolFees_ok_of_run hrun
    obtain ⟨_, hσ, hor, _⟩ := collectProtocolFees_post hok hrun
    obtain ⟨w1, w2, htr0, htr1, hs1, ho1, hl1, hs2, ho2, hext, _, _⟩ :=
      collectProtocolFees_call hok hrun
    have hT0' : IERC20.Spec (w.self.token0.impl : Token0Impl) := by
      simpa [IERC20.Ref.impl, ht0] using hT0
    have hhold0 := holdings0_sub_of_transfer self hself hsne hT0'
      (wCall := w) htr0
    have hT1call : IERC20.Spec (w.self.token1.impl : Token1Impl) := by
      simpa [IERC20.Ref.impl, ht1] using hT1
    have hhold1 := holdings1_sub_of_transfer self hself hsne hT1call
      (wCall := { w with ext := w1.ext }) htr1
    have hIndw : TokensIndependent w.self.token0 w.self.token1 w.oracle := by
      simpa [ht0, ht1, ho] using hInd
    have hframe1 := holdings1_frame_token0 self (w := w) (w1 := w1) hIndw
      (transfer_call_addr htr0) hs1 ho1
    have hw1 : w1 = { w with ext := w1.ext } :=
      eq_self_ext (σ := w.self) hs1 ho1 hl1
    have hInd1 : TokensIndependent w1.self.token0 w1.self.token1 w1.oracle := by
      simpa [hs1, ho1] using hIndw
    have hhold0_frame : holdings0 self w2 = holdings0 self w1 :=
      holdings0_frame_token1 self (w := w1) (w1 := w2) hInd1
        (by
          rw [hw1]
          exact transfer_call_addr (w := { w with ext := w1.ext }) htr1)
        (hs2.trans hs1.symm) (ho2.trans ho1.symm)
    have hhold0' : holdings0 self w' = holdings0 self w2 :=
      holdings0_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    have hhold1' : holdings1 self w' = holdings1 self w2 :=
      holdings1_congr self (by rw [hσ, hs2]; rfl) (hor.trans ho2.symm) hext
    refine ⟨⟨?_, ?_, hσ ▸ hst, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ]
      simp only [collectPost, Amount.raw_ofNat]
      have h0w : holdings0 self w' + w.self.protocolFees0.raw = holdings0 self w := by
        rw [hhold0', hhold0_frame]; exact hhold0
      exact collect_cover h0 h0w
    · rw [hσ]
      simp only [collectPost, Amount.raw_ofNat]
      have h1w : holdings1 self w' + w.self.protocolFees1.raw = holdings1 self w := by
        rw [hhold1', hhold1, ← hw1, hframe1]
      exact collect_cover h1 h1w
    · simpa [hσ, collectPost] using hps
    · simpa [hσ, collectPost] using ht0
    · simpa [hσ, collectPost] using ht1
    · simpa [hor] using ho
    · simpa [IERC20.Ref.impl, hσ, collectPost, ht0] using hT0
    · simpa [IERC20.Ref.impl, hσ, collectPost, ht1] using hT1
    · simpa [ht0, ht1, ho] using hInd

theorem getReserves_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .getReserves := by
  intro u ctx w _ _ hInvT
  cases u
  unfold worldAfter
  rw [spec_exec_getReserves, getReserves_ok]
  exact hInvT

theorem sharesOf_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .sharesOf := by
  intro who ctx w _ _ hInvT
  unfold worldAfter
  rw [spec_exec_sharesOf, sharesOf_ok]
  exact hInvT

theorem protocolFees_preserves_inv :
    PreservesInvFnAt spec (InvT self t0 t1 oracle) self .protocolFees := by
  intro u ctx w _ _ hInvT
  cases u
  unfold worldAfter
  rw [spec_exec_protocolFees, protocolFees_ok]
  exact hInvT

theorem cpamm_preserves_inv :
    PreservesInvAt spec (InvT self t0 t1 oracle) self :=
  PreservesInvAt.of_fns (C := spec) fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_preserves_inv self t0 t1 oracle
    | .removeLiquidity => removeLiquidity_preserves_inv self t0 t1 oracle
    | .swap0for1 => swap0for1_preserves_inv self t0 t1 oracle
    | .swap1for0 => swap1for0_preserves_inv self t0 t1 oracle
    | .setProtocolShare => setProtocolShare_preserves_inv self t0 t1 oracle
    | .setFeeTo => setFeeTo_preserves_inv self t0 t1 oracle
    | .collectProtocolFees => collectProtocolFees_preserves_inv self t0 t1 oracle
    | .getReserves => getReserves_preserves_inv self t0 t1 oracle
    | .sharesOf => sharesOf_preserves_inv self t0 t1 oracle
    | .protocolFees => protocolFees_preserves_inv self t0 t1 oracle

/-! ### Authorization (share count) -/

private theorem claim_mono_add (σ : Storage) (who a : Address) (a0 a1 : Nat)
    (hInv : InvStorage σ) :
    (σ.shares a).raw ≤ ((addLiquidityPost σ who a0 a1).shares a).raw := by
  have hsh : (σ.shares a).raw ≤ (sharesAfterDead σ a).raw := by
    by_cases hts : σ.totalShares.raw = 0
    · have hz := invStorage_shares_zero hInv hts a
      simp [sharesAfterDead, hts, Function.update, hz]
    · simp [sharesAfterDead, hts]
  simp only [addLiquidityPost]
  by_cases h : a = who
  · subst h
    simp [Function.update, Amount.raw_add, Amount.raw_ofWord]
    exact Nat.le_trans hsh (Nat.le_add_right _ _)
  · have hne : a ≠ who := h
    rw [Function.update_of_ne hne]
    exact hsh

private theorem claim_frame_remove (σ : Storage) (who a : Address) (s : Nat)
    (hne : who ≠ a) :
    ((removeLiquidityPost σ who s).shares a).raw = (σ.shares a).raw := by
  simp [removeLiquidityPost]
  exact Function.update_of_ne (Ne.symm hne) _ _

private theorem claim_eq_swap0 (σ : Storage) (dx proto out : Nat) (a : Address) :
    ((swap0Post σ dx proto out).shares a).raw = (σ.shares a).raw := by
  simp [swap0Post]

private theorem claim_eq_swap1 (σ : Storage) (dx proto out : Nat) (a : Address) :
    ((swap1Post σ dx proto out).shares a).raw = (σ.shares a).raw := by
  simp [swap1Post]

theorem addLiquidity_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth
      .addLiquidity :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨a0, a1⟩ ctx w a n w' hInv hrun hdec => by
    have hok := addLiquidity_ok_of_run hrun
    have ⟨_, hσ, _, _⟩ := addLiquidity_post a0 a1 hok hrun
    have hst : InvStorage w.self := hInv.1.2.2.1
    exact (Nat.not_lt.mpr (by
      simpa [claim, hσ] using
        claim_mono_add w.self ctx.sender a a0.raw a1.raw hst)) hdec

theorem removeLiquidity_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth
      .removeLiquidity :=
  NoUnauthorizedDecreaseFn_of_ok fun s ctx w a n w' _hInv hrun hdec => by
    change ctx.sender = a
    by_cases hs : ctx.sender = a
    · exact hs
    · have hok := removeLiquidity_ok_of_run hrun
      have ⟨_, hσ, _, _⟩ := removeLiquidity_post s hok hrun
      simp [claim, hσ, claim_frame_remove w.self ctx.sender a s.raw hs] at hdec

theorem swap0for1_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .swap0for1 :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨dx, minOut⟩ ctx w a n w' _hInv hrun hdec => by
    have hok := swap0for1_ok_of_run hrun
    have ⟨_, hσ, _, _⟩ := swap0for1_post dx minOut hok hrun
    simp [claim, hσ, claim_eq_swap0] at hdec

theorem swap1for0_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .swap1for0 :=
  NoUnauthorizedDecreaseFn_of_ok fun ⟨dx, minOut⟩ ctx w a n w' _hInv hrun hdec => by
    have hok := swap1for0_ok_of_run hrun
    have ⟨_, hσ, _, _⟩ := swap1for0_post dx minOut hok hrun
    simp [claim, hσ, claim_eq_swap1] at hdec

theorem setProtocolShare_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth
      .setProtocolShare :=
  NoUnauthorizedDecreaseFn_of_ok fun bps ctx w a n w' _hInv hrun hdec => by
    obtain ⟨_, _, rfl⟩ := setProtocolShare_ok_of_run hrun
    simp [claim] at hdec

theorem setFeeTo_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .setFeeTo :=
  NoUnauthorizedDecreaseFn_of_ok fun recipient ctx w a n w' _hInv hrun hdec => by
    obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run hrun
    simp [claim] at hdec

theorem collectProtocolFees_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth
      .collectProtocolFees :=
  NoUnauthorizedDecreaseFn_of_ok fun _u ctx w a n w' _hInv hrun hdec => by
    have hok := collectProtocolFees_ok_of_run hrun
    have ⟨_, hσ, _, _⟩ := collectProtocolFees_post hok hrun
    simp [hσ, claim, collectPost] at hdec

theorem getReserves_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .getReserves := by
  intro u ctx w a _hInv hdec
  cases u
  unfold worldAfter at hdec
  rw [spec_exec_getReserves, getReserves_ok] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem sharesOf_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .sharesOf := by
  intro who ctx w a _hInv hdec
  unfold worldAfter at hdec
  rw [spec_exec_sharesOf, sharesOf_ok] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem protocolFees_auth :
    NoUnauthorizedDecreaseFn spec (InvT self t0 t1 oracle) claim Auth .protocolFees := by
  intro u ctx w a _hInv hdec
  cases u
  unfold worldAfter at hdec
  rw [spec_exec_protocolFees, protocolFees_ok] at hdec
  exact (Nat.lt_irrefl _ hdec).elim

theorem cpamm_no_unauth :
    NoUnauthorizedDecrease spec (InvT self t0 t1 oracle) claim Auth :=
  NoUnauthorizedDecrease.of_fns (C := spec) fun fn =>
    match fn with
    | .addLiquidity => addLiquidity_auth self t0 t1 oracle
    | .removeLiquidity => removeLiquidity_auth self t0 t1 oracle
    | .swap0for1 => swap0for1_auth self t0 t1 oracle
    | .swap1for0 => swap1for0_auth self t0 t1 oracle
    | .setProtocolShare => setProtocolShare_auth self t0 t1 oracle
    | .setFeeTo => setFeeTo_auth self t0 t1 oracle
    | .collectProtocolFees => collectProtocolFees_auth self t0 t1 oracle
    | .getReserves => getReserves_auth self t0 t1 oracle
    | .sharesOf => sharesOf_auth self t0 t1 oracle
    | .protocolFees => protocolFees_auth self t0 t1 oracle

namespace Proof

theorem cpamm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World) (a : Address)
    (hw : Inv self w) (hW : Wf self tr w)
    (hR : RelyAlong (cpammRely self w.self.token0 w.self.token1 w.oracle) tr w)
    (hT0 : IERC20.Spec (w.self.token0.impl : Token0Impl))
    (hT1 : IERC20.Spec (w.self.token1.impl : Token1Impl))
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  no_unauthorized_extraction_at
    (cpamm_no_unauth self w.self.token0 w.self.token1 w.oracle)
    (cpamm_preserves_inv self w.self.token0 w.self.token1 w.oracle)
    (inv_rely self w.self.token0 w.self.token1 w.oracle)
    (ClaimMonoEnv.of_self (fun a (s : Storage) => (s.shares a).raw)
      (cpammRely self w.self.token0 w.self.token1 w.oracle))
    tr w a ⟨hw, rfl, rfl, rfl, hT0, hT1, hInd⟩ hW hR hA

theorem cpamm_solvent (self : Address) (tr : List (Step spec))
    (w : World)
    (hW : Wf self tr w)
    (hR : RelyAlong (cpammRely self w.self.token0 w.self.token1 w.oracle) tr w)
    (hT0 : IERC20.Spec (w.self.token0.impl : Token0Impl))
    (hT1 : IERC20.Spec (w.self.token1.impl : Token1Impl))
    (hInd : TokensIndependent w.self.token0 w.self.token1 w.oracle)
    (h : Inv self w) :
    CoversLpsAndProtocol self (run tr w) :=
  inv_covers self (run tr w)
    (inv_run_at
      (cpamm_preserves_inv self w.self.token0 w.self.token1 w.oracle)
      (inv_rely self w.self.token0 w.self.token1 w.oracle)
      ⟨h, rfl, rfl, rfl, hT0, hT1, hInd⟩ tr hW hR).1

end Proof

end Cpamm
