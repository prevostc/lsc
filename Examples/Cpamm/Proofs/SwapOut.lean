import Mathlib.Tactic.SplitIfs
import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Math
import Lsc.Lang.TxTheorems
import Lsc.Lang.AmountTheorems
import Lsc.Lang.WordTheorems

set_option linter.unusedSimpArgs false

/-!
`Tx.run` of the asset-polymorphic `swapOut` helper: success is the floor quote
`⌊rOut · dxF / (rIn + dxF)⌋` and protocol take `⌊fee · share / BPS⌋`. An
oversized take (`protoFee > fee`) reverts `FeeTooHigh`.
-/

open Lsc Lsc.Syntax Lsc.Stdlib Cpamm Stdlib

attribute [local simp] Amount.eq_iff Amount.ne_iff Amount.lt_iff Amount.le_iff

namespace Cpamm

variable {ctx : Ctx} {w : World Storage ExtState Event}

private theorem word_10000_ne : (10000 : Word) ≠ 0 := by decide

private theorem run_mulDivDown_bind {α : Type} {a b : Asset}
    (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        Tx.run (k ⟨num.raw * x.raw / y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_def, Amount.run_mulDivDown]
  split_ifs <;> rfl

private theorem run_mulDivDown_word_bind {α : Type} {b : Asset}
    (num : Amount b) (x y : Word)
    (k : Amount b → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y = 0 then .error (.arith .divByZero)
      else if num.raw * x < wordBound then
        Tx.run (k ⟨num.raw * x / y⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_word, Amount.run_mulDivDown]
  by_cases h0 : (Amount.ofWord (a := Asset.fixed 0) y).raw = 0
  · rw [if_pos h0]
    simp [Amount.raw_ofWord] at h0
    simp [h0]
  · rw [if_neg h0]
    simp [Amount.raw_ofWord] at h0
    by_cases hfit : num.raw * (Amount.ofWord (a := Asset.fixed 0) x).raw < wordBound
    · rw [if_pos hfit]
      simp [Amount.raw_ofWord] at hfit
      simp [h0, hfit]
    · rw [if_neg hfit]
      simp [Amount.raw_ofWord] at hfit
      simp [h0, hfit]

private theorem run_mulFixedDown_bind {α : Type} {a : Asset} {d : Nat}
    (x : Amount a) (r : Fixed d)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulFixedDown.hMulFixedDown (S := Storage) (X := ExtState)
        (E := Event) (ε := Error) x r >>= k) ctx w =
      if x.raw * r.raw < wordBound then Tx.run (k (Amount.mulDown x r)) ctx w
      else .error (.arith .overflow) := by
  have hden : (Amount.ofWord (Word.scale d) : Amount (Asset.fixed d)).raw ≠ 0 := by
    simpa [Amount.raw_ofWord] using
      (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide : 0 < 10)) : Word.scale d ≠ 0)
  rw [Tx.run_bind, Amount.hMulFixedDown_def, Amount.mulFixedDown, Amount.run_mulDivDown]
  rw [if_neg hden]
  by_cases hfit : x.raw * r.raw < wordBound
  · rw [if_pos hfit]
    simp [hfit, Amount.mulDown, Amount.floorMulDiv, Amount.raw_ofWord]
  · rw [if_neg hfit]
    simp [hfit]

private theorem run_hAdd_bind {α : Type} {a : Asset} (x y : Amount a)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HAddChecked.hAdd (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) x y >>= k) ctx w =
      if x.raw + y.raw < wordBound then Tx.run (k ⟨x.raw + y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hAdd_def, Amount.run_add]
  split_ifs <;> rfl

private theorem run_hSub_bind {α : Type} {a : Asset} (x y : Amount a)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HSubChecked.hSub (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) x y >>= k) ctx w =
      if y.raw ≤ x.raw then Tx.run (k ⟨x.raw - y.raw⟩) ctx w
      else .error (.arith .underflow) := by
  rw [Tx.run_bind, Amount.hSub_def, Amount.run_sub]
  split_ifs <;> rfl

private theorem run_req_false {α : Type} {c : Prop} [Decidable c] {e : Error}
    {k : Unit → Tx Storage ExtState Event Error α} (h : ¬c) :
    Tx.run (Tx.require (S := Storage) (X := ExtState) (E := Event) c e >>= k) ctx w =
      .error (.user e) := by
  simp [Tx.run_bind, Tx.run_require, h]

private theorem run_req_true {α : Type} {c : Prop} [Decidable c] {e : Error}
    {k : Unit → Tx Storage ExtState Event Error α} (h : c) :
    Tx.run (Tx.require (S := Storage) (X := ExtState) (E := Event) c e >>= k) ctx w =
      Tx.run (k ()) ctx w := by
  simp [Tx.run_bind, Tx.run_require, h]

/-- `protocolShareBps` when `feeTo ≠ 0`, otherwise `0`. -/
def coeffBps (σ : Storage) : Bps :=
  if σ.feeTo = 0 then 0 else σ.protocolShareBps

/-- Floor output of `swapOut`. -/
def swapOutOut (rIn rOut dx : Nat) : Nat := amountOutF rIn rOut dx

/-- Floor protocol take `⌊fee · share / BPS⌋`. -/
def swapOutProto (dx : Nat) (share : Bps) : Nat :=
  swapFee dx * share.raw / BPS.raw

/-- LP remainder of the 0.3% fee after the protocol take. -/
def swapOutLp (dx : Nat) (share : Bps) : Nat :=
  swapFee dx - swapOutProto dx share

/-- Arithmetic conditions under which `swapOut` succeeds. -/
structure SwapOutOk (rIn rOut dx : Nat) (share : Bps) : Prop where
  feeMul : dx * 9970 < wordBound
  den : rIn + dxFeeLess dx < wordBound
  denNe : rIn + dxFeeLess dx ≠ 0
  outMul : rOut * dxFeeLess dx < wordBound
  protoMul : swapFee dx * share.raw < wordBound
  lp : swapOutProto dx share ≤ swapFee dx

private theorem dxF_eq {a : Asset} (amountIn : Amount a) :
    (⟨amountIn.raw * 9970 / 10000⟩ : Amount a) = ⟨dxFeeLess amountIn.raw⟩ :=
  rfl

private theorem dxFeeLess_le' (dx : Nat) : dxFeeLess dx ≤ dx := by
  simpa [dxFeeLess, Nat.mul_comm dx] using
    remove_le_reserves (BPS.raw - FEE_BPS) dx BPS.raw (Nat.sub_le _ _) (by decide)

private theorem BPS_scale : (Word.scale 4 : Nat) = BPS.raw := rfl

private theorem proto_mulDown_share {a : Asset} (dx : Nat) (share : Bps) :
    Amount.mulDown (⟨swapFee dx⟩ : Amount a) share = ⟨swapOutProto dx share⟩ := by
  apply Amount.ext
  simp [Amount.mulDown_raw, swapOutProto, BPS_scale]

private theorem out_eq {a b : Asset} (rIn : Amount a) (rOut : Amount b)
    (amountIn : Amount a) :
    (⟨rOut.raw * dxFeeLess amountIn.raw /
        (rIn.raw + dxFeeLess amountIn.raw)⟩ : Amount b) =
      ⟨swapOutOut rIn.raw rOut.raw amountIn.raw⟩ := by
  simp [swapOutOut, amountOutF, dxFeeLess]

/-- `swapOut` reverts on `amountIn * 9970` overflow. -/
theorem run_swapOut_fee_mul {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (h : ¬ amountIn.raw * 9970 < wordBound) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .error (.arith .overflow) := by
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_neg h]

/-- `swapOut` reverts when `rIn + dxF` overflows. -/
theorem run_swapOut_den {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (hfee : amountIn.raw * 9970 < wordBound)
    (hden : ¬ rIn.raw + dxFeeLess amountIn.raw < wordBound) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .error (.arith .overflow) := by
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_pos hfee, dxF_eq]
  simp only [run_hAdd_bind]
  rw [if_neg hden]

/-- `swapOut` reverts when the output product overflows. -/
theorem run_swapOut_out_mul {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (hfee : amountIn.raw * 9970 < wordBound)
    (hden : rIn.raw + dxFeeLess amountIn.raw < wordBound)
    (hdenNe : rIn.raw + dxFeeLess amountIn.raw ≠ 0)
    (houtM : ¬ rOut.raw * dxFeeLess amountIn.raw < wordBound) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .error (.arith .overflow) := by
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_pos hfee, dxF_eq]
  simp only [run_hAdd_bind]
  rw [if_pos hden]
  simp only [run_mulDivDown_bind]
  rw [if_neg hdenNe, if_neg houtM]

/-- `swapOut` reverts when `fee * share` overflows. -/
theorem run_swapOut_proto_mul {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (hfee : amountIn.raw * 9970 < wordBound)
    (hden : rIn.raw + dxFeeLess amountIn.raw < wordBound)
    (hdenNe : rIn.raw + dxFeeLess amountIn.raw ≠ 0)
    (houtM : rOut.raw * dxFeeLess amountIn.raw < wordBound)
    (hprotoM : ¬ swapFee amountIn.raw * share.raw < wordBound) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .error (.arith .overflow) := by
  have hdxFle : dxFeeLess amountIn.raw ≤ amountIn.raw := dxFeeLess_le' amountIn.raw
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_pos hfee, dxF_eq]
  simp only [run_hAdd_bind]
  rw [if_pos hden]
  simp only [run_mulDivDown_bind]
  rw [if_neg hdenNe, if_pos houtM]
  simp only [run_hSub_bind]
  rw [if_pos hdxFle]
  simp only [run_mulFixedDown_bind]
  have hpm :
      ¬ (⟨amountIn.raw - dxFeeLess amountIn.raw⟩ : Amount a).raw * share.raw <
        wordBound := hprotoM
  rw [if_neg hpm]

/-- `swapOut` reverts when the protocol take exceeds the 0.3% fee. -/
theorem run_swapOut_lp {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (hfee : amountIn.raw * 9970 < wordBound)
    (hden : rIn.raw + dxFeeLess amountIn.raw < wordBound)
    (hdenNe : rIn.raw + dxFeeLess amountIn.raw ≠ 0)
    (houtM : rOut.raw * dxFeeLess amountIn.raw < wordBound)
    (hprotoM : swapFee amountIn.raw * share.raw < wordBound)
    (hlp : ¬ swapOutProto amountIn.raw share ≤ swapFee amountIn.raw) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .error (.user .FeeTooHigh) := by
  have hdxFle : dxFeeLess amountIn.raw ≤ amountIn.raw := dxFeeLess_le' amountIn.raw
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_pos hfee, dxF_eq]
  simp only [run_hAdd_bind]
  rw [if_pos hden]
  simp only [run_mulDivDown_bind]
  rw [if_neg hdenNe, if_pos houtM]
  simp only [run_hSub_bind]
  rw [if_pos hdxFle]
  simp only [run_mulFixedDown_bind]
  have hpm :
      (⟨amountIn.raw - dxFeeLess amountIn.raw⟩ : Amount a).raw * share.raw <
        wordBound := hprotoM
  rw [if_pos hpm]
  rw [show Amount.mulDown (⟨amountIn.raw - dxFeeLess amountIn.raw⟩ : Amount a) share =
        ⟨swapOutProto amountIn.raw share⟩ from by
      simpa [swapFee] using proto_mulDown_share (a := a) amountIn.raw share]
  have hn : ¬ ((⟨swapOutProto amountIn.raw share⟩ : Amount a) ≤
      ⟨amountIn.raw - dxFeeLess amountIn.raw⟩) := by
    simpa [swapFee] using hlp
  exact run_req_false hn

/-- When the arithmetic conditions hold, `swapOut` returns the floor pair. -/
theorem run_swapOut {a b : Asset}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (h : SwapOutOk rIn.raw rOut.raw amountIn.raw share) :
    Tx.run (swapOut rIn rOut amountIn share) ctx w =
      .ok ((⟨swapOutOut rIn.raw rOut.raw amountIn.raw⟩,
        ⟨swapOutProto amountIn.raw share⟩), w) := by
  have hdxFle : dxFeeLess amountIn.raw ≤ amountIn.raw := dxFeeLess_le' amountIn.raw
  unfold swapOut
  simp only [run_mulDivDown_word_bind]
  rw [if_neg word_10000_ne, if_pos h.feeMul, dxF_eq]
  simp only [run_hAdd_bind]
  rw [if_pos h.den]
  simp only [run_mulDivDown_bind]
  rw [if_neg h.denNe, if_pos h.outMul]
  rw [out_eq]
  simp only [run_hSub_bind]
  rw [if_pos hdxFle]
  simp only [run_mulFixedDown_bind]
  have hpm :
      (⟨amountIn.raw - dxFeeLess amountIn.raw⟩ : Amount a).raw * share.raw <
        wordBound := h.protoMul
  rw [if_pos hpm]
  rw [show Amount.mulDown (⟨amountIn.raw - dxFeeLess amountIn.raw⟩ : Amount a) share =
        ⟨swapOutProto amountIn.raw share⟩ from by
      simpa [swapFee] using proto_mulDown_share (a := a) amountIn.raw share]
  have hle : (⟨swapOutProto amountIn.raw share⟩ : Amount a) ≤
      ⟨amountIn.raw - dxFeeLess amountIn.raw⟩ := by
    simpa [swapFee] using h.lp
  rw [run_req_true hle]
  simp [Tx.run_pure]

/-- `swapOut` after a bind is the continuation on the floor pair. -/
theorem run_swapOut_bind {a b : Asset} {ρ : Type}
    (rIn : Amount a) (rOut : Amount b) (amountIn : Amount a) (share : Bps)
    (k : Amount b × Amount a → M ρ)
    (h : SwapOutOk rIn.raw rOut.raw amountIn.raw share) :
    Tx.run (swapOut rIn rOut amountIn share >>= k) ctx w =
      Tx.run (k (⟨swapOutOut rIn.raw rOut.raw amountIn.raw⟩,
        ⟨swapOutProto amountIn.raw share⟩)) ctx w := by
  rw [Tx.run_bind, run_swapOut rIn rOut amountIn share h]

/-- Success of `swapOut` is exactly the floor formulas. -/
theorem run_swapOut_ok {a b : Asset} (rIn : Amount a) (rOut : Amount b)
    (amountIn : Amount a) (share : Bps)
    {p : Amount b × Amount a}
    {w' : World Storage ExtState Event} :
    Tx.run (swapOut rIn rOut amountIn share) ctx w = .ok (p, w') ↔
      SwapOutOk rIn.raw rOut.raw amountIn.raw share ∧
        p.1 = ⟨swapOutOut rIn.raw rOut.raw amountIn.raw⟩ ∧
        p.2 = ⟨swapOutProto amountIn.raw share⟩ ∧
        w' = w := by
  constructor
  · intro hrun
    have hfee : amountIn.raw * 9970 < wordBound := by
      by_contra ht
      exact Tx.run_ok_error hrun (run_swapOut_fee_mul rIn rOut amountIn share ht)
    have hden : rIn.raw + dxFeeLess amountIn.raw < wordBound := by
      by_contra ht
      exact Tx.run_ok_error hrun (run_swapOut_den rIn rOut amountIn share hfee ht)
    have hdenNe : rIn.raw + dxFeeLess amountIn.raw ≠ 0 := by
      by_contra ht
      unfold swapOut at hrun
      simp only [run_mulDivDown_word_bind] at hrun
      rw [if_neg word_10000_ne, if_pos hfee, dxF_eq] at hrun
      simp only [run_hAdd_bind] at hrun
      rw [if_pos hden] at hrun
      simp only [run_mulDivDown_bind] at hrun
      rw [if_pos ht] at hrun
      cases hrun
    have houtM : rOut.raw * dxFeeLess amountIn.raw < wordBound := by
      by_contra ht
      exact Tx.run_ok_error hrun
        (run_swapOut_out_mul rIn rOut amountIn share hfee hden hdenNe ht)
    have hprotoM : swapFee amountIn.raw * share.raw < wordBound := by
      by_contra ht
      exact Tx.run_ok_error hrun
        (run_swapOut_proto_mul rIn rOut amountIn share hfee hden hdenNe houtM ht)
    have hlp : swapOutProto amountIn.raw share ≤ swapFee amountIn.raw := by
      by_contra ht
      exact Tx.run_ok_error hrun
        (run_swapOut_lp rIn rOut amountIn share hfee hden hdenNe houtM hprotoM ht)
    have hok : SwapOutOk rIn.raw rOut.raw amountIn.raw share :=
      ⟨hfee, hden, hdenNe, houtM, hprotoM, hlp⟩
    rw [run_swapOut rIn rOut amountIn share hok] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨hok, rfl, rfl, rfl⟩
  · intro ⟨hok, h1, h2, hw⟩
    have hp : p =
        (⟨swapOutOut rIn.raw rOut.raw amountIn.raw⟩,
          ⟨swapOutProto amountIn.raw share⟩) :=
      Prod.ext h1 h2
    rw [run_swapOut rIn rOut amountIn share hok, hp, hw]

end Cpamm
