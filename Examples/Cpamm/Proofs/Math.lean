import Mathlib.Tactic.SplitIfs
import Examples.Cpamm.Spec

/-!
CPAMM floor-product facts. Duplicated from the fee-less Amm example on
purpose: Cpamm must not import `Examples.Amm.Proofs`.
-/

namespace Cpamm

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

/-- A share `bps / bpsMax` of `n` cannot exceed `n`. -/
theorem share_le (n bps bpsMax : Nat) (h : bps ≤ bpsMax) (hMax : 0 < bpsMax) :
    n * bps / bpsMax ≤ n := by
  simpa [Nat.mul_comm n bps] using remove_le_reserves bps n bpsMax h hMax

/-- Fee-less Uniswap floor output: `k' ≥ k`. -/
theorem k_nondecreasing (rIn rOut dx : Nat) (hIn : 0 < rIn) :
    (rIn + dx) * (rOut - rOut * dx / (rIn + dx)) ≥ rIn * rOut := by
  let den := rIn + dx
  have hden : 0 < den := Nat.add_pos_left hIn dx
  have hout : rOut * dx / den ≤ rOut := by
    simpa [Nat.mul_comm] using
      remove_le_reserves dx rOut den (Nat.le_add_left dx rIn) hden
  have hchop : den * (rOut * dx / den) ≤ rOut * dx := Nat.mul_div_le (rOut * dx) den
  have hdistrib : den * (rOut - rOut * dx / den) =
      den * rOut - den * (rOut * dx / den) :=
    Nat.mul_sub_left_distrib den rOut (rOut * dx / den)
  have hge : den * rOut - den * (rOut * dx / den) ≥ den * rOut - rOut * dx :=
    Nat.sub_le_sub_left hchop _
  have hk : den * rOut - rOut * dx = rIn * rOut := by
    simp [den, Nat.add_mul, Nat.mul_comm dx]
  have h1 : den * (rOut - rOut * dx / den) ≥ den * rOut - rOut * dx :=
    hdistrib ▸ hge
  exact hk ▸ h1

/-- If the input reserve after the swap is at least the fee-less `rIn + dx`,
the same floor output still cannot decrease `k`. -/
theorem k_nondecreasing_ge (rIn rIn' rOut dx : Nat) (hIn : 0 < rIn)
    (hle : rIn + dx ≤ rIn') :
    rIn' * (rOut - rOut * dx / (rIn + dx)) ≥ rIn * rOut := by
  have h := k_nondecreasing rIn rOut dx hIn
  have hmul := Nat.mul_le_mul_right (rOut - rOut * dx / (rIn + dx)) hle
  exact Nat.le_trans h hmul

theorem swapQuote_out (rIn rOut dx feeTo pShareBps : Nat) :
    (swapQuote rIn rOut dx feeTo pShareBps).1 = amountOutF rIn rOut dx :=
  rfl

theorem swapQuote_proto (rIn rOut dx feeTo pShareBps : Nat) :
    (swapQuote rIn rOut dx feeTo pShareBps).2 =
      protoTake feeTo pShareBps (swapFee dx) :=
  rfl

theorem protoTake_le_fee (feeTo ps fee : Nat) (h : ps ≤ BPS) :
    protoTake feeTo ps fee ≤ fee := by
  unfold protoTake
  split_ifs
  · exact Nat.zero_le _
  · exact share_le fee ps BPS h (by decide)

/-- A successful quote never decreases `k`, provided the protocol share is at
most 100% (so the take cannot exceed the 0.3% fee). -/
theorem swapQuote_k (rIn rOut dx feeTo pShareBps : Nat)
    (hIn : 0 < rIn) (hps : pShareBps ≤ BPS) :
    (rIn + (dx - (swapQuote rIn rOut dx feeTo pShareBps).2)) *
      (rOut - (swapQuote rIn rOut dx feeTo pShareBps).1) ≥ rIn * rOut := by
  have hfee : protoTake feeTo pShareBps (swapFee dx) ≤ swapFee dx :=
    protoTake_le_fee feeTo pShareBps (swapFee dx) hps
  have hdxF : dxFeeLess dx ≤ dx := by
    simpa [dxFeeLess, Nat.mul_comm dx] using
      remove_le_reserves (BPS - FEE_BPS) dx BPS (Nat.sub_le _ _) (by decide)
  have hnet : dxFeeLess dx ≤ dx - protoTake feeTo pShareBps (swapFee dx) := by
    have h1 : protoTake feeTo pShareBps (swapFee dx) ≤ dx - dxFeeLess dx := by
      simpa [swapFee] using hfee
    have hsum : protoTake feeTo pShareBps (swapFee dx) + dxFeeLess dx ≤ dx :=
      Nat.add_le_of_le_sub hdxF h1
    rw [Nat.add_comm] at hsum
    exact Nat.le_sub_of_add_le hsum
  have hr' : rIn + dxFeeLess dx ≤
      rIn + (dx - protoTake feeTo pShareBps (swapFee dx)) :=
    Nat.add_le_add_left hnet _
  simpa [swapQuote, amountOutF] using
    k_nondecreasing_ge rIn
      (rIn + (dx - protoTake feeTo pShareBps (swapFee dx)))
      rOut (dxFeeLess dx) hIn hr'

end Cpamm
