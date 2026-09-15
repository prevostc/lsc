import Stdlib.Shares
import Lsc.Lang.AmountTheorems
import Lsc.Lang.TxTheorems
import Lsc.Lang.WordTheorems

set_option linter.unusedSimpArgs false

/-!
Proofs of virtual-offset share conversion. Statements live in
`Stdlib/SharesTheorems.lean`.
-/

open Lsc

namespace Lsc.Stdlib.Shares.Proof

variable {S X E ε : Type} {a s : Asset}

private theorem scale_pos (d : Nat) : 0 < Word.scale d :=
  Nat.pow_pos (by decide : 0 < 10)

theorem run_toShares (o : Offset) (assets totalAssets : Amount a)
    (totalShares : Amount s) (ctx : Ctx) (w : World S X E) :
    Tx.run (toShares (S := S) (X := X) (E := E) (ε := ε) o assets totalAssets
        totalShares) ctx w =
      if totalShares.raw + Word.scale o.decimals < wordBound then
        if totalAssets.raw + 1 < wordBound then
          if (totalShares.raw + Word.scale o.decimals) * assets.raw < wordBound
          then
            .ok (⟨toSharesRaw o assets.raw totalAssets.raw totalShares.raw⟩, w)
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  simp only [toShares, Tx.run_bind, Amount.run_add, virtualShares_raw]
  by_cases hts : totalShares.raw + Word.scale o.decimals < wordBound
  · simp [hts]
    by_cases hta : totalAssets.raw + 1 < wordBound
    · have hden : totalAssets.raw + 1 ≠ 0 := Nat.succ_ne_zero _
      simp [hta, Amount.run_mulDivDown, hden, toSharesRaw, Nat.mul_comm]
    · simp [hta]
  · simp [hts]

theorem run_toAssets (o : Offset) (shares : Amount s) (totalAssets : Amount a)
    (totalShares : Amount s) (ctx : Ctx) (w : World S X E) :
    Tx.run (toAssets (S := S) (X := X) (E := E) (ε := ε) o shares totalAssets
        totalShares) ctx w =
      if totalAssets.raw + 1 < wordBound then
        if totalShares.raw + Word.scale o.decimals < wordBound then
          if (totalAssets.raw + 1) * shares.raw < wordBound then
            .ok (⟨toAssetsRaw o shares.raw totalAssets.raw totalShares.raw⟩, w)
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  simp only [toAssets, Tx.run_bind, Amount.run_add, virtualShares_raw]
  by_cases hta : totalAssets.raw + 1 < wordBound
  · simp [hta]
    by_cases hts : totalShares.raw + Word.scale o.decimals < wordBound
    · have hz : ¬ (totalShares.raw = 0 ∧ Word.scale o.decimals = 0) := by
        intro ⟨_, hv⟩
        exact (Nat.pos_iff_ne_zero.mp (scale_pos o.decimals)) hv
      simp [hts, Amount.run_mulDivDown, hz, toAssetsRaw, Nat.mul_comm]
    · simp [hts]
  · simp [hta]

theorem toShares_ok {o : Offset} {assets totalAssets : Amount a}
    {totalShares : Amount s} {ctx : Ctx} {w : World S X E}
    {m : Amount s} {w' : World S X E}
    (h : Tx.run (toShares (S := S) (X := X) (E := E) (ε := ε) o assets
        totalAssets totalShares) ctx w = .ok (m, w')) :
    totalShares.raw + Word.scale o.decimals < wordBound ∧
      totalAssets.raw + 1 < wordBound ∧
      (totalShares.raw + Word.scale o.decimals) * assets.raw < wordBound ∧
      m.raw = toSharesRaw o assets.raw totalAssets.raw totalShares.raw ∧
      w' = w := by
  simp [run_toShares] at h
  by_cases hts : totalShares.raw + Word.scale o.decimals < wordBound
  · simp [hts] at h
    by_cases hta : totalAssets.raw + 1 < wordBound
    · simp [hta] at h
      by_cases hmul :
          (totalShares.raw + Word.scale o.decimals) * assets.raw < wordBound
      · simp [hmul] at h
        exact ⟨hts, hta, hmul, congrArg Amount.raw h.1.symm, h.2.symm⟩
      · simp [hmul] at h
    · simp [hta] at h
  · simp [hts] at h

theorem toAssets_ok {o : Offset} {shares : Amount s} {totalAssets : Amount a}
    {totalShares : Amount s} {ctx : Ctx} {w : World S X E}
    {r : Amount a} {w' : World S X E}
    (h : Tx.run (toAssets (S := S) (X := X) (E := E) (ε := ε) o shares
        totalAssets totalShares) ctx w = .ok (r, w')) :
    totalAssets.raw + 1 < wordBound ∧
      totalShares.raw + Word.scale o.decimals < wordBound ∧
      (totalAssets.raw + 1) * shares.raw < wordBound ∧
      r.raw = toAssetsRaw o shares.raw totalAssets.raw totalShares.raw ∧
      w' = w := by
  simp [run_toAssets] at h
  by_cases hta : totalAssets.raw + 1 < wordBound
  · simp [hta] at h
    by_cases hts : totalShares.raw + Word.scale o.decimals < wordBound
    · simp [hts] at h
      by_cases hmul : (totalAssets.raw + 1) * shares.raw < wordBound
      · simp [hmul] at h
        exact ⟨hta, hts, hmul, congrArg Amount.raw h.1.symm, h.2.symm⟩
      · simp [hmul] at h
    · simp [hts] at h
  · simp [hta] at h

theorem toSharesRaw_mono (o : Offset) {x₁ x₂ A S : Nat} (hle : x₁ ≤ x₂) :
    toSharesRaw o x₁ A S ≤ toSharesRaw o x₂ A S :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ hle)

theorem toSharesRaw_pos (o : Offset) {x A S : Nat}
    (hx : x * Word.scale o.decimals ≥ A + 1) :
    0 < toSharesRaw o x A S := by
  have hx' : A + 1 ≤ x * Word.scale o.decimals := hx
  have hnum : A + 1 ≤ x * (S + Word.scale o.decimals) :=
    Nat.le_trans hx' (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  exact Nat.div_pos hnum (Nat.succ_pos _)

/-- `x·(S+m+V) + m·(A+1) = m·(A+x+1) + x·(S+V)`. -/
private theorem cross_add (x m A S V : Nat) :
    x * (S + m + V) + m * (A + 1) = m * (A + x + 1) + x * (S + V) := by
  have hL : x * (S + m + V) = x * S + x * m + x * V := by
    simp [Nat.mul_add, Nat.add_assoc]
  have hR : m * (A + x + 1) = m * A + m * x + m := by
    simp [Nat.mul_add, Nat.add_assoc]
  have hM : m * (A + 1) = m * A + m := by simp [Nat.mul_add]
  have hX : x * (S + V) = x * S + x * V := by simp [Nat.mul_add]
  rw [hL, hR, hM, hX, Nat.mul_comm x m]
  ac_rfl

private theorem rem_le (x A S V : Nat) :
    x * (S + V) - (x * (S + V) / (A + 1)) * (A + 1) ≤ A := by
  let n := x * (S + V)
  let d := A + 1
  have hadd : d * (n / d) + n % d = n := Nat.div_add_mod n d
  have hle1 : d * (n / d) ≤ n := by
    have : d * (n / d) ≤ d * (n / d) + n % d := Nat.le_add_right _ _
    rwa [hadd] at this
  have hle : (n / d) * d ≤ n := by rw [Nat.mul_comm]; exact hle1
  have hsplit : n = (n / d) * d + n % d := by
    rw [Nat.mul_comm (n / d) d]; exact hadd.symm
  have heq : n - (n / d) * d = n % d :=
    (Nat.sub_eq_iff_eq_add hle).mpr (hsplit.trans (Nat.add_comm _ _))
  have hmod : n % d ≤ A :=
    Nat.lt_succ_iff.mp (by simpa [d] using Nat.mod_lt n (Nat.succ_pos _))
  calc
    n - (n / d) * d = n % d := heq
    _ ≤ A := hmod

/-- Round-trip loss: `V · (x − r) ≤ A + V`. -/
theorem inflation_bound_raw (V x A S : Nat) (hV : 0 < V) :
    let m := x * (S + V) / (A + 1)
    let r := m * (A + x + 1) / (S + m + V)
    V * (x - r) ≤ A + V := by
  intro m r
  let n := m * (A + x + 1)
  let den := S + m + V
  have hden : 0 < den :=
    Nat.lt_of_lt_of_le hV (Nat.le_add_left V (S + m))
  by_cases hrx : x ≤ r
  · simp [Nat.sub_eq_zero_of_le hrx]
  · have hlt : r < x := Nat.lt_of_not_ge hrx
    have hρ : x * (S + V) - m * (A + 1) ≤ A := rem_le x A S V
    have heq := cross_add x m A S V
    let ρn := n % den
    have hn_mod : n = r * den + ρn := by
      have h := (Nat.div_add_mod n den).symm
      have hr : n / den = r := by simp [r, n, den]
      rw [hr, Nat.mul_comm] at h
      exact h
    have hmodn : ρn < den := Nat.mod_lt n hden
    have hxden : x * den = n + (x * (S + V) - m * (A + 1)) := by
      have hle : m * (A + 1) ≤ x * (S + V) := Nat.div_mul_le_self _ _
      have : x * den + m * (A + 1) = n + x * (S + V) := by
        simpa [n, den] using heq
      omega
    have hsum :
        x * den = r * den + (ρn + (x * (S + V) - m * (A + 1))) := by
      have hn := hn_mod
      omega
    have hrd : r * den ≤ x * den :=
      Nat.mul_le_mul_right den (Nat.le_of_lt hlt)
    have hdiff : x * den - r * den =
        ρn + (x * (S + V) - m * (A + 1)) := by
      omega
    have hxd : (x - r) * den ≤ den - 1 + A := by
      have : (x - r) * den = x * den - r * den := Nat.sub_mul x r den
      have h1 : ρn ≤ den - 1 := Nat.le_pred_of_lt hmodn
      omega
    -- `V ≤ den`, so `V * (x - r) * den ≤ V * (den - 1 + A)`.
    have hVden : V ≤ den := Nat.le_add_left V (S + m)
    have hmul : V * ((x - r) * den) ≤ V * (den - 1 + A) :=
      Nat.mul_le_mul_left V hxd
    have hassoc : V * (x - r) * den = V * ((x - r) * den) := by
      simp [Nat.mul_assoc]
    have hL : V * (x - r) * den ≤ V * (den - 1 + A) := by
      rw [hassoc]; exact hmul
    have hR : V * (den - 1 + A) ≤ (A + V) * den := by
      cases A with
      | zero =>
        simpa using Nat.mul_le_mul_left V (Nat.sub_le den 1)
      | succ A' =>
        have hdenA : den - 1 + A'.succ = den + A' := by
          have : 1 ≤ den := Nat.succ_le_of_lt hden
          omega
        calc
          V * (den - 1 + A'.succ)
              = V * (den + A') := by rw [hdenA]
          _ = V * den + V * A' := Nat.mul_add _ _ _
          _ ≤ V * den + den * A' :=
            Nat.add_le_add_left (Nat.mul_le_mul_right A' hVden) _
          _ ≤ V * den + den * A' + den := Nat.le_add_right _ _
          _ = V * den + A'.succ * den := by
            rw [Nat.add_assoc, Nat.succ_mul, Nat.mul_comm A' den]
          _ = (A'.succ + V) * den := by
            rw [Nat.add_mul, Nat.add_comm (A'.succ * den), Nat.mul_comm V den]
    have hgoal : V * (x - r) * den ≤ (A + V) * den :=
      Nat.le_trans hL hR
    exact Nat.le_of_mul_le_mul_right hgoal hden

/-- Minting `toSharesRaw` preserves `S ≤ A · 10^offset`. -/
theorem toSharesRaw_preserves_inv (o : Offset) {x A S : Nat}
    (h : S ≤ A * Word.scale o.decimals) :
    S + toSharesRaw o x A S ≤ (A + x) * Word.scale o.decimals := by
  let V := Word.scale o.decimals
  let m := x * (S + V) / (A + 1)
  have hden : 0 < A + 1 := Nat.succ_pos _
  have hm : m * (A + 1) ≤ x * (S + V) := Nat.div_mul_le_self _ _
  have hkey : S * (A + 1) + x * (S + V) ≤ (A + x) * V * (A + 1) := by
    have hS : S * (A + x + 1) ≤ A * V * (A + x + 1) :=
      Nat.mul_le_mul_right _ h
    have hL : S * (A + 1) + x * (S + V) = S * (A + x + 1) + x * V := by
      have h1 : S * (A + 1) = S * A + S := by rw [Nat.mul_add, Nat.mul_one]
      have h2 : x * (S + V) = x * S + x * V := Nat.mul_add _ _ _
      have h3 : S * (A + x + 1) = S * A + S * x + S := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      rw [h1, h2, h3, Nat.mul_comm S x]
      ac_rfl
    have hR : (A + x) * V * (A + 1) = A * V * (A + x + 1) + x * V := by
      have h1 : (A + x) * V = A * V + x * V := Nat.add_mul _ _ _
      have h2 : (A * V + x * V) * (A + 1) =
          A * V * (A + 1) + x * V * (A + 1) := Nat.add_mul _ _ _
      have h3 : A * V * (A + 1) = A * V * A + A * V := by
        rw [Nat.mul_add, Nat.mul_one]
      have h4 : x * V * (A + 1) = x * V * A + x * V := by
        rw [Nat.mul_add, Nat.mul_one]
      have h5 : A * V * (A + x + 1) = A * V * A + A * V * x + A * V := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have hx : x * V * A = A * V * x := by ac_rfl
      rw [h1, h2, h3, h4, h5, hx]
      ac_rfl
    rw [hL, hR]
    exact Nat.add_le_add_right hS _
  have hmul : (S + m) * (A + 1) ≤ (A + x) * V * (A + 1) := by
    calc
      (S + m) * (A + 1) = S * (A + 1) + m * (A + 1) := Nat.add_mul _ _ _
      _ ≤ S * (A + 1) + x * (S + V) := Nat.add_le_add_left hm _
      _ ≤ (A + x) * V * (A + 1) := hkey
  exact Nat.le_of_mul_le_mul_right hmul hden

/-- Redeeming `toAssetsRaw` preserves `S ≤ A · 10^offset`. -/
theorem toAssetsRaw_preserves_inv (o : Offset) {s A S : Nat}
    (hs : s ≤ S) (h : S ≤ A * Word.scale o.decimals) :
    S - s ≤ (A - toAssetsRaw o s A S) * Word.scale o.decimals := by
  let V := Word.scale o.decimals
  let r := s * (A + 1) / (S + V)
  have hden : 0 < S + V :=
    Nat.lt_of_lt_of_le (scale_pos o.decimals) (Nat.le_add_left _ _)
  have hrA : r ≤ A := by
    have hs' : s * (A + 1) ≤ S * (A + 1) := Nat.mul_le_mul_right _ hs
    have hSA : S * (A + 1) ≤ A * (S + V) := by
      have h1 : S * (A + 1) = S * A + S := by rw [Nat.mul_add, Nat.mul_one]
      have h2 : A * (S + V) = A * S + A * V := Nat.mul_add _ _ _
      rw [h1, h2, Nat.mul_comm S A]
      exact Nat.add_le_add_left h _
    have hle : s * (A + 1) ≤ A * (S + V) := Nat.le_trans hs' hSA
    have : s * (A + 1) / (S + V) ≤ A * (S + V) / (S + V) :=
      Nat.div_le_div_right hle
    rwa [Nat.mul_div_left A hden] at this
  have hsV : s ≤ S + V := Nat.le_trans hs (Nat.le_add_right _ _)
  have hkey : S * (S + V) + s * (A + 1) * V ≤ (A * V + s) * (S + V) := by
    let K := A * V - S
    have hK : A * V = S + K := (Nat.add_sub_of_le h).symm
    have hsk : s * K ≤ K * (S + V) := by
      rw [Nat.mul_comm s K]
      exact Nat.mul_le_mul_left K hsV
    have h1 : S * (S + V) = S * S + S * V := Nat.mul_add _ _ _
    have h2 : s * (A + 1) * V = s * A * V + s * V := by
      have : s * (A + 1) = s * A + s := by rw [Nat.mul_add, Nat.mul_one]
      rw [this, Nat.add_mul]
    have h3 : (A * V + s) * (S + V) =
        S * S + K * S + S * V + K * V + s * S + s * V := by
      rw [hK]
      have hSK : (S + K) * (S + V) = S * S + S * V + K * S + K * V := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hadd : (S + K + s) * (S + V) =
          (S + K) * (S + V) + s * (S + V) :=
        Nat.add_mul (S + K) s (S + V)
      have hsSV : s * (S + V) = s * S + s * V := Nat.mul_add _ _ _
      rw [hadd, hSK, hsSV]
      ac_rfl
    have hA : s * A * V = s * S + s * K := by
      have : s * A * V = s * (A * V) := by rw [Nat.mul_assoc]
      rw [this, hK, Nat.mul_add]
    have hsum' : S * S + S * V + (s * A * V + s * V) ≤
        S * S + K * S + S * V + K * V + s * S + s * V := by
      have : s * A * V ≤ K * S + K * V + s * S := by
        rw [hA]
        have : s * K ≤ K * S + K * V := by
          have : K * (S + V) = K * S + K * V := Nat.mul_add _ _ _
          exact Nat.le_trans hsk (Nat.le_of_eq this)
        omega
      omega
    rw [h1, h2, h3]
    exact hsum'
  have hr : r * (S + V) ≤ s * (A + 1) := Nat.div_mul_le_self _ _
  have hmul : (S + r * V) * (S + V) ≤ (A * V + s) * (S + V) := by
    have hrV : r * V * (S + V) ≤ s * (A + 1) * V := by
      have : r * (S + V) * V ≤ s * (A + 1) * V :=
        Nat.mul_le_mul_right V hr
      have hcomm : r * V * (S + V) = r * (S + V) * V := by ac_rfl
      exact hcomm ▸ this
    calc
      (S + r * V) * (S + V)
          = S * (S + V) + r * V * (S + V) := Nat.add_mul _ _ _
      _ ≤ S * (S + V) + s * (A + 1) * V := Nat.add_le_add_left hrV _
      _ ≤ (A * V + s) * (S + V) := hkey
  have hsum : S + r * V ≤ A * V + s :=
    Nat.le_of_mul_le_mul_right hmul hden
  have hdiff : S - s ≤ A * V - r * V := by omega
  have hsub : A * V - r * V = (A - r) * V := (Nat.sub_mul A r V).symm
  rwa [hsub] at hdiff

end Lsc.Stdlib.Shares.Proof
