import Stdlib.Proof.SharesProof

/-!
Virtual-offset share conversion: `Tx.run` unfolding, the inflation bound,
and monotonicity / dust-threshold facts.
-/

open Lsc

namespace Lsc.Stdlib.Shares

variable {S X E ε : Type} {a s : Asset}

/-- `toShares` succeeds iff the two virtual adds and the fused product fit
in a word. The result is `⌊assets · (totalShares + 10^offset) / (totalAssets + 1)⌋`
and the world is unchanged. The virtual-asset divisor is never zero. -/
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
      else .error (.arith .overflow) :=
  Proof.run_toShares o assets totalAssets totalShares ctx w

/-- `toAssets` succeeds iff the two virtual adds and the fused product fit
in a word. The result is `⌊shares · (totalAssets + 1) / (totalShares + 10^offset)⌋`
and the world is unchanged. The virtual-share divisor is never zero. -/
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
      else .error (.arith .overflow) :=
  Proof.run_toAssets o shares totalAssets totalShares ctx w

/-- A successful `toShares` returns the floor formula, the three word checks
passed, and does not change the world. -/
theorem toShares_ok {o : Offset} {assets totalAssets : Amount a}
    {totalShares : Amount s} {ctx : Ctx} {w : World S X E}
    {m : Amount s} {w' : World S X E}
    (h : Tx.run (toShares (S := S) (X := X) (E := E) (ε := ε) o assets
        totalAssets totalShares) ctx w = .ok (m, w')) :
    totalShares.raw + Word.scale o.decimals < wordBound ∧
      totalAssets.raw + 1 < wordBound ∧
      (totalShares.raw + Word.scale o.decimals) * assets.raw < wordBound ∧
      m.raw = toSharesRaw o assets.raw totalAssets.raw totalShares.raw ∧
      w' = w :=
  Proof.toShares_ok h

/-- A successful `toAssets` returns the floor formula, the three word checks
passed, and does not change the world. -/
theorem toAssets_ok {o : Offset} {shares : Amount s} {totalAssets : Amount a}
    {totalShares : Amount s} {ctx : Ctx} {w : World S X E}
    {r : Amount a} {w' : World S X E}
    (h : Tx.run (toAssets (S := S) (X := X) (E := E) (ε := ε) o shares
        totalAssets totalShares) ctx w = .ok (r, w')) :
    totalAssets.raw + 1 < wordBound ∧
      totalShares.raw + Word.scale o.decimals < wordBound ∧
      (totalAssets.raw + 1) * shares.raw < wordBound ∧
      r.raw = toAssetsRaw o shares.raw totalAssets.raw totalShares.raw ∧
      w' = w :=
  Proof.toAssets_ok h

/-- `toShares` is monotone in the deposited assets (raw floor formula). -/
theorem toSharesRaw_mono (o : Offset) {x₁ x₂ A S : Nat} (hle : x₁ ≤ x₂) :
    toSharesRaw o x₁ A S ≤ toSharesRaw o x₂ A S :=
  Proof.toSharesRaw_mono o hle

/-- A deposit of at least `(totalAssets + 1) / 10^offset` wei (equivalently
`assets · 10^offset ≥ totalAssets + 1`) mints a positive share count. -/
theorem toSharesRaw_pos (o : Offset) {x A S : Nat}
    (hx : x * Word.scale o.decimals ≥ A + 1) :
    0 < toSharesRaw o x A S :=
  Proof.toSharesRaw_pos o hx

/-- After depositing `x` into a vault with live assets `A` and share supply
`S`, the minted shares redeem (same virtual offset, rounding down) for `r`
satisfying `10^offset · (x − r) ≤ A + 10^offset`. Unmatched assets already
in the vault must therefore be on the order of `10^offset` wei per wei the
depositor cannot redeem. This is the attacker-cost form of the inflation
bound; the weaker `r ≥ x − x/10^offset − 1` is false when `A` is already
inflated and the deposit mints zero shares. -/
theorem inflation_bound_raw (o : Offset) (x A S : Nat) :
    let V := Word.scale o.decimals
    let m := toSharesRaw o x A S
    let r := toAssetsRaw o m (A + x) (S + m)
    V * (x - r) ≤ A + V :=
  Proof.inflation_bound_raw (Word.scale o.decimals) x A S
    (Nat.pow_pos (by decide : 0 < 10))

/-- Minting does not break `totalShares ≤ totalAssets · 10^offset`. -/
theorem toSharesRaw_preserves_inv (o : Offset) {x A S : Nat}
    (h : S ≤ A * Word.scale o.decimals) :
    S + toSharesRaw o x A S ≤ (A + x) * Word.scale o.decimals :=
  Proof.toSharesRaw_preserves_inv o h

/-- Redeeming does not break `totalShares ≤ totalAssets · 10^offset`. -/
theorem toAssetsRaw_preserves_inv (o : Offset) {s A S : Nat}
    (hs : s ≤ S) (h : S ≤ A * Word.scale o.decimals) :
    S - s ≤ (A - toAssetsRaw o s A S) * Word.scale o.decimals :=
  Proof.toAssetsRaw_preserves_inv o hs h

end Lsc.Stdlib.Shares
