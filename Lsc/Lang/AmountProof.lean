import Lsc.Lang.Amount
import Lsc.Lang.WordProof

/-!
Proofs of the checked-amount theorems. Statements live in `AmountTheorems.lean`.
-/

namespace Lsc
namespace Amount.Proof

variable {S X E ε : Type} {a b : Asset}

theorem add_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw + y.raw ∧ x.raw + y.raw < wordBound ∧ w' = w := by
  simp [Amount.run_add] at h
  by_cases hfit : x.raw + y.raw < wordBound
  · simp [hfit] at h
    exact ⟨congrArg Amount.raw h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem sub_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw - y.raw ∧ y.raw ≤ x.raw ∧ w' = w := by
  simp [Amount.run_sub] at h
  by_cases hle : y.raw ≤ x.raw
  · simp [hle] at h
    exact ⟨congrArg Amount.raw h.1.symm, hle, h.2.symm⟩
  · simp [hle] at h

theorem mulScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.mulScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      .ok (q, w')) :
    q.raw = x.raw * k ∧ x.raw * k < wordBound ∧ w' = w := by
  simp [Amount.run_mulScalar] at h
  by_cases hfit : x.raw * k < wordBound
  · simp [hfit] at h
    exact ⟨congrArg Amount.raw h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem divScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.divScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      .ok (q, w')) :
    q.raw = x.raw / k ∧ k ≠ 0 ∧ w' = w := by
  simp [Amount.run_divScalar] at h
  by_cases hk : k = 0
  · simp [hk] at h
  · simp [hk] at h
    exact ⟨congrArg Amount.raw h.1.symm, hk, h.2.symm⟩

private theorem run_word_mulDivDown {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    Tx.run (Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num.raw x.raw y.raw)
      ctx w = .ok (q.raw, w') := by
  simp [Amount.run_mulDivDown] at h
  by_cases hy0 : y.raw = 0
  · simp [hy0] at h
  · by_cases hfit : num.raw * x.raw < wordBound
    · simp [hy0, hfit] at h
      simp [Tx.run_mulDivDown, hy0, hfit, congrArg Amount.raw h.1.symm, h.2.symm]
    · simp [hy0, hfit] at h

private theorem run_word_mulDivUp {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    Tx.run (Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num.raw x.raw y.raw)
      ctx w = .ok (q.raw, w') := by
  simp [Amount.run_mulDivUp] at h
  by_cases hy0 : y.raw = 0
  · simp [hy0] at h
  · by_cases hfit : num.raw * x.raw < wordBound
    · simp [hy0, hfit] at h
      simp [Tx.run_mulDivUp, hy0, hfit, congrArg Amount.raw h.1.symm, h.2.symm]
    · simp [hy0, hfit] at h

theorem mulDivDown_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧ q.raw = num.raw * x.raw / y.raw ∧
      q.raw * y.raw ≤ num.raw * x.raw ∧
      num.raw * x.raw - q.raw * y.raw < y.raw ∧ w' = w :=
  Lsc.Proof.mulDivDown_ok (run_word_mulDivDown h)

theorem mulDivUp_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧
      q.raw = num.raw * x.raw / y.raw +
        (if num.raw * x.raw % y.raw = 0 then 0 else 1) ∧
      num.raw * x.raw ≤ q.raw * y.raw ∧ w' = w :=
  Lsc.Proof.mulDivUp_ok (run_word_mulDivUp h)

end Amount.Proof
end Lsc
