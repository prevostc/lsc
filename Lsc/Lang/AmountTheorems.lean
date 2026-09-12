import Lsc.Lang.AmountProof

/-!
Checked-amount theorems: success of an arithmetic primitive implies the
expected result on `.raw` and an unchanged world.
-/

namespace Lsc.Amount

variable {S X E ε : Type} {a b : Asset}

/-- A successful checked add returns the mathematical sum, which fits in a
word, and does not change the world. -/
theorem add_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw + y.raw ∧ x.raw + y.raw < wordBound ∧ w' = w :=
  Proof.add_ok h

/-- A successful checked subtract returns the mathematical difference, the
subtrahend did not exceed the minuend, and the world is unchanged. -/
theorem sub_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw - y.raw ∧ y.raw ≤ x.raw ∧ w' = w :=
  Proof.sub_ok h

/-- A successful scalar multiply returns the mathematical product, which fits
in a word, and does not change the world. -/
theorem mulScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.mulScalar (S := S) (X := X) (E := E) (ε := ε) x k)
      ctx w = .ok (q, w')) :
    q.raw = x.raw * k ∧ x.raw * k < wordBound ∧ w' = w :=
  Proof.mulScalar_ok h

/-- A successful scalar divide returns the mathematical quotient, the divisor
was nonzero, and the world is unchanged. -/
theorem divScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.divScalar (S := S) (X := X) (E := E) (ε := ε) x k)
      ctx w = .ok (q, w')) :
    q.raw = x.raw / k ∧ k ≠ 0 ∧ w' = w :=
  Proof.divScalar_ok h

/-- A successful `mulDivDown` returns `⌊num.raw * x.raw / y.raw⌋`. The divisor
is nonzero, the product fits in a word, and the remainder
`num.raw * x.raw − q.raw * y.raw` is strictly less than `y.raw`. The world
is unchanged. -/
theorem mulDivDown_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧ q.raw = num.raw * x.raw / y.raw ∧
      q.raw * y.raw ≤ num.raw * x.raw ∧
      num.raw * x.raw - q.raw * y.raw < y.raw ∧ w' = w :=
  Proof.mulDivDown_ok h

/-- A successful `mulDivUp` returns `⌈num.raw * x.raw / y.raw⌉`. The divisor is
nonzero, the product fits in a word, and `q.raw * y.raw` is at least the
product. The world is unchanged. -/
theorem mulDivUp_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧
      q.raw = num.raw * x.raw / y.raw +
        (if num.raw * x.raw % y.raw = 0 then 0 else 1) ∧
      num.raw * x.raw ≤ q.raw * y.raw ∧ w' = w :=
  Proof.mulDivUp_ok h

end Lsc.Amount
