import Lsc.Lang.WordProof

/-!
Checked-word theorems: success of an arithmetic primitive implies the
expected result and an unchanged world. Also the `Tx.run` unfolding lemmas
for `mulDivDown` / `mulDivUp` / `pow10`.
-/

namespace Lsc

variable {S X E ε : Type}

/-- A successful checked add returns the mathematical sum, which fits in a
word, and does not change the world. -/
theorem addChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.addChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a + b ∧ a + b < wordBound ∧ w' = w :=
  Proof.addChecked_ok h

/-- A successful checked subtract returns the mathematical difference, the
subtrahend did not exceed the minuend, and the world is unchanged. -/
theorem subChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.subChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a - b ∧ b ≤ a ∧ w' = w :=
  Proof.subChecked_ok h

/-- A successful checked multiply returns the mathematical product, which fits
in a word, and does not change the world. -/
theorem mulChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a * b ∧ a * b < wordBound ∧ w' = w :=
  Proof.mulChecked_ok h

/-- A successful checked divide returns the mathematical quotient, the divisor
was nonzero, and the world is unchanged. -/
theorem divChecked_ok {a b : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.divChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      .ok (q, w')) :
    q = a / b ∧ b ≠ 0 ∧ w' = w :=
  Proof.divChecked_ok h

/-- A successful `mulDivDown` returns `⌊a * b / c⌋`. The divisor is nonzero, the
product fits in a word, and the remainder `a * b - q * c` is strictly less
than `c`. The world is unchanged. -/
theorem mulDivDown_ok {a b c : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      .ok (q, w')) :
    c ≠ 0 ∧ a * b < wordBound ∧ q = a * b / c ∧ q * c ≤ a * b ∧
      a * b - q * c < c ∧ w' = w :=
  Proof.mulDivDown_ok h

/-- A successful `mulDivUp` returns `⌈a * b / c⌉`. The divisor is nonzero, the
product fits in a word, and `q * c` is at least the product. The world is
unchanged. -/
theorem mulDivUp_ok {a b c : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      .ok (q, w')) :
    c ≠ 0 ∧ a * b < wordBound ∧
      q = a * b / c + (if a * b % c = 0 then 0 else 1) ∧ a * b ≤ q * c ∧ w' = w :=
  Proof.mulDivUp_ok h

namespace Tx

/-- `Tx.run (mulDivDown a b c)` is the checked fused floor-divide: revert on
zero divisor or when the product does not fit in a word. -/
@[simp] theorem run_mulDivDown (a b c : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulDivDown (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c, w)
      else .error (.arith .overflow) :=
  Proof.run_mulDivDown a b c ctx w

/-- `Tx.run (mulDivUp a b c)` is the checked fused ceil-divide: revert on zero
divisor or when the product does not fit in a word. -/
@[simp] theorem run_mulDivUp (a b c : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulDivUp (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
      else .error (.arith .overflow) :=
  Proof.run_mulDivUp a b c ctx w

/-- The `Nat` `mulDiv↓` instance is `Tx.mulDivDown`. -/
@[simp] theorem hMulDivDown_nat (a b c : Nat) :
    Lsc.Tx.HMulDivDown.hMulDivDown (S := S) (X := X) (E := E) (ε := ε) a b c =
      mulDivDown a b c :=
  Proof.hMulDivDown_nat a b c

/-- The `Nat` `mulDiv↑` instance is `Tx.mulDivUp`. -/
@[simp] theorem hMulDivUp_nat (a b c : Nat) :
    Lsc.Tx.HMulDivUp.hMulDivUp (S := S) (X := X) (E := E) (ε := ε) a b c =
      mulDivUp a b c :=
  Proof.hMulDivUp_nat a b c

/-- `Tx.run (pow10 d)` returns `10^d` or reverts when `d > 77`. -/
@[simp] theorem run_pow10 (d : Nat) (ctx : Ctx) (w : World S X E) :
    run (pow10 (S := S) (X := X) (E := E) (ε := ε) d) ctx w =
      if d > pow10Max then .error (.arith .overflow)
      else .ok (10 ^ d, w) :=
  Proof.run_pow10 d ctx w

end Tx

/-- A successful `pow10 d` returns `10^d` with `d ≤ 77`, and does not change
the world. -/
theorem pow10_ok {d : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.pow10 (S := S) (X := X) (E := E) (ε := ε) d) ctx w = .ok (q, w')) :
    d ≤ Tx.pow10Max ∧ q = 10 ^ d ∧ w' = w :=
  Proof.pow10_ok h

/-- Rescaling a word from a decimal count to itself is the identity: the
returned value is the input and the world is unchanged. -/
theorem rescale_id {d : Nat} {r : Rounding} {a : Nat} {ctx : Ctx} {w : World S X E}
    {q : Nat} {w' : World S X E}
    (h : Tx.run (Tx.rescale (S := S) (X := X) (E := E) (ε := ε) d d r a) ctx w =
      .ok (q, w')) :
    q = a ∧ w' = w :=
  Proof.rescale_id h

end Lsc
