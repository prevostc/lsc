import Lsc.Lang.AmountProof

/-!
Checked-amount theorems: success of an arithmetic primitive implies the
expected result on `.raw` and an unchanged world. Also `Tx.run` unfolding
lemmas, certificate bind lemmas, and `require` / `ite` rewrites used by
`lsc_reify`.
-/

namespace Lsc.Amount

variable {S X E ε : Type} {a b : Asset}

/-- `Tx.run (add x y)` is the checked sum, or overflow. -/
@[simp] theorem run_add (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if x.raw + y.raw < wordBound then .ok (⟨x.raw + y.raw⟩, w)
      else .error (.arith .overflow) :=
  Proof.run_add x y ctx w

/-- `Tx.run (sub x y)` is the checked difference, or underflow. -/
@[simp] theorem run_sub (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if y.raw ≤ x.raw then .ok (⟨x.raw - y.raw⟩, w)
      else .error (.arith .underflow) :=
  Proof.run_sub x y ctx w

/-- `Tx.run (mulScalar x k)` is the checked product, or overflow. -/
@[simp] theorem run_mulScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if x.raw * k < wordBound then .ok (⟨x.raw * k⟩, w)
      else .error (.arith .overflow) :=
  Proof.run_mulScalar x k ctx w

/-- `Tx.run (divScalar x k)` is the checked quotient, or division by zero. -/
@[simp] theorem run_divScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (divScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if k ≠ 0 then .ok (⟨x.raw / k⟩, w)
      else .error (.arith .divByZero) :=
  Proof.run_divScalar x k ctx w

/-- `Tx.run (mulDivDown num x y)` is the checked fused floor-divide on `.raw`. -/
@[simp] theorem run_mulDivDown (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw⟩, w)
      else .error (.arith .overflow) :=
  Proof.run_mulDivDown num x y ctx w

/-- `Tx.run (mulDivUp num x y)` is the checked fused ceil-divide on `.raw`. -/
@[simp] theorem run_mulDivUp (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw +
          (if num.raw * x.raw % y.raw = 0 then 0 else 1)⟩, w)
      else .error (.arith .overflow) :=
  Proof.run_mulDivUp num x y ctx w

/-- Surface `load` of an `Amount` field is Core `load` of `.raw` then `ofWord`. -/
theorem load_bind_ofWord {β : Type} (proj : S → Amount a)
    (k : Amount a → Tx S X E ε β) :
    Tx.load (X := X) (E := E) (ε := ε) proj >>= k =
      Tx.load (fun σ => (proj σ).raw) >>= fun n => k (ofWord n) :=
  Proof.load_bind_ofWord proj k

/-- Surface `loadMap` of an `Amount` mapping is Core `.raw` then `ofWord`. -/
theorem loadMap_bind_ofWord {K β : Type} (proj : S → K → Amount a) (key : K)
    (k : Amount a → Tx S X E ε β) :
    Tx.loadMap (X := X) (E := E) (ε := ε) proj key >>= k =
      Tx.loadMap (fun σ i => (proj σ i).raw) key >>= fun n => k (ofWord n) :=
  Proof.loadMap_bind_ofWord proj key k

/-- Surface `loadMap2` of an `Amount` nested mapping is Core `.raw` then `ofWord`. -/
theorem loadMap2_bind_ofWord {K₁ K₂ β : Type} (proj : S → K₁ → K₂ → Amount a)
    (k₁ : K₁) (k₂ : K₂) (k : Amount a → Tx S X E ε β) :
    Tx.loadMap2 (X := X) (E := E) (ε := ε) proj k₁ k₂ >>= k =
      Tx.loadMap2 (fun σ i j => (proj σ i j).raw) k₁ k₂ >>=
        fun n => k (ofWord n) :=
  Proof.loadMap2_bind_ofWord proj k₁ k₂ k

/-- Surface `add` is Core `addChecked` on `.raw` then `ofWord`. -/
theorem add_bind_ofWord {β : Type} (x y : Amount a)
    (k : Amount a → Tx S X E ε β) :
    add (S := S) (X := X) (E := E) (ε := ε) x y >>= k =
      Tx.addChecked x.raw y.raw >>= fun n => k (ofWord n) :=
  Proof.add_bind_ofWord x y k

/-- Surface `sub` is Core `subChecked` on `.raw` then `ofWord`. -/
theorem sub_bind_ofWord {β : Type} (x y : Amount a)
    (k : Amount a → Tx S X E ε β) :
    sub (S := S) (X := X) (E := E) (ε := ε) x y >>= k =
      Tx.subChecked x.raw y.raw >>= fun n => k (ofWord n) :=
  Proof.sub_bind_ofWord x y k

/-- Surface `mulDivDown` is Core `Tx.mulDivDown` on `.raw` then `ofWord`. -/
theorem mulDivDown_bind_ofWord {β : Type} (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx S X E ε β) :
    mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y >>= k =
      Tx.mulDivDown num.raw x.raw y.raw >>= fun n => k (ofWord n) :=
  Proof.mulDivDown_bind_ofWord num x y k

/-- Surface `mulDivUp` is Core `Tx.mulDivUp` on `.raw` then `ofWord`. -/
theorem mulDivUp_bind_ofWord {β : Type} (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx S X E ε β) :
    mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y >>= k =
      Tx.mulDivUp num.raw x.raw y.raw >>= fun n => k (ofWord n) :=
  Proof.mulDivUp_bind_ofWord num x y k

/-- `require (0 < x)` is the Core word test `0 < x.raw`. -/
@[simp] theorem require_pos (x : Amount a) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (0 < x) err =
      Tx.require (0 < x.raw) err :=
  Proof.require_pos x err

/-- `require (0 < ofWord n)` is the Core word test `0 < n`. -/
@[simp] theorem require_lt_ofWord (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (0 < ofWord (a := a) n) err =
      Tx.require (0 < n) err :=
  Proof.require_lt_ofWord n err

/-- `require (x ≤ ofWord n)` is the Core word test `x.raw ≤ n`. -/
@[simp] theorem require_le_ofWord (x : Amount a) (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (x ≤ ofWord n) err =
      Tx.require (x.raw ≤ n) err :=
  Proof.require_le_ofWord x n err

/-- `require (ofWord n = 0)` is the Core word test `n = 0`. -/
@[simp] theorem require_eq_zero_ofWord (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (ofWord (a := a) n = 0) err =
      Tx.require (n = 0) err :=
  Proof.require_eq_zero_ofWord n err

/-- `if ofWord n = 0` is the Core word branch `if n = 0`. -/
@[simp] theorem ite_eq_zero_ofWord {β : Type} (n : Word)
    (t e : Tx S X E ε β) :
    (if ofWord (a := a) n = 0 then t else e) = (if n = 0 then t else e) :=
  Proof.ite_eq_zero_ofWord n t e

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

namespace Lsc.Lang

variable {S X E ε : Type}

/-- Mapping `ofWord` over a word `Tx` does not change the post-world. -/
theorem worldAfter_ofWord {a : Asset} (x : Tx S X E ε Nat)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (Amount.ofWord (a := a) <$> x) ctx w :=
  Proof.worldAfter_ofWord x ctx w

/-- Mapping a pair of `ofWord` over a word-pair `Tx` does not change the
post-world. -/
theorem worldAfter_amountProd {a b : Asset} (x : Tx S X E ε (Nat × Nat))
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w =
      worldAfter ((fun v =>
        (Amount.ofWord (a := a) v.1, Amount.ofWord (a := b) v.2)) <$> x) ctx w :=
  Proof.worldAfter_amountProd x ctx w

end Lsc.Lang
