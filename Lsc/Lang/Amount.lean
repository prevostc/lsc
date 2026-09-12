import Lean
import Lsc.Lang.Word

/-!
# Asset-indexed amounts

Numbers are indexed by the **asset** they denominate. The asset is a
contract-level closed constant; bindings and storage fields are typed by
it. `Amount a` is a one-field structure (an abbrev would unify every
amount back to `Word`). Same-asset `+? -?`; `*? /?` only against a `Word`
scalar; `mulDivDown` / `Up` take a numerator of asset `b` and a ratio of
two `a`s.

`Fixed d` is dimensionless fixed-point with static decimals.
-/

namespace Lsc

/-- What an amount is denominated in. `name` is for `Repr` / ABI docs.
`decimals?` is `some d` when static (LP shares, WAD) and `none` when the
decimals are only known on chain. -/
structure Asset where
  name : Lean.Name
  decimals? : Option Nat
  deriving Repr, DecidableEq

/-- Dimensionless fixed-point asset at `d` decimals. -/
def Asset.fixed (d : Nat) : Asset := ⟨`fixed, some d⟩

/-- A quantity of asset `a`. Erased to one word by Reify. -/
structure Amount (a : Asset) where
  raw : Word
  deriving Repr

/-- Dimensionless fixed-point number at `d` decimals. -/
abbrev Fixed (d : Nat) : Type := Amount (Asset.fixed d)

namespace Amount

variable {a b : Asset}

instance : DecidableEq (Amount a) := fun x y =>
  if h : x.raw = y.raw then
    isTrue (by cases x; cases y; subst h; rfl)
  else
    isFalse (by intro h'; cases x; cases y; exact h (Amount.mk.inj h'))

instance : OfNat (Amount a) n := ⟨⟨n⟩⟩
instance : Inhabited (Amount a) := ⟨⟨0⟩⟩
instance : LT (Amount a) where
  lt x y := x.raw < y.raw
instance : LE (Amount a) where
  le x y := x.raw ≤ y.raw
instance (x y : Amount a) : Decidable (x < y) := Nat.decLt x.raw y.raw
instance (x y : Amount a) : Decidable (x ≤ y) := Nat.decLe x.raw y.raw

/-- Mathematical add, for statements and invariants. Overflowing `+?` is the
surface operation. -/
instance : Add (Amount a) where
  add x y := ⟨x.raw + y.raw⟩
instance : Sub (Amount a) where
  sub x y := ⟨x.raw - y.raw⟩
instance : Mul (Amount a) where
  mul x y := ⟨x.raw * y.raw⟩

@[ext] theorem ext {x y : Amount a} (h : x.raw = y.raw) : x = y := by
  cases x; cases y; subst h; rfl

/-- Tag a raw word as an amount. Boundary use only. -/
def ofWord (n : Word) : Amount a := ⟨n⟩

@[simp] theorem raw_mk (n : Word) : (⟨n⟩ : Amount a).raw = n := rfl
@[simp] theorem mk_raw (x : Amount a) : (⟨x.raw⟩ : Amount a) = x := rfl
@[simp] theorem raw_ofWord (n : Word) : (ofWord n : Amount a).raw = n := rfl
@[simp] theorem ofWord_raw (x : Amount a) : ofWord (a := a) x.raw = x := rfl
@[simp] theorem raw_add (x y : Amount a) : (x + y).raw = x.raw + y.raw := rfl
@[simp] theorem raw_sub (x y : Amount a) : (x - y).raw = x.raw - y.raw := rfl
@[simp] theorem raw_mul (x y : Amount a) : (x * y).raw = x.raw * y.raw := rfl
@[simp] theorem raw_ofNat (n : Nat) : (OfNat.ofNat n : Amount a).raw = n := rfl
@[simp] theorem raw_zero : (0 : Amount a).raw = 0 := rfl
@[simp] theorem mk_add (x y : Amount a) : (⟨x.raw + y.raw⟩ : Amount a) = x + y := rfl
@[simp] theorem mk_sub (x y : Amount a) : (⟨x.raw - y.raw⟩ : Amount a) = x - y := rfl
@[simp] theorem ofWord_add (x y : Amount a) : ofWord (x.raw + y.raw) = x + y := rfl
@[simp] theorem ofWord_sub (x y : Amount a) : ofWord (x.raw - y.raw) = x - y := rfl

theorem raw_sub_add {x y : Amount a} (h : y.raw ≤ x.raw) : (x - y + y).raw = x.raw :=
  Nat.sub_add_cancel h
@[simp] theorem lt_iff (x y : Amount a) : x < y ↔ x.raw < y.raw := Iff.rfl
@[simp] theorem le_iff (x y : Amount a) : x ≤ y ↔ x.raw ≤ y.raw := Iff.rfl

theorem not_le_of_gt {x y : Amount a} (h : y < x) : ¬ x ≤ y :=
  Nat.not_le_of_gt h
theorem not_lt_of_ge {x y : Amount a} (h : x ≤ y) : ¬ y < x :=
  Nat.not_lt_of_ge h

/-- Schema-shaped map updates agree with `Function.update` on `Amount`. -/
theorem update_raw {K : Type} [DecidableEq K] (m : K → Amount a)
    (k : K) (n : Word) :
    (fun k' => ofWord (Function.update (fun i => (m i).raw) k n k')) =
      Function.update m k (ofWord n) := by
  funext k'
  by_cases h : k' = k <;> simp [Function.update, h, ofWord]

@[simp] theorem update_raw_apply {K : Type} [DecidableEq K] (m : K → Amount a)
    (k k' : K) (v : Amount a) :
    (Function.update m k v k').raw = Function.update (fun i => (m i).raw) k v.raw k' := by
  by_cases h : k' = k <;> simp [Function.update, h]

/-- Two successive schema-shaped updates agree with `Function.update`. -/
theorem update2_raw {K : Type} [DecidableEq K] (m : K → Amount a)
    (k₁ k₂ : K) (n₁ n₂ : Word) :
    (fun k => ofWord
      (Function.update (Function.update (fun i => (m i).raw) k₁ n₁) k₂ n₂ k)) =
      Function.update (Function.update m k₁ (ofWord n₁)) k₂ (ofWord n₂) := by
  have hraw :
      (fun i => (Function.update m k₁ (ofWord n₁) i).raw) =
        Function.update (fun i => (m i).raw) k₁ n₁ := by
    funext i; simp [update_raw_apply]
  rw [← hraw]
  exact update_raw (Function.update m k₁ (ofWord n₁)) k₂ n₂

/-- `ofWord` of a schema-shaped lookup-plus-word is the Amount lookup plus `ofWord`. -/
theorem ofWord_update_add {K : Type} [DecidableEq K] (m : K → Amount a)
    (k k' : K) (n addend : Word) :
    ofWord (Function.update (fun i => (m i).raw) k n k' + addend) =
      Function.update m k (ofWord n) k' + ofWord addend := by
  apply ext
  simp [raw_add, update_raw_apply]

/-- Nested mapping update used by `allowances[owner, spender]`. -/
theorem update_nested_raw {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    (m : K₁ → K₂ → Amount a) (k₁ : K₁) (k₂ : K₂) (n : Word) :
    (fun i j => ofWord (Function.update (fun i j => (m i j).raw) k₁
      (Function.update (fun j => (m k₁ j).raw) k₂ n) i j)) =
      Function.update m k₁ (Function.update (m k₁) k₂ (ofWord n)) := by
  funext i j
  by_cases h₁ : i = k₁ <;> by_cases h₂ : j = k₂
    <;> simp [Function.update, h₁, h₂, ofWord]

variable {S X E ε : Type}

/-- Same-asset checked add. Definitionally `ofWord <$> addChecked`, so a
certificate `ofWord <$> Core.denote` matches the surface. -/
def add (x y : Amount a) : Tx S X E ε (Amount a) :=
  ofWord <$> Tx.addChecked x.raw y.raw

/-- Same-asset checked subtract. -/
def sub (x y : Amount a) : Tx S X E ε (Amount a) :=
  ofWord <$> Tx.subChecked x.raw y.raw

/-- Scale by a word. -/
def mulScalar (x : Amount a) (k : Word) : Tx S X E ε (Amount a) :=
  ofWord <$> Tx.mulChecked x.raw k

/-- Divide by a word. -/
def divScalar (x : Amount a) (k : Word) : Tx S X E ε (Amount a) :=
  ofWord <$> Tx.divChecked x.raw k

/-- `⌊num * x / y⌋`: numerator of asset `b`, ratio of two `a`s. -/
def mulDivDown (num : Amount b) (x y : Amount a) : Tx S X E ε (Amount b) :=
  ofWord <$> Tx.mulDivDown num.raw x.raw y.raw

/-- `⌈num * x / y⌉`. -/
def mulDivUp (num : Amount b) (x y : Amount a) : Tx S X E ε (Amount b) :=
  ofWord <$> Tx.mulDivUp num.raw x.raw y.raw

instance : Tx.HAddChecked (Amount a) (Amount a) (Amount a) where
  hAdd := add
instance : Tx.HSubChecked (Amount a) (Amount a) (Amount a) where
  hSub := sub
instance : Tx.HMulChecked (Amount a) Word (Amount a) where
  hMul := mulScalar
instance : Tx.HDivChecked (Amount a) Word (Amount a) where
  hDiv := divScalar

variable {S X E ε : Type}

@[simp] theorem hAdd_def (x y : Amount a) :
    Tx.HAddChecked.hAdd (S := S) (X := X) (E := E) (ε := ε) x y = add x y := rfl
@[simp] theorem hSub_def (x y : Amount a) :
    Tx.HSubChecked.hSub (S := S) (X := X) (E := E) (ε := ε) x y = sub x y := rfl
@[simp] theorem hMul_def (x : Amount a) (k : Word) :
    Tx.HMulChecked.hMul (S := S) (X := X) (E := E) (ε := ε) x k = mulScalar x k := rfl
@[simp] theorem hDiv_def (x : Amount a) (k : Word) :
    Tx.HDivChecked.hDiv (S := S) (X := X) (E := E) (ε := ε) x k = divScalar x k := rfl

@[simp] theorem run_add (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if x.raw + y.raw < wordBound then .ok (⟨x.raw + y.raw⟩, w)
      else .error (.arith .overflow) := by
  simp [add, Tx.run_map, Tx.run_addChecked]
  by_cases h : x.raw + y.raw < wordBound <;> simp [h, ofWord]

@[simp] theorem run_sub (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if y.raw ≤ x.raw then .ok (⟨x.raw - y.raw⟩, w)
      else .error (.arith .underflow) := by
  simp [sub, Tx.run_map, Tx.run_subChecked]
  by_cases h : y.raw ≤ x.raw <;> simp [h, ofWord]

@[simp] theorem run_mulScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if x.raw * k < wordBound then .ok (⟨x.raw * k⟩, w)
      else .error (.arith .overflow) := by
  simp [mulScalar, Tx.run_map, Tx.run_mulChecked]
  by_cases h : x.raw * k < wordBound <;> simp [h, ofWord]

@[simp] theorem run_divScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (divScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if k ≠ 0 then .ok (⟨x.raw / k⟩, w)
      else .error (.arith .divByZero) := by
  simp [divScalar, Tx.run_map, Tx.run_divChecked]
  by_cases h : k = 0 <;> simp [h, ofWord]

@[simp] theorem run_mulDivDown (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw⟩, w)
      else .error (.arith .overflow) := by
  simp [mulDivDown, Tx.run_map, Tx.run_mulDivDown]
  by_cases hy : y.raw = 0
  · simp [hy]
  · by_cases hfit : num.raw * x.raw < wordBound <;> simp [hy, hfit, ofWord]

@[simp] theorem run_mulDivUp (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw +
          (if num.raw * x.raw % y.raw = 0 then 0 else 1)⟩, w)
      else .error (.arith .overflow) := by
  simp [mulDivUp, Tx.run_map, Tx.run_mulDivUp]
  by_cases hy : y.raw = 0
  · simp [hy]
  · by_cases hfit : num.raw * x.raw < wordBound <;> simp [hy, hfit, ofWord]

end Amount

namespace Lang
variable {S X E ε : Type}

/-- Reverse `worldAfter_map` so `rw` can wrap a Core word denotation. -/
theorem worldAfter_ofWord {a : Asset} (x : Tx S X E ε Nat)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (Amount.ofWord (a := a) <$> x) ctx w :=
  (worldAfter_map (Amount.ofWord (a := a)) x ctx w).symm

end Lang

end Lsc
