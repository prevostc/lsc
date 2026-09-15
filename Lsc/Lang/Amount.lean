import Lean
import Lsc.Lang.Word
import Lsc.Lang.Inline

/-!
# Asset-indexed amounts

Numbers are indexed by the **asset** they denominate. The asset is a
contract-level closed constant; bindings and storage fields are typed by
it. `Amount a` is a one-field structure (an abbrev would unify every
amount back to `Word`). Same-asset `+? -?`; `*? /?` only against a `Word`
scalar; `mulDivDown` / `Up` take a numerator of asset `b` and a ratio of
two `a`s, or two `Word`s (scale 0). The fused ops are written
`num mulDiv↓ x / y` and `num mulDiv↑ x / y`. `x *?↓ r` / `x *?↑ r`
scale by a `Fixed d`. `x.as b` is the 1:1 retag when `a.decimals?` equals
`b.decimals?` at elaboration; `x.asUnchecked b` is the same retag without
that check.

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

/-- Elaboration tactic for `Amount.as`: `decide` the decimals equality, or a
readable error telling the author to use `asUnchecked`. -/
syntax "same_decimals" : tactic

macro_rules
  | `(tactic| same_decimals) =>
    `(tactic| first
        | decide
        | fail "Amount.as: decimals? must be equal (use asUnchecked)")

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

/-- 1:1 retag when `a.decimals? = b.decimals?` at elaboration; use `asUnchecked`
for a documented cross-scale relabel (an AMM first mint has no single decimals). -/
def as (x : Amount a) (b : Asset)
    (_h : a.decimals? = b.decimals? := by same_decimals) : Amount b :=
  ⟨x.raw⟩

/-- Same retag with no decimals check. Document why the conversion is sound. -/
def asUnchecked (x : Amount a) (b : Asset) : Amount b := ⟨x.raw⟩

/-- Total `⌊x * y / z⌋` on raw words (Lean: `n / 0 = 0`). -/
def floorMulDiv (x y z : Nat) : Nat := x * y / z

/-- Total `⌈x * y / z⌉` on raw words (`z = 0` yields 0). -/
def ceilMulDiv (x y z : Nat) : Nat :=
  x * y / z + if z = 0 ∨ x * y % z = 0 then 0 else 1

/-- Total `⌊x.raw * r.raw / 10^d⌋`. -/
def mulDown {d : Nat} (x : Amount a) (r : Fixed d) : Amount a :=
  ⟨floorMulDiv x.raw r.raw (Word.scale d)⟩

/-- Total `⌈x.raw * r.raw / 10^d⌉`. -/
def mulUp {d : Nat} (x : Amount a) (r : Fixed d) : Amount a :=
  ⟨ceilMulDiv x.raw r.raw (Word.scale d)⟩

@[simp] theorem raw_as (x : Amount a) (b : Asset)
    (h : a.decimals? = b.decimals?) : (as x b h).raw = x.raw := rfl
@[simp] theorem as_eq_ofWord (x : Amount a) (b : Asset)
    (h : a.decimals? = b.decimals?) : as x b h = ofWord x.raw := rfl
@[simp] theorem as_ofWord (n : Word) (b : Asset)
    (h : a.decimals? = b.decimals?) :
    as (ofWord n : Amount a) b h = ofWord n := rfl
@[simp] theorem raw_asUnchecked (x : Amount a) (b : Asset) :
    (x.asUnchecked b).raw = x.raw := rfl
@[simp] theorem asUnchecked_eq_ofWord (x : Amount a) (b : Asset) :
    x.asUnchecked b = ofWord x.raw := rfl
@[simp] theorem asUnchecked_ofWord (n : Word) (b : Asset) :
    (ofWord n : Amount a).asUnchecked b = ofWord n := rfl
@[simp] theorem mulDown_raw {d : Nat} (x : Amount a) (r : Fixed d) :
    (mulDown x r).raw = x.raw * r.raw / Word.scale d := rfl
@[simp] theorem mulUp_raw {d : Nat} (x : Amount a) (r : Fixed d) :
    (mulUp x r).raw = ceilMulDiv x.raw r.raw (Word.scale d) := rfl
@[simp] theorem raw_mk (n : Word) : (⟨n⟩ : Amount a).raw = n := rfl
@[simp] theorem mk_raw (x : Amount a) : (⟨x.raw⟩ : Amount a) = x := rfl
@[simp] theorem raw_ofWord (n : Word) : (ofWord n : Amount a).raw = n := rfl
@[simp] theorem ofWord_zero : (ofWord 0 : Amount a) = 0 := rfl
@[simp] theorem ofWord_raw (x : Amount a) : ofWord (a := a) x.raw = x := rfl
@[simp] theorem raw_add (x y : Amount a) : (x + y).raw = x.raw + y.raw := rfl
@[simp] theorem raw_sub (x y : Amount a) : (x - y).raw = x.raw - y.raw := rfl
@[simp] theorem raw_mul (x y : Amount a) : (x * y).raw = x.raw * y.raw := rfl
@[simp] theorem raw_ofNat (n : Nat) : (OfNat.ofNat n : Amount a).raw = n := rfl
@[simp] theorem raw_one : (1 : Amount a).raw = 1 := rfl
@[simp] theorem raw_zero : (0 : Amount a).raw = 0 := rfl
@[simp] theorem ofWord_eq_zero (n : Word) : (ofWord n : Amount a) = 0 ↔ n = 0 :=
  ⟨fun h => by
    have := congrArg Amount.raw h
    simp only [raw_ofWord, raw_zero] at this
    exact this,
   fun h => h ▸ ofWord_zero⟩
@[simp] theorem add_zero (x : Amount a) : x + 0 = x := Amount.ext (by simp)
@[simp] theorem zero_add (x : Amount a) : 0 + x = x := Amount.ext (by simp)
@[simp] theorem sub_zero (x : Amount a) : x - 0 = x := Amount.ext (by simp)
@[simp] theorem mk_add (x y : Amount a) : (⟨x.raw + y.raw⟩ : Amount a) = x + y := rfl
@[simp] theorem mk_sub (x y : Amount a) : (⟨x.raw - y.raw⟩ : Amount a) = x - y := rfl
@[simp] theorem ofWord_add (x y : Amount a) : ofWord (x.raw + y.raw) = x + y := rfl
@[simp] theorem ofWord_add_left (x : Amount a) (n : Word) :
    ofWord (x.raw + n) = x + ofWord n := rfl
@[simp] theorem ofWord_add_right (n : Word) (x : Amount a) :
    ofWord (n + x.raw) = ofWord n + x := rfl
@[simp] theorem ofWord_sub (x y : Amount a) : ofWord (x.raw - y.raw) = x - y := rfl
@[simp] theorem ofWord_sub_right (n : Word) (x : Amount a) :
    ofWord (n - x.raw) = ofWord n - x := rfl
@[simp] theorem ofWord_sub_left (x : Amount a) (n : Word) :
    ofWord (x.raw - n) = x - ofWord n := rfl

theorem raw_sub_add {x y : Amount a} (h : y.raw ≤ x.raw) : (x - y + y).raw = x.raw :=
  Nat.sub_add_cancel h
@[simp] theorem lt_iff (x y : Amount a) : x < y ↔ x.raw < y.raw := Iff.rfl
@[simp] theorem le_iff (x y : Amount a) : x ≤ y ↔ x.raw ≤ y.raw := Iff.rfl
theorem eq_iff (x y : Amount a) : x = y ↔ x.raw = y.raw :=
  ⟨fun h => h ▸ rfl, ext⟩
theorem ne_iff (x y : Amount a) : x ≠ y ↔ x.raw ≠ y.raw :=
  not_congr (eq_iff x y)

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

/-- Pointwise form of `update_raw`. -/
theorem ofWord_update_lookup {K : Type} [DecidableEq K] (m : K → Amount a)
    (k k' : K) (n : Word) :
    ofWord (Function.update (fun i => (m i).raw) k n k') =
      Function.update m k (ofWord n) k' :=
  congrFun (update_raw m k n) k'

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

/-- `⌊x * r / 10^d⌋`. Reverts on product overflow; `10^d ≠ 0`. -/
@[lsc_inline]
def mulFixedDown {d : Nat} (x : Amount a) (r : Fixed d) : Tx S X E ε (Amount a) :=
  mulDivDown x r (ofWord (Word.scale d))

/-- `⌈x * r / 10^d⌉`. Reverts on product overflow; `10^d ≠ 0`. -/
@[lsc_inline]
def mulFixedUp {d : Nat} (x : Amount a) (r : Fixed d) : Tx S X E ε (Amount a) :=
  mulDivUp x r (ofWord (Word.scale d))

instance : Tx.HAddChecked S X E ε (Amount a) (Amount a) (Amount a) where
  hAdd := add
instance : Tx.HSubChecked S X E ε (Amount a) (Amount a) (Amount a) where
  hSub := sub
instance : Tx.HMulChecked S X E ε (Amount a) Word (Amount a) where
  hMul := mulScalar
instance : Tx.HDivChecked S X E ε (Amount a) Word (Amount a) where
  hDiv := divScalar
instance : Tx.HMulDivDown S X E ε (Amount b) (Amount a) (Amount a) (Amount b) where
  hMulDivDown := mulDivDown
instance : Tx.HMulDivUp S X E ε (Amount b) (Amount a) (Amount a) (Amount b) where
  hMulDivUp := mulDivUp
/-- Scale-0 ratio: `num mulDiv↓ 9970 / 10000` with plain `Word`s. -/
instance (priority := 2000) : Tx.HMulDivDown S X E ε (Amount b) Word Word (Amount b) where
  hMulDivDown num x y :=
    mulDivDown (a := Asset.fixed 0) num (ofWord x) (ofWord y)
instance (priority := 2000) : Tx.HMulDivUp S X E ε (Amount b) Word Word (Amount b) where
  hMulDivUp num x y :=
    mulDivUp (a := Asset.fixed 0) num (ofWord x) (ofWord y)
instance {d : Nat} : Tx.HMulFixedDown S X E ε (Amount a) (Fixed d) (Amount a) where
  hMulFixedDown := mulFixedDown
instance {d : Nat} : Tx.HMulFixedUp S X E ε (Amount a) (Fixed d) (Amount a) where
  hMulFixedUp := mulFixedUp

variable {S X E ε : Type}

@[simp] theorem hAdd_def (x y : Amount a) :
    Tx.HAddChecked.hAdd (S := S) (X := X) (E := E) (ε := ε) x y = add x y := rfl
@[simp] theorem hSub_def (x y : Amount a) :
    Tx.HSubChecked.hSub (S := S) (X := X) (E := E) (ε := ε) x y = sub x y := rfl
@[simp] theorem hMul_def (x : Amount a) (k : Word) :
    Tx.HMulChecked.hMul (S := S) (X := X) (E := E) (ε := ε) x k = mulScalar x k := rfl
@[simp] theorem hDiv_def (x : Amount a) (k : Word) :
    Tx.HDivChecked.hDiv (S := S) (X := X) (E := E) (ε := ε) x k = divScalar x k := rfl
@[simp] theorem hMulDivDown_def (num : Amount b) (x y : Amount a) :
    Tx.HMulDivDown.hMulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y =
      mulDivDown num x y :=
  rfl
@[simp] theorem hMulDivUp_def (num : Amount b) (x y : Amount a) :
    Tx.HMulDivUp.hMulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y =
      mulDivUp num x y :=
  rfl
@[simp] theorem hMulDivDown_word (num : Amount b) (x y : Word) :
    Tx.HMulDivDown.hMulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y =
      mulDivDown (a := Asset.fixed 0) num (ofWord x) (ofWord y) :=
  rfl
@[simp] theorem hMulDivUp_word (num : Amount b) (x y : Word) :
    Tx.HMulDivUp.hMulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y =
      mulDivUp (a := Asset.fixed 0) num (ofWord x) (ofWord y) :=
  rfl
@[simp] theorem hMulFixedDown_def {d : Nat} (x : Amount a) (r : Fixed d) :
    Tx.HMulFixedDown.hMulFixedDown (S := S) (X := X) (E := E) (ε := ε) x r =
      mulFixedDown x r :=
  rfl
@[simp] theorem hMulFixedUp_def {d : Nat} (x : Amount a) (r : Fixed d) :
    Tx.HMulFixedUp.hMulFixedUp (S := S) (X := X) (E := E) (ε := ε) x r =
      mulFixedUp x r :=
  rfl

end Amount

namespace Syntax
scoped infixl:70 " *↓ " => Lsc.Amount.mulDown
scoped infixl:70 " *↑ " => Lsc.Amount.mulUp
end Syntax

end Lsc
