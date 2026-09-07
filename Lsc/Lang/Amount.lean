import Lsc.Lang.Tx

/-!
# units of measure: `Amount τ s`, `Fixed s`, `Flag`

Most DeFi accidents that are not reentrancy are decimal accidents: adding 6-decimal USDC
to 18-decimal DAI, multiplying two WAD numbers without dividing by WAD, rounding in the
protocol's disfavour. This module makes those type errors at zero runtime cost.

* `Amount τ s` is a `structure` over `Nat` tagged with a *token marker* `τ` (any type, used
  only as a phantom) and a *scale* `s` (the denominator). Same-unit arithmetic only.
  Named scales (`WAD`, `RAY`, …) and derived ops (`mulDown`, `rescale`, `convert`, …) live
  in `Stdlib.Scales`.
* `Fixed s := Amount Unit s` is a dimensionless fixed-point number (rates, ratios, prices).
* `Flag` is the storage-level boolean: a `def` newtype over `Nat` with values `0`/`1`, so that
  `Core` stays a language of words and the certificate stays `rfl`.

The compiler denotation is still `Core.denote` into `Nat`. Amount-typed certificates use
`Core.denoteAWord` / `Core.denoteAUnit` (`toNat` on parameters; `ofNat` at each word op).
`denoteA` uses `Amount.add` / `sub` / `shareDown` / `shareUp` and `Tx.mulDivDown` / `Up`.
-/

namespace Lsc

/-- Rounding direction. Every lossy operation on amounts takes one explicitly. -/
inductive Rounding
  | down
  | up
  deriving DecidableEq, Repr

/-! ## `mulDiv` primitives (the only lossy word operations in the language) -/

namespace Tx

variable {S X E ε : Type}

/-- `⌊a * b / c⌋`. Reverts on `c = 0` and, in this Phase-B version, when the intermediate
product does not fit in a word (Phase E replaces the intermediate check by a full-precision
512-bit product; the surface API does not change). -/
def mulDivDown (a b c : Nat) : Tx S X E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c, w)
    else .error (.arith .overflow)

/-- `⌈a * b / c⌉`, same revert conditions as `mulDivDown`. The result always fits in a word
when the product does (`a * b / c + 1 ≤ a * b` unless `c = 1`, in which case the remainder
is zero). -/
def mulDivUp (a b c : Nat) : Tx S X E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
    else .error (.arith .overflow)

@[simp] theorem run_mulDivDown (a b c : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulDivDown (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c, w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_mulDivUp (a b c : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulDivUp (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
      else .error (.arith .overflow) := rfl

end Tx

/-! ## `Amount` -/

set_option linter.unusedVariables false in
/-- A quantity of token `τ` at scale `s`. A `structure` so mixed-unit arithmetic is a
type error; `τ` is a phantom marker (declare one per asset: `structure DAI`), `s` the
denominator. Core denotes into `Nat`; `toNat`/`ofNat` are the boundary. -/
structure Amount (τ : Type) (s : Nat) where
  toNat : Nat

/-- Dimensionless fixed-point number at scale `s` (a rate, ratio or price). -/
abbrev Fixed (s : Nat) : Type := Amount Unit s

set_option linter.unusedVariables false in
/-- A price of one `τ₁` in `τ₂`, at scale `s`: `convert p a = a * p / s`. -/
def Price (τ₁ τ₂ : Type) (s : Nat) : Type := Amount Unit s

namespace Amount

variable {τ τ' : Type} {s s' : Nat}

instance : DecidableEq (Amount τ s) := fun a b =>
  if h : a.toNat = b.toNat then
    isTrue (by cases a; cases b; subst h; rfl)
  else
    isFalse (by intro h'; cases a; cases b; exact h (Amount.mk.inj h'))
instance : OfNat (Amount τ s) n := ⟨⟨n⟩⟩
instance : Repr (Amount τ s) where
  reprPrec a := reprPrec a.toNat
instance : Inhabited (Amount τ s) := ⟨⟨0⟩⟩
instance : LT (Amount τ s) where
  lt a b := a.toNat < b.toNat
instance : LE (Amount τ s) where
  le a b := a.toNat ≤ b.toNat
instance (a b : Amount τ s) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance (a b : Amount τ s) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat

/-- Tag a raw word as an amount. Boundary use only (ABI decoding, tests). -/
def ofNat (n : Nat) : Amount τ s := ⟨n⟩

/-- The scale as a value of the same fixed-point type: `one scale = 1.0`. The scale is a
runtime word (not the type index), so opaque external scales stay out of Core literals. -/
def one (scale : Nat) : Amount τ s := ⟨scale⟩

@[simp] theorem toNat_mk (n : Nat) : (⟨n⟩ : Amount τ s).toNat = n := rfl
@[simp] theorem mk_toNat (a : Amount τ s) : ⟨a.toNat⟩ = a := rfl
@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n : Amount τ s).toNat = n := rfl
@[simp] theorem ofNat_toNat (a : Amount τ s) : ofNat (τ := τ) (s := s) a.toNat = a := rfl

variable {S X E ε : Type}

/-! ### Same-unit checked arithmetic -/

def add (a b : Amount τ s) : Tx S X E ε (Amount τ s) :=
  fun _ w =>
    if a.toNat + b.toNat < wordBound then .ok (ofNat (a.toNat + b.toNat), w)
    else .error (.arith .overflow)
def sub (a b : Amount τ s) : Tx S X E ε (Amount τ s) :=
  fun _ w =>
    if b.toNat ≤ a.toNat then .ok (ofNat (a.toNat - b.toNat), w)
    else .error (.arith .underflow)

/-! ### Proportional shares (`a * b / c` with `b`, `c` in the same unit; vault/share math) -/

/-- `⌊a * b / c⌋`, `b` and `c` of one unit, result in `a`'s unit. -/
def shareDown (a : Amount τ s) (b c : Amount τ' s') : Tx S X E ε (Amount τ s) :=
  fun _ w =>
    if c.toNat = 0 then .error (.arith .divByZero)
    else if a.toNat * b.toNat < wordBound then
      .ok (ofNat (a.toNat * b.toNat / c.toNat), w)
    else .error (.arith .overflow)
/-- `⌈a * b / c⌉`. -/
def shareUp (a : Amount τ s) (b c : Amount τ' s') : Tx S X E ε (Amount τ s) :=
  fun _ w =>
    if c.toNat = 0 then .error (.arith .divByZero)
    else if a.toNat * b.toNat < wordBound then
      .ok (ofNat (a.toNat * b.toNat / c.toNat +
        (if a.toNat * b.toNat % c.toNat = 0 then 0 else 1)), w)
    else .error (.arith .overflow)

/-! ### Run lemmas (Amount ops wrap `Tx` prims with `toNat`/`ofNat`) -/

@[simp] theorem run_add (a b : Amount τ s) (ctx : Ctx) (w : World S X E) :
    Tx.run (add (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if toNat a + toNat b < wordBound then .ok (ofNat (toNat a + toNat b), w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_sub (a b : Amount τ s) (ctx : Ctx) (w : World S X E) :
    Tx.run (sub (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if toNat b ≤ toNat a then .ok (ofNat (toNat a - toNat b), w)
      else .error (.arith .underflow) := rfl

@[simp] theorem run_shareDown (a : Amount τ s) (b c : Amount τ' s') (ctx : Ctx)
    (w : World S X E) :
    Tx.run (shareDown (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if toNat c = 0 then .error (.arith .divByZero)
      else if toNat a * toNat b < wordBound then
        .ok (ofNat (toNat a * toNat b / toNat c), w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_shareUp (a : Amount τ s) (b c : Amount τ' s') (ctx : Ctx)
    (w : World S X E) :
    Tx.run (shareUp (S := S) (X := X) (E := E) (ε := ε) a b c) ctx w =
      if toNat c = 0 then .error (.arith .divByZero)
      else if toNat a * toNat b < wordBound then
        .ok (ofNat (toNat a * toNat b / toNat c +
          (if toNat a * toNat b % toNat c = 0 then 0 else 1)), w)
      else .error (.arith .overflow) := rfl

end Amount

/-! ## `Flag` -/

/-- Storage boolean as a word: `0 = off`, `1 = on`. Definitionally `Nat`; ABI type `bool`. -/
def Flag : Type := Nat

namespace Flag
instance : DecidableEq Flag := inferInstanceAs (DecidableEq Nat)
instance : Repr Flag := inferInstanceAs (Repr Nat)
instance : Inhabited Flag := ⟨(0 : Nat)⟩
/-- The set flag. -/
def on : Flag := (1 : Nat)
/-- The cleared flag (the storage default). -/
def off : Flag := (0 : Nat)
end Flag

/-! ### Unit-preserving surface sugar

`a +? b` is `Tx.addChecked` on `Nat` and does not typecheck on `Amount`. Prefer
`Amount.add` / `Amount.sub`, or the scoped `+ₐ` / `-ₐ` below, whose result stays
`Amount τ s`. There is no `*ₐ` / `/ₐ`: rounding must be named (`mulDown`/`mulUp`).
-/
namespace Syntax
scoped infixl:65 " +ₐ " => Lsc.Amount.add
scoped infixl:65 " -ₐ " => Lsc.Amount.sub
end Syntax

end Lsc
