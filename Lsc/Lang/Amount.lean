import Lsc.Lang.Tx

/-!
# units of measure: `Amount τ s`, `Fixed s`, `Flag`

Most DeFi accidents that are not reentrancy are decimal accidents: adding 6-decimal USDC
to 18-decimal DAI, multiplying two WAD numbers without dividing by WAD, rounding in the
protocol's disfavour. This module makes those type errors at zero runtime cost.

* `Amount τ s` is a `structure` over `Nat` tagged with a *token marker* `τ` (any type, used
  only as a phantom) and a *scale* `s` (the denominator: `WAD = 10^18`, `USDC = 10^6`).
  Same-unit arithmetic only. A `def` newtype would unify with `Nat` and across units.
* `Fixed s := Amount Unit s` is a dimensionless fixed-point number (rates, ratios, prices).
  `Amount τ s * Fixed s → Amount τ s`; two amounts divide to a `Fixed s`.
* Every operation that can lose precision names its rounding direction (`mulDown`/`mulUp`,
  `divDown`/`divUp`, `rescale … .down/.up`). There is no unrounded `*`/`/` on amounts.
* `Flag` is the storage-level boolean: a `def` newtype over `Nat` with values `0`/`1`, so that
  `Core` stays a language of words and the certificate stays `rfl`. (A `Bool`-typed `Core`
  would need typed environments; deferred.)

The compiler denotation is still `Core.denote` into `Nat`. Amount-typed certificates use
`Core.denoteAWord` / `Core.denoteAUnit` (`toNat` on parameters; `ofNat` at each word op).
-/

namespace Lsc

/-! ## Scales -/

/-- 18 decimals (DAI, WETH, most ERC20s). -/
def WAD : Nat := 10 ^ 18
/-- 27 decimals (Aave/MakerDAO rates). -/
def RAY : Nat := 10 ^ 27
/-- 6 decimals (USDC, USDT). -/
def USDC_SCALE : Nat := 10 ^ 6
/-- Uniswap v3 Q64.96 fixed point. -/
def Q96 : Nat := 2 ^ 96
/-- 8 decimals (WBTC, Chainlink USD feeds). -/
def E8 : Nat := 10 ^ 8

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

/-! ### Scaling by a dimensionless factor (`Amount τ s * Fixed s → Amount τ s`) -/

/-- `⌊a * x / s⌋`. `s` is passed as a runtime word. -/
def mulDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat x.toNat s
/-- `⌈a * x / s⌉`. -/
def mulUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat x.toNat s
/-- `⌊a * s / x⌋`. -/
def divDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat s x.toNat
/-- `⌈a * s / x⌉`. -/
def divUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat s x.toNat

/-! ### Ratios of two same-unit amounts (dimensionless) -/

/-- `⌊a * s / b⌋ : Fixed s`. -/
def ratioDown (a b : Amount τ s) : Tx S X E ε (Fixed s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat s b.toNat
/-- `⌈a * s / b⌉ : Fixed s`. -/
def ratioUp (a b : Amount τ s) : Tx S X E ε (Fixed s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat s b.toNat

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

/-! ### Changing scale and unit -/

/-- Re-express an amount at another scale (`a * tgtScale / srcScale`), rounding as requested.
Both scales are runtime words. -/
def rescale (srcScale tgtScale : Nat) (r : Rounding) (a : Amount τ s) :
    Tx S X E ε (Amount τ s') :=
  match r with
  | .down => (fun n => ofNat n) <$> Tx.mulDivDown a.toNat tgtScale srcScale
  | .up => (fun n => ofNat n) <$> Tx.mulDivUp a.toNat tgtScale srcScale

/-- Convert `τ₁` into `τ₂` at price `p` (`a * p / s`). `s` is a runtime word. -/
def convert {τ₁ τ₂ : Type} (p : Price τ₁ τ₂ s) (scale : Nat) (r : Rounding)
    (a : Amount τ₁ s) : Tx S X E ε (Amount τ₂ s) :=
  match r with
  | .down => (fun n => ofNat n) <$> Tx.mulDivDown a.toNat p.toNat scale
  | .up => (fun n => ofNat n) <$> Tx.mulDivUp a.toNat p.toNat scale

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
