import Lsc3.Tx

/-!
# LSC v3 — units of measure: `Amount τ s`, `Fixed s`, `Flag`

Most DeFi accidents that are not reentrancy are decimal accidents: adding 6-decimal USDC
to 18-decimal DAI, multiplying two WAD numbers without dividing by WAD, rounding in the
protocol's disfavour. This module makes those type errors at zero runtime cost.

* `Amount τ s` is a `def` newtype over `Nat` (definitionally a word, exactly like `Address`)
  tagged with a *token marker* `τ` (any type, used only as a phantom) and a *scale* `s`
  (the denominator: `WAD = 10^18`, `USDC = 10^6`, `Q96 = 2^96`). Same-unit arithmetic only.
* `Fixed s := Amount Unit s` is a dimensionless fixed-point number (rates, ratios, prices).
  `Amount τ s * Fixed s → Amount τ s`; two amounts divide to a `Fixed s`.
* Every operation that can lose precision names its rounding direction (`mulDown`/`mulUp`,
  `divDown`/`divUp`, `rescale … .down/.up`). There is no unrounded `*`/`/` on amounts.
* `Flag` is the storage-level boolean: a `def` newtype over `Nat` with values `0`/`1`, so that
  `Core` stays a language of words and the certificate stays `rfl`. (A `Bool`-typed `Core`
  would need typed environments; deferred.)

Core stays untyped: the reifier maps these operations to the `mulDiv` primitives below with
constant scales. Phase E adds the full-precision (512-bit intermediate) `mulDiv`.
-/

namespace Lsc3

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

variable {S E ε : Type}

/-- `⌊a * b / c⌋`. Reverts on `c = 0` and, in this Phase-B version, when the intermediate
product does not fit in a word (Phase E replaces the intermediate check by a full-precision
512-bit product; the surface API does not change). -/
def mulDivDown (a b c : Nat) : Tx S E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c, w)
    else .error (.arith .overflow)

/-- `⌈a * b / c⌉`, same revert conditions as `mulDivDown`. The result always fits in a word
when the product does (`a * b / c + 1 ≤ a * b` unless `c = 1`, in which case the remainder
is zero). -/
def mulDivUp (a b c : Nat) : Tx S E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
    else .error (.arith .overflow)

@[simp] theorem run_mulDivDown (a b c : Nat) (ctx : Ctx) (w : World S E) :
    run (mulDivDown (S := S) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c, w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_mulDivUp (a b c : Nat) (ctx : Ctx) (w : World S E) :
    run (mulDivUp (S := S) (E := E) (ε := ε) a b c) ctx w =
      if c = 0 then .error (.arith .divByZero)
      else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
      else .error (.arith .overflow) := rfl

end Tx

/-! ## `Amount` -/

set_option linter.unusedVariables false in
/-- A quantity of token `τ` at scale `s`. Definitionally `Nat`; `τ` is a phantom marker type
(declare one per asset: `structure DAI`, `structure USDC`), `s` the denominator. -/
def Amount (τ : Type) (s : Nat) : Type := Nat

/-- Dimensionless fixed-point number at scale `s` (a rate, ratio or price). -/
abbrev Fixed (s : Nat) : Type := Amount Unit s

set_option linter.unusedVariables false in
/-- A price of one `τ₁` in `τ₂`, at scale `s`: `convert p a = a * p / s`. -/
def Price (τ₁ τ₂ : Type) (s : Nat) : Type := Amount Unit s

namespace Amount

variable {τ τ' : Type} {s s' : Nat}

instance : DecidableEq (Amount τ s) := inferInstanceAs (DecidableEq Nat)
instance : OfNat (Amount τ s) n := ⟨(n : Nat)⟩
instance : Repr (Amount τ s) := inferInstanceAs (Repr Nat)
instance : Inhabited (Amount τ s) := ⟨(0 : Nat)⟩
instance : LT (Amount τ s) := inferInstanceAs (LT Nat)
instance : LE (Amount τ s) := inferInstanceAs (LE Nat)
instance (a b : Amount τ s) : Decidable (a < b) := Nat.decLt a b
instance (a b : Amount τ s) : Decidable (a ≤ b) := Nat.decLe a b

/-- The raw word (number of smallest units). -/
def toNat (a : Amount τ s) : Nat := a

/-- Tag a raw word as an amount. Boundary use only (ABI decoding, tests). -/
def ofNat (n : Nat) : Amount τ s := n

/-- The scale as a value of the same fixed-point type: `one = 1.0`. -/
def one : Fixed s := s

variable {S E ε : Type}

/-! ### Same-unit checked arithmetic -/

def add (a b : Amount τ s) : Tx S E ε (Amount τ s) := Tx.addChecked a b
def sub (a b : Amount τ s) : Tx S E ε (Amount τ s) := Tx.subChecked a b

/-! ### Scaling by a dimensionless factor (`Amount τ s * Fixed s → Amount τ s`) -/

/-- `⌊a * x / s⌋`. -/
def mulDown (a : Amount τ s) (x : Fixed s) : Tx S E ε (Amount τ s) := Tx.mulDivDown a x s
/-- `⌈a * x / s⌉`. -/
def mulUp (a : Amount τ s) (x : Fixed s) : Tx S E ε (Amount τ s) := Tx.mulDivUp a x s
/-- `⌊a * s / x⌋`. -/
def divDown (a : Amount τ s) (x : Fixed s) : Tx S E ε (Amount τ s) := Tx.mulDivDown a s x
/-- `⌈a * s / x⌉`. -/
def divUp (a : Amount τ s) (x : Fixed s) : Tx S E ε (Amount τ s) := Tx.mulDivUp a s x

/-! ### Ratios of two same-unit amounts (dimensionless) -/

/-- `⌊a * s / b⌋ : Fixed s`. -/
def ratioDown (a b : Amount τ s) : Tx S E ε (Fixed s) := Tx.mulDivDown a s b
/-- `⌈a * s / b⌉ : Fixed s`. -/
def ratioUp (a b : Amount τ s) : Tx S E ε (Fixed s) := Tx.mulDivUp a s b

/-! ### Proportional shares (`a * b / c` with `b`, `c` in the same unit; vault/share math) -/

/-- `⌊a * b / c⌋`, `b` and `c` of one unit, result in `a`'s unit. -/
def shareDown (a : Amount τ s) (b c : Amount τ' s') : Tx S E ε (Amount τ s) := Tx.mulDivDown a b c
/-- `⌈a * b / c⌉`. -/
def shareUp (a : Amount τ s) (b c : Amount τ' s') : Tx S E ε (Amount τ s) := Tx.mulDivUp a b c

/-! ### Changing scale and unit -/

/-- Re-express an amount at scale `s'` (`a * s' / s`), rounding as requested. -/
def rescale (s' : Nat) (r : Rounding) (a : Amount τ s) : Tx S E ε (Amount τ s') :=
  match r with
  | .down => Tx.mulDivDown a s' s
  | .up => Tx.mulDivUp a s' s

/-- Convert `τ₁` into `τ₂` at price `p` (`a * p / s`). -/
def convert {τ₁ τ₂ : Type} (p : Price τ₁ τ₂ s) (r : Rounding) (a : Amount τ₁ s) :
    Tx S E ε (Amount τ₂ s) :=
  match r with
  | .down => Tx.mulDivDown a p s
  | .up => Tx.mulDivUp a p s

/-! ### Run lemmas (Amount ops are `def` aliases of `Tx` prims; these keep `simp` on-surface) -/

@[simp] theorem run_add (a b : Amount τ s) (ctx : Ctx) (w : World S E) :
    Tx.run (add (S := S) (E := E) (ε := ε) a b) ctx w =
      if Nat.add a b < wordBound then .ok (Nat.add a b, w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_sub (a b : Amount τ s) (ctx : Ctx) (w : World S E) :
    Tx.run (sub (S := S) (E := E) (ε := ε) a b) ctx w =
      if b ≤ a then .ok (Nat.sub a b, w) else .error (.arith .underflow) := rfl

@[simp] theorem run_shareDown (a : Amount τ s) (b c : Amount τ' s') (ctx : Ctx)
    (w : World S E) :
    Tx.run (shareDown (S := S) (E := E) (ε := ε) a b c) ctx w =
      if c = (0 : Nat) then .error (.arith .divByZero)
      else if Nat.mul a b < wordBound then .ok (Nat.div (Nat.mul a b) c, w)
      else .error (.arith .overflow) := rfl

@[simp] theorem run_shareUp (a : Amount τ s) (b c : Amount τ' s') (ctx : Ctx)
    (w : World S E) :
    Tx.run (shareUp (S := S) (E := E) (ε := ε) a b c) ctx w =
      if c = (0 : Nat) then .error (.arith .divByZero)
      else if Nat.mul a b < wordBound then
        .ok (Nat.div (Nat.mul a b) c + (if Nat.mod (Nat.mul a b) c = 0 then 0 else 1), w)
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

`a +? b` is `Tx.addChecked` on `Nat`. Because `Amount τ s` is definitionally `Nat`, that
notation typechecks on amounts but **returns `Nat`**, dropping the token/scale. Prefer
`Amount.add` / `Amount.sub`, or the scoped `+ₐ` / `-ₐ` below, whose result stays
`Amount τ s`. There is no `*ₐ` / `/ₐ`: rounding must be named (`mulDown`/`mulUp`).

This is typeclass-free so the reifier matches `Lsc3.Amount.add` (definitionally
`Tx.addChecked`) and the certificate stays `rfl`.
-/
namespace Syntax
scoped infixl:65 " +ₐ " => Lsc3.Amount.add
scoped infixl:65 " -ₐ " => Lsc3.Amount.sub
end Syntax

end Lsc3
