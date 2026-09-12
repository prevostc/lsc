import Lsc.Lang.Tx
import Lsc.Lang.Inline

/-!
# `Word` — the plain checked 256-bit word

`Word` is the unitless 256-bit base: `+? -? *? /?` revert on overflow,
underflow, or zero-division, plus `mulDivDown` / `Up` and `pow10` (revert
if the exponent exceeds 77). Quantities of an asset are `Amount a` in
`Lsc.Lang.Amount`; dimensionless fixed-point is `Fixed d`.
-/

namespace Lsc

/-- Rounding direction. Every lossy scale conversion takes one explicitly. -/
inductive Rounding
  | down
  | up
  deriving DecidableEq, Repr

/-- A 256-bit word. Reducibly `Nat`, so checked arithmetic, `simp` lemmas, and
ABI codecs need no conversion. No extra `OfNat`/`LE` instances — those would
compete with `Nat` and break numerals. -/
abbrev Word : Type := Nat

namespace Word
/-- `10^d` as a word. Meaningful as a 256-bit value for `d ≤ 77`. -/
def scale (d : Nat) : Word := (10 ^ d : Nat)

/-- `10^77` still fits in a 256-bit word; `10^78` does not. -/
theorem tenPow77_lt_wordBound : (10 : Nat) ^ 77 < wordBound := by decide

/-- `10^d` fits in a word whenever `d ≤ 77`. -/
theorem tenPow_of_le_max {d : Nat} (h : d ≤ 77) : (10 : Nat) ^ d < wordBound :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide : 0 < 10) h) tenPow77_lt_wordBound
end Word

/-- Storage boolean as a word: `0 = off`, `1 = on`. ABI type `bool`. -/
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

/-! ## `mulDiv` and `pow10` -/

namespace Tx

variable {S X E ε : Type}

/-- Largest `d` such that `10^d` fits in a word (`10^77 < 2^256 ≤ 10^78`). -/
def pow10Max : Nat := 77

/-- `⌊a * b / c⌋`. Reverts on `c = 0` and when the intermediate product does not
fit in a word. -/
def mulDivDown (a b c : Nat) : Tx S X E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c, w)
    else .error (.arith .overflow)

/-- `⌈a * b / c⌉`, same revert conditions as `mulDivDown`. -/
def mulDivUp (a b c : Nat) : Tx S X E ε Nat :=
  fun _ w =>
    if c = 0 then .error (.arith .divByZero)
    else if a * b < wordBound then .ok (a * b / c + (if a * b % c = 0 then 0 else 1), w)
    else .error (.arith .overflow)

/-- `10^d`. Reverts on overflow when `d > 77`. -/
def pow10 (d : Nat) : Tx S X E ε Nat :=
  fun _ w =>
    if d > pow10Max then .error (.arith .overflow)
    else .ok (10 ^ d, w)

/-- Re-express `a` from `srcDec` decimals to `tgtDec` decimals. Same-scale is
the identity. Otherwise `pow10` then `mulDiv`. `r` must be a literal. -/
@[lsc_inline]
def rescale (srcDec tgtDec : Nat) (r : Rounding) (a : Nat) : Tx S X E ε Nat :=
  if srcDec = tgtDec then
    pure a
  else do
    let src ← pow10 srcDec
    let tgt ← pow10 tgtDec
    match r with
    | .down => mulDivDown a tgt src
    | .up => mulDivUp a tgt src

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

@[simp] theorem run_pow10 (d : Nat) (ctx : Ctx) (w : World S X E) :
    run (pow10 (S := S) (X := X) (E := E) (ε := ε) d) ctx w =
      if d > pow10Max then .error (.arith .overflow)
      else .ok (10 ^ d, w) := rfl

end Tx

end Lsc
