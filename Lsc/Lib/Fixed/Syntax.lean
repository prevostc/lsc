import Lsc.Core.UInt256
import Lsc.Core.MapKey
import Lsc.Lib.Fixed.ScaleMode
import Lsc.Types
import Lean

namespace Lsc.Fixed

/-- Phantom tag for untagged fixed-point amounts (`Wei`, plain `Wad`). -/
inductive Untagged where

/-- Fixed-point number at `decimals` places, optionally tagged nominally per token. -/
structure Fixed (decimals : Nat) (tag : Type) where
  raw : UInt256

instance {d : Nat} {tag : Type} : Repr (Fixed d tag) := ⟨fun a _ => reprPrec a.raw 0⟩

instance {d : Nat} {tag : Type} : BEq (Fixed d tag) := ⟨fun a b => a.raw == b.raw⟩

instance {d : Nat} {tag : Type} : DecidableEq (Fixed d tag) := fun a b =>
  decidable_of_iff (a.raw = b.raw) (by constructor <;> (intro h; cases a; cases b; simp_all))

abbrev Fixed.n {d : Nat} {tag : Type} (w : Fixed d tag) : Nat := w.raw.toNat

def scale (d : Nat) : Nat := 10 ^ d

def WAD : Nat := scale 18

@[simp] theorem scale_zero : scale 0 = 1 := by simp [scale]

@[simp] theorem scale_eighteen : scale 18 = WAD := rfl

abbrev Wei := Fixed 0 Untagged
abbrev Wad := Fixed 18 Untagged

def mkNat {d : Nat} {tag : Type} (n : Nat) : Fixed d tag := ⟨BitVec.ofNat 256 n⟩

@[simp] theorem mkNat_self {d : Nat} {tag : Type} (w : Fixed d tag) :
    mkNat w.n = w := by
  simp [mkNat, Fixed.n, BitVec.ofNat_toNat]

def one {d : Nat} {tag : Type} : Fixed d tag := mkNat (scale d)

def Fixed.convert {d1 d2 : Nat} {tag : Type} (a : Fixed d1 tag) : Except ArithError (Fixed d2 tag) :=
  if d2 ≥ d1 then
    let factor := scale (d2 - d1)
    let widened := a.raw.toNat * factor
    if widened < 2 ^ 256 then .ok (mkNat widened)
    else .error .Overflow
  else
    let factor := scale (d1 - d2)
    .ok (mkNat (a.raw.toNat / factor))

def Fixed.retag {d : Nat} {t1 t2 : Type} (a : Fixed d t1) : Fixed d t2 := ⟨a.raw⟩

/-- Unified fixed-point expression AST (`.wei` and `.wad` share this type). -/
inductive Expr where
  | lit : Nat → Expr
  | var : Ident → Expr
  | storageGet : Ident → Expr
  | mapGet : Ident → MapKey → Expr
  | mapGet2 : Ident → MapKey → MapKey → Expr
  | addChecked : Expr → Expr → Expr
  | addCheckedNat : Expr → Nat → Expr
  | subChecked : Expr → Expr → Expr
  | mulHalfUpChecked : ScaleMode → Expr → Expr → Expr
  | divDownChecked : ScaleMode → Expr → Expr → Expr
  | sqrtDownChecked : ScaleMode → Expr → Expr
  | min : Expr → Expr → Expr
  deriving Repr

def arithErrors : Expr → List ArithError
  | .addChecked _ _ => [.Overflow]
  | .addCheckedNat _ _ => [.Overflow]
  | .subChecked _ _ => [.Underflow]
  | .mulHalfUpChecked _ _ _ => [.Overflow]
  | .divDownChecked _ _ _ => [.DivisionByZero, .Overflow]
  | .sqrtDownChecked _ _ => [.Overflow]
  | .min _ _ => []
  | .lit _ | .var _ | .storageGet _ | .mapGet _ _ | .mapGet2 _ _ _ => []

end Lsc.Fixed
