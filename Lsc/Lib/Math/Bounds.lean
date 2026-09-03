import Lsc.Lib.Fixed.Arith

namespace Lsc.Math.Bounds

open Lsc.Fixed

def u256Bound : Nat := 2 ^ 256
def u256Max : Nat := u256Bound - 1

def sqrtArg (scale x : Nat) : Nat :=
  if scale == 1 then x else x * scale

def canSqrtDown (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (x : Fixed d tag) : Prop :=
  sqrtArg scaleMode.scaleNat x.n < u256Bound

def canMulHalfUp (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (a b : Fixed d tag) : Prop :=
  (a.n * b.n + scaleMode.scaleNat / 2) / scaleMode.scaleNat < u256Bound

def sqrtProductSpec (a b : Wad) : Except ArithError Wad := do
  let product ← mulHalfUpChecked (.static 18) a b
  sqrtDown (.static 18) product

def canSqrtProduct (a b : Wad) : Prop :=
  canMulHalfUp (.static 18) a b ∧
    canSqrtDown (.static 18)
      (mkNat ((a.n * b.n + ScaleMode.scaleNat (.static 18) / 2) /
        ScaleMode.scaleNat (.static 18)) : Wad)

end Lsc.Math.Bounds
