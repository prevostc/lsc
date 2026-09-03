import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Math.Sqrt
import Lsc.Lib.Math.Min

namespace Lsc.Fixed

def addChecked {d : Nat} {tag : Type} (a b : Fixed d tag) : Except ArithError (Fixed d tag) :=
  (UInt256.addChecked a.raw b.raw).map (fun r => ⟨r⟩)

def subChecked {d : Nat} {tag : Type} (a b : Fixed d tag) : Except ArithError (Fixed d tag) :=
  (UInt256.subChecked a.raw b.raw).map (fun r => ⟨r⟩)

def addCheckedNat {d : Nat} {tag : Type} (a : Fixed d tag) (n : Nat) : Except ArithError (Fixed d tag) :=
  (UInt256.addCheckedNat a.raw n).map (fun r => ⟨r⟩)

def mulHalfUpChecked (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (a b : Fixed d tag) : Except ArithError (Fixed d tag) :=
  let s := scaleMode.scaleNat
  let productNat := a.n * b.n
  let resultNat := (productNat + s / 2) / s
  if resultNat > (BitVec.allOnes 256).toNat then
    .error .Overflow
  else
    .ok (mkNat resultNat)

def divDownChecked (scaleMode : ScaleMode) {d : Nat} {tag : Type}
    (a b : Fixed d tag) : Except ArithError (Fixed d tag) :=
  if b.raw == 0 then
    .error .DivisionByZero
  else
    let s := scaleMode.scaleNat
    let numerNat := a.n * s
    let resultNat := numerNat / b.n
    if resultNat > (BitVec.allOnes 256).toNat then
      .error .Overflow
    else
      .ok (mkNat resultNat)

end Lsc.Fixed
