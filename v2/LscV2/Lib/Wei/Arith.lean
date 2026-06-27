import LscV2.Lib.Wei.Type

namespace LscV2.Wei

def addChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.addChecked a.raw b.raw).map Wei.mk

def subChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.subChecked a.raw b.raw).map Wei.mk

def mulChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.mulChecked a.raw b.raw).map Wei.mk

def divFloor (a b : Wei) : Except ArithError Wei :=
  (UInt256.divChecked a.raw b.raw).map Wei.mk

def addCheckedNat (a : Wei) (n : Nat) : Except ArithError Wei :=
  (UInt256.addCheckedNat a.raw n).map Wei.mk

@[simp]
theorem addCheckedNat_ok (a : Wei) (n : Nat) (h : a.raw.toNat + n < 2 ^ 256) :
    addCheckedNat a n = .ok ⟨BitVec.ofNat 256 (a.raw.toNat + n)⟩ := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

@[simp]
theorem addCheckedNat_error (a : Wei) (n : Nat) (h : ¬ a.raw.toNat + n < 2 ^ 256) :
    addCheckedNat a n = .error .Overflow := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

end LscV2.Wei
