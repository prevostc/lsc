import LscV2.Types

namespace LscV2

inductive ArithError
  | Overflow
  | Underflow
  | DivisionByZero
  deriving Repr, DecidableEq

namespace UInt256

def addChecked (a b : UInt256) : Except ArithError UInt256 :=
  let r := a + b
  if r < a then .error .Overflow else .ok r

def subChecked (a b : UInt256) : Except ArithError UInt256 :=
  if a < b then .error .Underflow else .ok (a - b)

def mulChecked (a b : UInt256) : Except ArithError UInt256 :=
  let r := a * b
  if a != 0 && r / a != b then .error .Overflow else .ok r

def divChecked (a b : UInt256) : Except ArithError UInt256 :=
  if b == 0 then .error .DivisionByZero else .ok (a / b)

def mulDiv (a b c : UInt256) : Except ArithError UInt256 :=
  if c == 0 then
    .error .DivisionByZero
  else
    let r : Nat := a.toNat * b.toNat / c.toNat
    if r > (BitVec.allOnes 256).toNat then
      .error .Overflow
    else
      .ok (BitVec.ofNat 256 r)

def addCheckedNat (a : UInt256) (n : Nat) : Except ArithError UInt256 :=
  let sum := a.toNat + n
  if _h : sum < 2 ^ 256 then
    .ok (BitVec.ofNat 256 sum)
  else
    .error .Overflow

@[simp]
theorem addCheckedNat_ok (a : UInt256) (n : Nat) (h : a.toNat + n < 2 ^ 256) :
    addCheckedNat a n = .ok (BitVec.ofNat 256 (a.toNat + n)) := by
  simp [addCheckedNat, h]

@[simp]
theorem addCheckedNat_error (a : UInt256) (n : Nat) (h : ¬ a.toNat + n < 2 ^ 256) :
    addCheckedNat a n = .error .Overflow := by
  simp [addCheckedNat, h]

end UInt256

def WAD : UInt256 := BitVec.ofNat 256 1_000_000_000_000_000_000
def RAY : UInt256 := BitVec.ofNat 256 1_000_000_000_000_000_000_000_000_000

structure Wei where
  raw : UInt256
  deriving Repr, DecidableEq

namespace Wei

def mkNat (n : Nat) : Wei := ⟨BitVec.ofNat 256 n⟩

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

end Wei

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

structure Ray where
  raw : UInt256
  deriving Repr, DecidableEq

namespace Wad

def addChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.addChecked a.raw b.raw).map Wad.mk

def subChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.subChecked a.raw b.raw).map Wad.mk

def mulDown (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw b.raw WAD).map Wad.mk

def divDown (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw WAD b.raw).map Wad.mk

def mulUp (_a _b : Wad) : Except ArithError Wad := sorry
def mulHalfUp (_a _b : Wad) : Except ArithError Wad := sorry
def divUp (_a _b : Wad) : Except ArithError Wad := sorry
def divHalfUp (_a _b : Wad) : Except ArithError Wad := sorry

end Wad

namespace Ray

def addChecked (a b : Ray) : Except ArithError Ray :=
  (UInt256.addChecked a.raw b.raw).map Ray.mk

def subChecked (a b : Ray) : Except ArithError Ray :=
  (UInt256.subChecked a.raw b.raw).map Ray.mk

def mulDown (_a _b : Ray) : Except ArithError Ray := sorry
def mulUp (_a _b : Ray) : Except ArithError Ray := sorry
def mulHalfUp (_a _b : Ray) : Except ArithError Ray := sorry
def divDown (_a _b : Ray) : Except ArithError Ray := sorry
def divUp (_a _b : Ray) : Except ArithError Ray := sorry
def divHalfUp (_a _b : Ray) : Except ArithError Ray := sorry

end Ray

end LscV2
