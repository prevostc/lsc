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

end LscV2
