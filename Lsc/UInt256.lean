namespace Lsc

abbrev UInt256 := { n : Nat // n < 2 ^ 256 }

namespace UInt256

def val (a : UInt256) : Nat := a.1

def mk (n : Nat) (h : n < 2 ^ 256) : UInt256 := ⟨n, h⟩

def zero : UInt256 := mk 0 (by decide)

def one : UInt256 := mk 1 (by decide)

def max : UInt256 := mk (2 ^ 256 - 1) (by omega)

@[simp] theorem zero_val : zero.val = 0 := rfl

@[simp] theorem one_val : one.val = 1 := rfl

@[simp] theorem eq_iff {a b : UInt256} : a = b ↔ a.val = b.val := Subtype.ext_iff

instance : DecidableEq UInt256 := fun a b =>
  decidable_of_iff (a.val = b.val) UInt256.eq_iff.symm

instance : LE UInt256 where
  le a b := a.val ≤ b.val

instance : LT UInt256 where
  lt a b := a.val < b.val

@[simp] theorem le_iff {a b : UInt256} : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

@[simp] theorem lt_iff {a b : UInt256} : a < b ↔ a.val < b.val := Iff.rfl

/-- Proof-only literal add (theorem-side; requires explicit bound). Not for contract `+?` code. -/
def addNat (a : UInt256) (n : Nat) (h : a.val + n < 2 ^ 256) : UInt256 :=
  mk (a.val + n) h

end UInt256

end Lsc
