import LscV1.UInt256

namespace LscV1

/-- Encode a logical slot value into a single EVM storage word. -/
class ToWord (α : Type) where
  toWord : α → UInt256

/-- Decode a storage word into a logical slot value. -/
class FromWord (α : Type) where
  fromWord : UInt256 → α

instance : ToWord UInt256 where
  toWord := id

instance : FromWord UInt256 where
  fromWord := id

def Bool.toWord (b : Bool) : UInt256 :=
  if b then UInt256.one else UInt256.zero

def UInt256.toBool (w : UInt256) : Bool :=
  w.val ≠ 0

instance : ToWord Bool where
  toWord := Bool.toWord

instance : FromWord Bool where
  fromWord := UInt256.toBool

@[simp] theorem Bool.toWord_false : Bool.toWord false = UInt256.zero := rfl

@[simp] theorem Bool.toWord_true : Bool.toWord true = UInt256.one := rfl

@[simp] theorem UInt256.toBool_zero : UInt256.toBool UInt256.zero = false := by
  simp [UInt256.toBool, UInt256.zero_val]

@[simp] theorem UInt256.toBool_one : UInt256.toBool UInt256.one = true := by
  simp [UInt256.toBool, UInt256.one_val]

@[simp] theorem fromWord_toWord (b : Bool) : FromWord.fromWord (ToWord.toWord b) = b := by
  cases b <;> rfl

@[simp] theorem fromWord_toWord_UInt256 (v : UInt256) : (FromWord.fromWord (ToWord.toWord v) : UInt256) = v := rfl

end LscV1
