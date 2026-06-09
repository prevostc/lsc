import Lsc.UInt256

namespace Lsc

structure Address where
  val : UInt256
  deriving Repr, DecidableEq

def Address.zero : Address := ⟨UInt256.mk 0 (by decide)⟩

/-- Default executing contract address for proofs (v0 test harness). -/
def defaultSelf : Address := Address.zero

/-- Whole simulated chain state — all accounts' storage, balances, and code. -/
structure World where
  storage : Address → Nat → UInt256
  balance : Address → UInt256
  code    : Address → ByteArray

namespace World

def empty : World where
  storage := fun _ _ => UInt256.mk 0 (by decide)
  balance := fun _ => UInt256.mk 0 (by decide)
  code    := fun _ => ByteArray.empty

def getStorage (w : World) (addr : Address) (slot : Nat) : UInt256 :=
  w.storage addr slot

def setStorage (w : World) (addr : Address) (slot : Nat) (v : UInt256) : World :=
  { w with storage := fun a s => if a == addr && s == slot then v else w.storage a s }

@[simp] theorem getStorage_setStorage (w : World) (addr : Address) (slot : Nat) (v : UInt256) :
    getStorage (setStorage w addr slot v) addr slot = v := by
  simp [getStorage, setStorage]

@[simp] theorem getStorage_setStorage_ne (w : World) (addr : Address)
    {s₁ s₂ : Nat} (v : UInt256) (h : s₁ ≠ s₂) :
    getStorage (setStorage w addr s₁ v) addr s₂ = getStorage w addr s₂ := by
  simp only [getStorage, setStorage]
  simp only [Bool.and_eq_true, beq_iff_eq, beq_self_eq_true, true_and]
  exact if_neg (Ne.symm h)

end World

end Lsc
