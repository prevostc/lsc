import Lsc.Core.UInt256
import Lsc.Types

namespace Lsc.Wei

structure Wei where
  raw : UInt256
  deriving Repr, DecidableEq

def mkNat (n : Nat) : Wei := ⟨BitVec.ofNat 256 n⟩

/-- Wei-domain expression fragment (`Expr .wei`). -/
inductive Expr where
  | lit : Nat → Expr
  | var : Ident → Expr
  | storageGet : Ident → Expr
  | addChecked : Expr → Expr → Expr
  | addCheckedNat : Expr → Nat → Expr
  | subChecked : Expr → Expr → Expr
  deriving Repr

def addCheckedNatStorage (field : Ident) (n : Nat) : Expr :=
  .addCheckedNat (.storageGet field) n

@[simp] theorem addCheckedNatStorage_eq (field : Ident) (n : Nat) :
    addCheckedNatStorage field n = .addCheckedNat (.storageGet field) n := rfl

def arithErrors : Expr → List ArithError
  | .addChecked _ _ => [.Overflow]
  | .addCheckedNat _ _ => [.Overflow]
  | .subChecked _ _ => [.Underflow]
  | _ => []

end Lsc.Wei
