import Lsc.Lib.Fixed.Syntax

namespace Lsc.Wei

abbrev Wei := Fixed.Wei
abbrev Expr := Fixed.Expr

def mkNat (n : Nat) : Wei := Fixed.mkNat n

def arithErrors := @Fixed.arithErrors

def addCheckedNatStorage (field : Ident) (n : Nat) : Expr :=
  .addCheckedNat (.storageGet field) n

@[simp] theorem addCheckedNatStorage_eq (field : Ident) (n : Nat) :
    addCheckedNatStorage field n = .addCheckedNat (.storageGet field) n := rfl

end Lsc.Wei
