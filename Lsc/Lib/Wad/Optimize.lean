import Lsc.Lib.Wad.Syntax
import Lsc.Lib.Fixed.Optimize

namespace Lsc.Wad

open Lsc.Compile.IR (Expr Stmt)

def lowerExpr (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr) : Except String Compile.IR.Expr :=
  Fixed.lowerExpr fieldSlot mapFieldSlot e

def lowerAddCheckedNatStorage (slot : Nat) (n : Nat) (overflowSelector : Nat) : Stmt :=
  let old := "lsc_add_old"
  let new := "lsc_add_new"
  .seq
    (.letBind old (.sload slot))
    (.seq
      (.letBind new (.add (.local old) (.lit n)))
      (.seq
        (.ifRevertSelector (.lt (.local new) (.local old)) overflowSelector)
        (.sstore slot (.local new))))

def lowerAddCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot mapFieldSlot : Ident → Option Nat)
    (overflowSelector : Nat) : Except String Stmt :=
  Fixed.lowerAddCheckedStorage slot rhs fieldSlot mapFieldSlot overflowSelector

def lowerSubCheckedStorage (slot : Nat) (rhs : Expr) (fieldSlot mapFieldSlot : Ident → Option Nat)
    (underflowSelector : Nat) : Except String Stmt :=
  Fixed.lowerSubCheckedStorage slot rhs fieldSlot mapFieldSlot underflowSelector

end Lsc.Wad
