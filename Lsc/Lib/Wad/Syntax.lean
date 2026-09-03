import Lsc.Lib.Fixed.Syntax
import Lsc.Lib.Fixed.ScaleMode
import Lean

namespace Lsc.Wad

open Lsc.Fixed (ScaleMode)

abbrev Wad := Fixed.Wad
abbrev Expr := Fixed.Expr

export Fixed (Untagged Fixed Fixed.n scale WAD mkNat one Fixed.convert Fixed.retag mkNat_self scale_eighteen)

def arithErrors := @Fixed.arithErrors

def mk (raw : UInt256) : Wad := ⟨raw⟩

def one : Wad := Fixed.one

def exprMulHalfUpChecked (a b : Expr) : Expr := .mulHalfUpChecked (ScaleMode.static 18) a b
def exprDivDownChecked (a b : Expr) : Expr := .divDownChecked (ScaleMode.static 18) a b
def exprSqrtDownChecked (a : Expr) : Expr := .sqrtDownChecked (ScaleMode.static 18) a

elab "declare_token_amount " id:ident : command => do
  let tagId := Lean.mkIdent (Lean.Name.mkSimple "Tag")
  Lean.Elab.Command.elabCommand (← `(
    inductive $tagId))
  Lean.Elab.Command.elabCommand (← `(abbrev $id := Lsc.Fixed.Fixed 18 $tagId))
  Lean.Elab.Command.elabCommand (← `(
    instance : Inhabited $id where default := ⟨0⟩))

end Lsc.Wad
