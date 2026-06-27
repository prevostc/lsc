import LscV2.Syntax

open LscV2

namespace LscV2.SyntaxTest

def incrementRequireRef : Stmt :=
  Stmt.require (Expr.not (Expr.storageGet (t := .bool) "paused")) "Paused"

def incrementLetRef : Stmt :=
  Stmt.letBind "n" ⟨Ty.wei,
    Expr.weiAddCheckedNat (Expr.storageGet (t := .wei) "number") 1⟩

def incrementSetRef : Stmt :=
  Stmt.storageSet "number" ⟨Ty.wei, Expr.var (t := .wei) "n"⟩

def incrementEmitRef : Stmt :=
  Stmt.emit "Incremented" [⟨Ty.wei, Expr.var (t := .wei) "n"⟩]

def incrementAstRef : Stmt :=
  Stmt.seq incrementRequireRef
    (Stmt.seq incrementLetRef (Stmt.seq incrementSetRef incrementEmitRef))

def pauseRequireOwnerRef : Stmt :=
  Stmt.require (Expr.eq Expr.caller (Expr.storageGet (t := .address) "owner")) "NotOwner"

def pauseEmitRef : Stmt := Stmt.emit "Paused" []

def incrementRequireMacro : Stmt := lsc! require (!$.paused) else revert Paused;
def incrementLetMacro : Stmt := lsc! let n ← $.number +? 1;
def incrementSetMacro : Stmt := lsc! $.number := n;
def incrementEmitMacro : Stmt := lsc! emit Incremented(n);
def incrementAstMacro : Stmt :=
  lsc! require (!$.paused) else revert Paused; let n ← $.number +? 1; $.number := n; emit Incremented(n);
def pauseRequireOwnerMacro : Stmt := lsc! require (msg.sender == $.owner) else revert NotOwner;
def pauseEmitMacro : Stmt := lsc! emit Paused();

example : incrementRequireMacro = incrementRequireRef := rfl
example : incrementLetMacro = incrementLetRef := rfl
example : incrementSetMacro = incrementSetRef := rfl
example : incrementEmitMacro = incrementEmitRef := rfl
example : incrementAstMacro = incrementAstRef := rfl
example : pauseRequireOwnerMacro = pauseRequireOwnerRef := rfl
example : pauseEmitMacro = pauseEmitRef := rfl

end LscV2.SyntaxTest
