import LscV2.AST
import LscV2.Eval
import Lean

open Lean

namespace LscV2.DSL

declare_syntax_cat lsc_ty
declare_syntax_cat lsc_expr
declare_syntax_cat lsc_stmt
declare_syntax_cat lsc_store_ref
declare_syntax_cat lsc_field_decl
declare_syntax_cat lsc_error_decl
declare_syntax_cat lsc_event_decl
declare_syntax_cat lsc_func_decl
declare_syntax_cat lsc_contract_body

syntax "$." ident : lsc_store_ref
syntax lsc_store_ref : lsc_expr

syntax "UInt256" : lsc_ty
syntax "Bool" : lsc_ty
syntax "Address" : lsc_ty
syntax "Wei" : lsc_ty
syntax "Wad" : lsc_ty
syntax "Ray" : lsc_ty

syntax num : lsc_expr
syntax ident : lsc_expr

syntax lsc_stmt lsc_stmt : lsc_stmt
syntax "let" ident "←" lsc_store_ref "+?" num ";" : lsc_stmt
syntax lsc_store_ref ":=" lsc_expr ";" : lsc_stmt
syntax "emit" ident "(" lsc_expr ")" ";" : lsc_stmt
syntax "do" lsc_stmt : lsc_stmt
syntax "skip" ";" : lsc_stmt

syntax ident ":" lsc_ty (":=" num)? : lsc_field_decl
syntax "|" ident : lsc_error_decl
syntax "|" ident "(" ident ":" lsc_ty ")" : lsc_event_decl
syntax "def" ident ":" "Tx" ":=" "do" lsc_stmt : lsc_func_decl

syntax "storage" ":" lsc_field_decl+
     "errors" ":" lsc_error_decl+
     "events" ":" lsc_event_decl+
     lsc_func_decl+ : lsc_contract_body

syntax "contract" ident "where" lsc_contract_body : command

partial def expandLscExpr (stx : TSyntax `lsc_expr) : MacroM (TSyntax `term) := do
  match ← expandMacro? stx.raw with
  | some expanded =>
    if expanded == stx.raw then return ⟨expanded⟩
    else expandLscExpr ⟨expanded⟩
  | none => return ⟨stx.raw⟩

partial def expandLscStmt (stx : TSyntax `lsc_stmt) : MacroM (TSyntax `term) := do
  match ← expandMacro? stx.raw with
  | some expanded =>
    if expanded == stx.raw then return ⟨expanded⟩
    else expandLscStmt ⟨expanded⟩
  | none => return ⟨stx.raw⟩

macro_rules
  | `(lsc_ty| UInt256) => `(LscV2.Ty.uint256)
  | `(lsc_ty| Bool) => `(LscV2.Ty.bool)
  | `(lsc_ty| Address) => `(LscV2.Ty.address)
  | `(lsc_ty| Wei) => `(LscV2.Ty.wei)
  | `(lsc_ty| Wad) => `(LscV2.Ty.wad)
  | `(lsc_ty| Ray) => `(LscV2.Ty.ray)

macro_rules
  | `(lsc_expr| $. $f:ident) =>
      `(@LscV2.Expr.storageGet LscV2.Ty.wei $(quote f.getId.toString))
  | `(lsc_expr| $i:ident) =>
      `(@LscV2.Expr.var LscV2.Ty.wei $(quote i.getId.toString))

macro_rules
  | `(lsc_stmt| let $i:ident ← $. $f:ident +? $d:num;) =>
      `(LscV2.Stmt.letBind $(quote i.getId.toString)
        (LscV2.Ty.wei,
          @LscV2.Expr.weiAddCheckedNat (@LscV2.Expr.storageGet LscV2.Ty.wei $(quote f.getId.toString)) $(quote d.getNat)))

macro_rules
  | `(lsc_stmt| $. $f:ident := $e:lsc_expr;) => do
      let e ← expandLscExpr e
      `(LscV2.Stmt.storageSet $(quote f.getId.toString) (LscV2.Ty.wei, $e))
  | `(lsc_stmt| emit $name:ident ( $arg:lsc_expr ) ;) => do
      let arg ← expandLscExpr arg
      `(LscV2.Stmt.emit $(quote name.getId.toString) [(LscV2.Ty.wei, $arg)])
  | `(lsc_stmt| skip;) => `(LscV2.Stmt.skip)

macro_rules
  | `(lsc_stmt| $s1:lsc_stmt $s2:lsc_stmt) => do
      let s1 ← expandLscStmt s1
      let s2 ← expandLscStmt s2
      `(LscV2.Stmt.seq $s1 $s2)
  | `(lsc_stmt| do $s:lsc_stmt) => `(lsc_stmt| $s)

end LscV2.DSL

namespace LscV2

def expandLscStmt := DSL.expandLscStmt

end LscV2
