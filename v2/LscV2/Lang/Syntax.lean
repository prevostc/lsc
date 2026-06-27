import LscV2.Lang.AST
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

syntax num : lsc_expr
syntax (name := lsc_var) ident : lsc_expr
syntax (name := lsc_true) "true" : lsc_expr
syntax (name := lsc_false) "false" : lsc_expr
syntax "msg.sender" : lsc_expr
syntax "(" lsc_expr ")" : lsc_expr
syntax:45 lsc_expr:45 "==" lsc_expr:46 : lsc_expr
syntax:40 "!" lsc_expr : lsc_expr

syntax lsc_stmt lsc_stmt : lsc_stmt
syntax "let" ident "←" lsc_store_ref "+?" num ";" : lsc_stmt
syntax lsc_store_ref ":=" lsc_expr ";" : lsc_stmt
syntax "require" "(" lsc_expr ")" "else" "revert" ident ";" : lsc_stmt
syntax "emit" ident "(" lsc_expr,* ")" ";" : lsc_stmt
syntax "revert" ident ";" : lsc_stmt
syntax "do" lsc_stmt : lsc_stmt
syntax "skip" ";" : lsc_stmt

syntax ident ":" lsc_ty (":=" lsc_expr)? : lsc_field_decl
syntax "|" ident : lsc_error_decl
syntax "|" ident "(" ident ":" lsc_ty ")" : lsc_event_decl
syntax "|" ident : lsc_event_decl
syntax "def" ident ":" "Tx" ":=" "do" lsc_stmt : lsc_func_decl

syntax "storage" ":" lsc_field_decl*
     "errors" ":" lsc_error_decl*
     "events" ":" lsc_event_decl*
     lsc_func_decl* : lsc_contract_body

syntax "contract" ident "where" lsc_contract_body : command

inductive FieldKind
  | wei
  | bool
  | address
  | uint256

abbrev FieldMap := Array (String × FieldKind)

def fieldKindToTy (k : FieldKind) : MacroM (TSyntax `term) :=
  match k with
  | .wei => `(LscV2.Ty.wei)
  | .bool => `(LscV2.Ty.bool)
  | .address => `(LscV2.Ty.address)
  | .uint256 => `(LscV2.Ty.uint256)

def lscTyToFieldKind (stx : TSyntax `lsc_ty) : MacroM FieldKind :=
  match stx with
  | `(lsc_ty| UInt256) => pure .uint256
  | `(lsc_ty| Bool) => pure .bool
  | `(lsc_ty| Address) => pure .address
  | `(lsc_ty| Wei) => pure .wei
  | _ => Macro.throwError s!"unsupported storage type {stx}"

def lscTyToTyTerm (stx : TSyntax `lsc_ty) : MacroM (TSyntax `term) := do
  fieldKindToTy (← lscTyToFieldKind stx)

def lookupFieldKind (fields : FieldMap) (name : String) : MacroM FieldKind := do
  for (n, k) in fields do
    if n == name then return k
  Macro.throwError s!"unknown storage field {name}"

partial def expandLscExprWith (fields : FieldMap) (stx : TSyntax `lsc_expr) : MacroM (TSyntax `term) := do
  match ← expandMacro? stx.raw with
  | some expanded =>
    if expanded == stx.raw then expandLscExprWith fields stx
    else expandLscExprWith fields ⟨expanded⟩
  | none =>
    match stx with
    | `(lsc_expr| $n:num) => `(LscV2.Wei.Expr.lit $(quote n.getNat))
    | `(lsc_expr| lsc_true) => `(LscV2.CoreExpr.lit LscV2.Ty.bool (LscV2.Lit.bool Bool.true))
    | `(lsc_expr| lsc_false) => `(LscV2.CoreExpr.lit LscV2.Ty.bool (LscV2.Lit.bool Bool.false))
    | `(lsc_expr| msg.sender) => `(LscV2.CoreExpr.txField LscV2.TxField.caller)
    | `(lsc_expr| $. $f:ident) => do
        let fname := f.getId.toString
        let kind ← lookupFieldKind fields fname
        match kind with
        | .wei => `(LscV2.Wei.Expr.storageGet $(quote fname))
        | k =>
          let tyStx ← fieldKindToTy k
          `( @LscV2.CoreExpr.storageGet $tyStx $(quote fname) )
    | `(lsc_expr| $i:ident) =>
        `(LscV2.Wei.Expr.var $(quote i.getId.toString))
    | `(lsc_expr| ($e:lsc_expr)) => expandLscExprWith fields e
    | `(lsc_expr| $a:lsc_expr == $b:lsc_expr) => do
        let a ← expandLscExprWith fields a
        let b ← expandLscExprWith fields b
        `(@LscV2.CoreExpr.eq LscV2.Ty.address $a $b)
    | `(lsc_expr| ! $e:lsc_expr) => do
        let e ← expandLscExprWith fields e
        `(LscV2.CoreExpr.not $e)
    | _ => Macro.throwError s!"unsupported expression {stx}"

partial def expandLscStmtWith (fields : FieldMap) (stx : TSyntax `lsc_stmt) : MacroM (TSyntax `term) := do
  match ← expandMacro? stx.raw with
  | some expanded =>
    if expanded == stx.raw then expandLscStmtWith fields stx
    else expandLscStmtWith fields ⟨expanded⟩
  | none =>
    match stx with
    | `(lsc_stmt| let $i:ident ← $. $f:ident +? $d:num;) =>
        `(LscV2.Stmt.letBind $(quote i.getId.toString)
          (Sigma.mk LscV2.Ty.wei (LscV2.Wei.addCheckedNatStorage $(quote f.getId.toString) $(quote d.getNat))))
    | `(lsc_stmt| $. $f:ident := $e:lsc_expr;) => do
        let e ← expandLscExprWith fields e
        let fname := f.getId.toString
        let kind ← lookupFieldKind fields fname
        let tyStx ← fieldKindToTy kind
        `(LscV2.Stmt.storageSet $(quote fname) (Sigma.mk $tyStx $e))
    | `(lsc_stmt| require ($e:lsc_expr) else revert $err:ident;) => do
        let e ← expandLscExprWith fields e
        `(LscV2.Stmt.require $e $(quote err.getId.toString))
    | `(lsc_stmt| emit $name:ident ( $args:lsc_expr,* ) ;) => do
        let elems := args.getElems
        if elems.isEmpty then
          `(LscV2.Stmt.emit $(quote name.getId.toString) [])
        else
          let expanded ← elems.mapM (expandLscExprWith fields)
          `(LscV2.Stmt.emit $(quote name.getId.toString) [$[(Sigma.mk LscV2.Ty.wei $expanded)],*])
    | `(lsc_stmt| revert $err:ident;) =>
        `(LscV2.Stmt.revert $(quote err.getId.toString))
    | `(lsc_stmt| skip;) => `(LscV2.Stmt.skip)
    | `(lsc_stmt| $s1:lsc_stmt $s2:lsc_stmt) => do
        let s1 ← expandLscStmtWith fields s1
        let s2 ← expandLscStmtWith fields s2
        `(LscV2.Stmt.seq $s1 $s2)
    | `(lsc_stmt| do $s:lsc_stmt) => expandLscStmtWith fields s
    | _ => Macro.throwError s!"unsupported statement {stx}"

end LscV2.DSL

namespace LscV2

def expandLscStmtWith := DSL.expandLscStmtWith

end LscV2
