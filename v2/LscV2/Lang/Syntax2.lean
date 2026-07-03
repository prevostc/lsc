import LscV2.Lang.AST
import LscV2.Lang.TxM
import LscV2.Lang.Derive
import Lean

/-!
# `lscExpr`/`lscStmt`: the full dss2024-style bracket-delimited grammar

Builds out the prototype's `tx <name> { ... }` delimiter (`require`-only) into the full
minimal grammar the migration plan calls for: a fresh `lscExpr` expression category plus
the remaining `lscStmt` statement productions (assignment, `revert`, `emit`, `if`/`else`,
`var`), all elaborated directly into `LscV2.Stmt`/`LscV2.Expr` values, reusing
`Lang/Derive.lean`'s `FieldKind`/`getStructureFieldKinds`/`elabErrorCtorName`/
`getCtorFieldKind` machinery rather than reimplementing any of it.

## `σ.field` resolution: fresh grammar + `FieldKind` introspection (plan's preferred option)

`σ.field` is *not* parsed as its own dedicated production — like `msg.sender`, Lean's lexer
already tokenises a dotted identifier (`σ.field`) as a single compound `Name`
(`.str (.str .anonymous "σ") "field"`, see `TxM.lean`'s docstring on `sigmaFieldName?`,
reused here directly), so a single `ident` production in `lscExpr` covers plain local names,
`σ.field`, and `msg.sender` alike; the elaborator (`elabLscExpr`) dispatches on the parsed
`Name`'s shape. For the `σ.field` case specifically, this file resolves the field's storage
`Ty` by calling `LscV2.Deriving.getStructureFieldKinds` against the contract's *real* storage
`structure` — found via a new `LscV2.Deriving.contractStorageExt` registry (a same-namespace
`Name → Name` map, `derive_contract_dsl`-populated, analogous to the existing
`contractTypesExt`), **not** by depending on the `deriving ContractStorage`-generated
`$ns.σ.$field` constants. This matches the plan's explicit "avoids depending on the
`deriving ContractStorage`-generated `σ` namespace constants going forward" preference (the
prototype file's alternative, reusing those generated constants via a `term` antiquotation,
was not needed — it was reasonably simple to introspect the structure directly).

## `let x = e;`: implemented, not deferred

Because this elaborator has full `TermElabM` control over the whole `tx { ... }` block (unlike
`TxM.lean`'s `do`-notation macro layer, which only ever sees one `doElem` at a time with no
persistent side channel), it can thread an explicit `locals : List (String × FieldKind)`
association list through statement elaboration by hand — no typeclass dispatch
(`LetBindable`/`SetSigma`) is needed at all, since every `lscExpr`/`lscStmt` node's `FieldKind`
is fully determined by *static* lookups (`locals`, `getStructureFieldKinds`, or the operator's
own fixed contract) rather than by real Lean-level type inference. `let n = σ.number +? 1;`
therefore emits exactly one `Stmt.letBind`, and any later `n` in the same `tx` block resolves
to a `storageGet`-avoiding `Expr.var` reference — the same once-evaluated semantics
`TxM.lean`'s `letWei`/`var` provide, with a plainer, Rust-shaped surface syntax (`let` keyword,
plain `=` rather than `:=` — no collision with the separate `σ.field = e;` assignment
production, since that one has no leading keyword and these remain unambiguous by first token).

## Arithmetic (`+?`/`-?`): direct dispatch on `FieldKind`, no typeclass hack

`TxM.lean`'s `WeiAddChecked`/`LetBindable`/`SetSigma` typeclasses exist purely to let plain
Lean notation (`+?`, `var`, `set`) dispatch on a *value*'s Lean type inside ordinary
`do`-notation, where the elaborator has no other way to know which combinator to call. Here,
every `lscExpr` node's `FieldKind` is already computed by `elabLscExpr` as it recurses, so
`+?`/`-?` simply pattern-match on the already-known left/right `FieldKind`s directly — no
typeclasses needed. `Wei.Expr`'s `addCheckedNat` (bare-`Nat` right-hand side, e.g.
`σ.number +? 1`) is detected syntactically (`lscExprAsNatLit?`, peeking at the raw `lscExpr`
node before elaborating it) so `1` doesn't need to round-trip through a `CoreExpr`/`Wei.Expr`
literal it isn't.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace LscV2.Syntax2

/-! ## Syntax categories -/

/-- Fresh, inert-everywhere-else expression category. Nothing outside an explicit
`tx { ... }` delimiter (via `lscStmt`, below) ever parses into `lscExpr`. -/
declare_syntax_cat lscExpr

/-- Local/bound identifiers, `σ.field` storage reads, and `msg.sender` all lex as a single
(possibly dotted) `ident` token — dispatched by `Name` shape in `elabLscExpr`, not split into
separate grammar productions (see module docstring). -/
syntax:max (name := lscExprIdent) ident : lscExpr

/-- Numeric literal. Defaults to `Ty.uint256`-kind unless consumed directly by `+?`/`-?`'s
bare-`Nat` `Wei.Expr.addCheckedNat`/`.lit` handling (see `lscExprAsNatLit?`). -/
syntax:max (name := lscExprNum) num : lscExpr

/-- Boolean literal. Using plain `"true"`/`"false"` as fresh `syntax` atoms (even via
`declare_syntax_cat`-scoped rules) was verified to break their pre-existing meaning as Lean's
builtin `Bool` literal terms *everywhere else in the file* (e.g. `paused : Bool := false` in a
plain `structure` stops parsing with `unexpected token 'false'; expected term`) — `Lean.Parser
.nonReservedSymbol` is the standard fix for exactly this token-table collision: it registers
`"true"`/`"false"` as *non-reserved* symbols usable as `lscExpr` leading tokens without
shadowing/reserving them for every other parser category, so the builtin `Bool` term notation
keeps working unchanged elsewhere in this same file. -/
syntax:max (name := lscExprTrue) &"true" : lscExpr
syntax:max (name := lscExprFalse) &"false" : lscExpr

syntax:max (name := lscExprMsgSender) "msg.sender" : lscExpr

syntax:max (name := lscExprParen) "(" lscExpr ")" : lscExpr

/-- Boolean negation, binds tighter than `==`/`+?`/`-?`. -/
syntax:75 (name := lscExprNot) "!" lscExpr:75 : lscExpr

/-- Checked addition (`Wei`-kind only), left-associative. -/
syntax:65 (name := lscExprAdd) lscExpr:65 " +? " lscExpr:66 : lscExpr

/-- Checked subtraction (`Wei`-kind only), left-associative. -/
syntax:65 (name := lscExprSub) lscExpr:65 " -? " lscExpr:66 : lscExpr

/-- Equality (any matching non-`Wei` kind). -/
syntax:50 (name := lscExprEq) lscExpr:51 " == " lscExpr:51 : lscExpr

/-- Fresh, inert-everywhere-else statement category (unchanged from the prototype, extended
with the new productions below). -/
declare_syntax_cat lscStmt

/-- `require(cond) else revert ErrCtor();` — `cond` is a real `lscExpr`; `ErrCtor` is resolved
against the contract's real `Err` inductive. Parens around `cond` (Solidity's `require(condition,
"reason")` convention), `else` (Swift's `guard cond else { ... }` precedent), and the
call-style `ErrCtor()` (matching Solidity's actual custom-error `revert Ctor();` syntax,
0.8.4+) — see the migration plan for the full rationale. -/
syntax (name := lscRequire) "require" "(" lscExpr ")" " else " "revert " ident "(" ")" ";" : lscStmt

/-- `revert ErrCtor();` — mirrors `require`'s error-resolution logic; call-style to match
Solidity's custom-error `revert Ctor();` syntax. -/
syntax (name := lscRevert) "revert " ident "(" ")" ";" : lscStmt

/-- `emit Ctor();` — 0-argument event, call-style for consistency with `emit Ctor(arg);`. -/
syntax (name := lscEmit0) "emit " ident "(" ")" ";" : lscStmt

/-- `emit Ctor(arg);` — 1-argument event. -/
syntax (name := lscEmit1) "emit " ident "(" lscExpr ")" ";" : lscStmt

/-- `σ.field = e;` — storage assignment. The left-hand side is a plain `ident` (see the
module docstring on why `σ.field` needs no dedicated production); a non-`σ.field` left-hand
side is a clear elaboration-time error, not a silent misparse. -/
syntax (name := lscAssign) ident " = " lscExpr ";" : lscStmt

/-- `let x = e;` — evaluate-once local binding (see module docstring's "`let x = e;`" section,
same semantics, Rust-shaped spelling: `let` keyword + plain `=`, chosen over `:=` since the
binding reads naturally either way and this isn't competing with `Eq`/`doReassign` the way
`TxM.lean`'s old `do`-notation attempts were). -/
syntax (name := lscLetBind) "let " ident " = " lscExpr ";" : lscStmt

/-- `if (cond) { ... } else { ... }`. -/
syntax (name := lscIfElse) "if" "(" lscExpr ")" "{" lscStmt* "}" "else" "{" lscStmt* "}" : lscStmt

/-- `if (cond) { ... }` — no-`else` form, compiles to `Stmt.ifThenElse cond thn Stmt.skip`. -/
syntax (name := lscIf) "if" "(" lscExpr ")" "{" lscStmt* "}" : lscStmt

/-! ## Elaboration -/

/-- If `stx` is literally a bare numeral (`lscExprNum`), return its value — used by `+?`/`-?`
to detect the bare-`Nat` right-hand side (`Wei.addCheckedNat`) without first elaborating it as
a full `CoreExpr .uint256`. -/
def lscExprAsNatLit? (stx : TSyntax `lscExpr) : Option Nat :=
  match stx with
  | `(lscExpr| $n:num) => some n.getNat
  | _ => none

/-- Look up a storage field's `FieldKind` against the real storage `structure`, reusing
`LscV2.Deriving.getStructureFieldKinds` directly (no reimplementation). -/
def storageFieldKind (storageName : Name) (field : String) : TermElabM LscV2.Deriving.FieldKind := do
  let kinds ← LscV2.Deriving.getStructureFieldKinds storageName
  match kinds.find? (fun p => p.1.toString == field) with
  | some (_, k) => return k
  | none => throwError "Syntax2: unknown storage field `{field}` on `{storageName}`"

/-- Elaborate one `lscExpr` node into a `LscV2.Expr`-valued `Term`, alongside the `FieldKind`
tag it was resolved at (needed by callers, e.g. `require`/`if`'s `Bool`-kind check, `emit`'s
expected-argument-kind check, and `+?`/`-?`'s own dispatch). -/
partial def elabLscExpr (storageName : Name) (locals : List (String × LscV2.Deriving.FieldKind)) :
    TSyntax `lscExpr → TermElabM (Term × LscV2.Deriving.FieldKind)
  | `(lscExpr| ($e)) => elabLscExpr storageName locals e
  | `(lscExpr| msg.sender) => do
      return (← `(LscV2.CoreExpr.txField LscV2.TxField.caller), .address)
  | `(lscExpr| true) => do
      return (← `(LscV2.CoreExpr.lit LscV2.Ty.bool (LscV2.Lit.bool true)), .bool)
  | `(lscExpr| false) => do
      return (← `(LscV2.CoreExpr.lit LscV2.Ty.bool (LscV2.Lit.bool false)), .bool)
  | `(lscExpr| ! $e) => do
      let (t, k) ← elabLscExpr storageName locals e
      unless k == .bool do
        throwError "`!` expects a `Bool`-kind `lscExpr`, got a `{repr k}`-kind one"
      return (← `(LscV2.CoreExpr.not $t), .bool)
  | `(lscExpr| $a +? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wei do
        throwError "`+?`'s left-hand side must be `Wei`-kind, got `{repr ak}`"
      match lscExprAsNatLit? b with
      | some n => return (← `(LscV2.Wei.Expr.addCheckedNat $at_ $(quote n)), .wei)
      | none =>
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wei do
            throwError "`+?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
          return (← `(LscV2.Wei.Expr.addChecked $at_ $bt), .wei)
  | `(lscExpr| $a -? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wei do
        throwError "`-?`'s left-hand side must be `Wei`-kind, got `{repr ak}`"
      let bt ← match lscExprAsNatLit? b with
        | some n => `(LscV2.Wei.Expr.lit $(quote n))
        | none => do
            let (bt, bk) ← elabLscExpr storageName locals b
            unless bk == .wei do
              throwError "`-?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
            pure bt
      return (← `(LscV2.Wei.Expr.subChecked $at_ $bt), .wei)
  | `(lscExpr| $a == $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      let (bt, bk) ← elabLscExpr storageName locals b
      unless ak == bk do
        throwError "`==` between mismatched kinds `{repr ak}` and `{repr bk}`"
      if ak == .wei then
        throwError "`==` is not yet supported on `Wei`-kind expressions"
      -- Explicit `t` (rather than `eqAuto`'s implicit-`t` inference from `a`) avoids the same
      -- defeq-but-not-syntactic-equality trap the hand-written `pause`/`unpause` needed
      -- `@CoreExpr.eqAuto Ty.address ...` to route around (e.g. `msg.sender : CoreExpr
      -- (txFieldTy .caller)` vs `σ.owner : CoreExpr Ty.address`): `ak`'s `tyConst` is always
      -- the concrete `Ty` literal (from `storageFieldKind`/`Lit`/local `FieldKind`s), never an
      -- unreduced type-family application, so pinning `t` to it keeps the result syntactically
      -- `Ty`-headed rather than stuck on whichever operand happened to be elaborated first.
      let tyConst ← ak.tyConst
      return (← `(@LscV2.CoreExpr.eqAuto $tyConst $at_ $bt), .bool)
  | `(lscExpr| $n:num) => do
      let litTerm ← `(LscV2.Lit.u256 $(quote n.getNat))
      return (← `(LscV2.CoreExpr.lit LscV2.Ty.uint256 $litTerm), .uint256)
  | `(lscExpr| $x:ident) => do
      let name := x.getId
      match LscV2.sigmaFieldName? name with
      | some field => do
          let k ← storageFieldKind storageName field
          let t ← k.storageGetStx field
          return (t, k)
      | none =>
          let nameStr := name.toString
          match locals.find? (·.1 == nameStr) with
          | some (_, k) =>
              let nameLit := quote nameStr
              let t ← match k with
                | .wei => `(LscV2.Wei.Expr.var $nameLit)
                | .bool => `(LscV2.CoreExpr.var LscV2.Ty.bool $nameLit)
                | .address => `(LscV2.CoreExpr.var LscV2.Ty.address $nameLit)
                | .uint256 => `(LscV2.CoreExpr.var LscV2.Ty.uint256 $nameLit)
              return (t, k)
          | none => throwErrorAt x "unbound identifier `{nameStr}` in `lscExpr`"
  | stx => throwErrorAt stx "Syntax2.elabLscExpr: unsupported `lscExpr` node"

mutual

/-- Elaborate one `lscStmt` node into a `LscV2.Stmt`-valued `Term`, alongside the possibly-
extended `locals` list (extended only by `var`). -/
partial def elabLscStmt (storageName : Name) (locals : List (String × LscV2.Deriving.FieldKind)) :
    TSyntax `lscStmt → TermElabM (Term × List (String × LscV2.Deriving.FieldKind))
  | `(lscStmt| require ( $cond ) else revert $errCtor:ident ( ) ;) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`require`'s condition must be `Bool`-kind, got `{repr k}`"
      let (errName, _) ← LscV2.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← LscV2.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(LscV2.Stmt.require $condTerm $(quote ctorStr)), locals)
  | `(lscStmt| revert $errCtor:ident ( ) ;) => do
      let (errName, _) ← LscV2.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← LscV2.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(LscV2.Stmt.revert $(quote ctorStr)), locals)
  | `(lscStmt| emit $ctor:ident ( ) ;) => do
      let (_, eventName) ← LscV2.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← LscV2.Deriving.getCtorFieldKind ctorName with
      | none => return (← `(LscV2.Stmt.emit $(quote ctorShort) ([] : List LscV2.ExprAny)), locals)
      | some _ => throwErrorAt ctor "`emit {ctorShort}` requires exactly one argument"
  | `(lscStmt| emit $ctor:ident ( $arg ) ;) => do
      let (_, eventName) ← LscV2.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← LscV2.Deriving.getCtorFieldKind ctorName with
      | none => throwErrorAt ctor "`emit {ctorShort}` takes no arguments"
      | some k => do
          let (argTerm, ak) ← elabLscExpr storageName locals arg
          unless ak == k do
            throwErrorAt ctor "`emit {ctorShort}` expects a `{repr k}`-kind argument, got `{repr ak}`"
          let tyConst ← k.tyConst
          return (← `(LscV2.Stmt.emit $(quote ctorShort) [⟨$tyConst, $argTerm⟩]), locals)
  | `(lscStmt| $x:ident = $e ;) => do
      match LscV2.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let (eTerm, ek) ← elabLscExpr storageName locals e
          unless ek == k do
            throwErrorAt x "storage field `{field}` expects a `{repr k}`-kind value, got `{repr ek}`"
          let tyConst ← k.tyConst
          return (← `(LscV2.Stmt.storageSet $(quote field) ⟨$tyConst, $eTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| let $x:ident = $e ;) => do
      let (eTerm, k) ← elabLscExpr storageName locals e
      let tyConst ← k.tyConst
      let nameStr := x.getId.toString
      let stmtTerm ← `(LscV2.Stmt.letBind $(quote nameStr) ⟨$tyConst, $eTerm⟩)
      return (stmtTerm, (nameStr, k) :: locals)
  | `(lscStmt| if ( $cond ) { $thn* } else { $els* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      let (elsTerm, _) ← elabStmtList storageName locals els
      return (← `(LscV2.Stmt.ifThenElse $condTerm $thnTerm $elsTerm), locals)
  | `(lscStmt| if ( $cond ) { $thn* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      return (← `(LscV2.Stmt.ifThenElse $condTerm $thnTerm LscV2.Stmt.skip), locals)
  | stx => throwErrorAt stx "Syntax2.elabLscStmt: unsupported `lscStmt` node"

/-- Fold a sequence of `lscStmt` nodes into one chained `LscV2.Stmt` term via
`Stmt.seq`/`Stmt.skip`, threading `locals` through so a `var` in an earlier statement is
visible to later ones (mirroring `TxM.run`'s fold, and the prototype's original loop). -/
partial def elabStmtList (storageName : Name) (locals : List (String × LscV2.Deriving.FieldKind))
    (stmts : Array (TSyntax `lscStmt)) : TermElabM (Term × List (String × LscV2.Deriving.FieldKind)) := do
  let mut result : Term ← `(LscV2.Stmt.skip)
  let mut locs := locals
  for s in stmts do
    let (t, locs') ← elabLscStmt storageName locs s
    result ← `(LscV2.Stmt.seq $result $t)
    locs := locs'
  return (result, locs)

end

/-- `tx <name> { <lscStmt>* }` — the delimiter/entry point, unchanged in shape from the
prototype (see that file's original docstring for why this command-level shape was chosen),
now resolving `σ.field`'s storage `Ty` via `LscV2.Deriving.currContractStorageName` +
`getStructureFieldKinds` before elaborating any statements. -/
elab "tx " name:ident "{" stmts:lscStmt* "}" : command => do
  let bodyTerm ← liftTermElabM do
    let storageName ← LscV2.Deriving.currContractStorageName
    let (t, _) ← elabStmtList storageName [] stmts
    return t
  elabCommand (← `(command| def $name : LscV2.Stmt := $bodyTerm))

end LscV2.Syntax2
