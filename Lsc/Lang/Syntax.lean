import Lsc.Lang.AST
import Lsc.Lang.TxM
import Lsc.Lang.Derive
import Lean

/-!
# `lscExpr`/`lscStmt`: the full dss2024-style bracket-delimited grammar

Builds out the prototype's `tx <name> { ... }` delimiter (`require`-only) into the full
minimal grammar the migration plan calls for: a fresh `lscExpr` expression category plus
the remaining `lscStmt` statement productions (assignment, `revert`, `emit`, `if`/`else`,
`var`), all elaborated directly into `Lsc.Stmt`/`Lsc.Expr` values, reusing
`Lang/Derive.lean`'s `FieldKind`/`getStructureFieldKinds`/`elabErrorCtorName`/
`getCtorFieldKind` machinery rather than reimplementing any of it.

## `σ.field` resolution: fresh grammar + `FieldKind` introspection (plan's preferred option)

`σ.field` is *not* parsed as its own dedicated production — like `msg.sender`, Lean's lexer
already tokenises a dotted identifier (`σ.field`) as a single compound `Name`
(`.str (.str .anonymous "σ") "field"`, see `TxM.lean`'s docstring on `sigmaFieldName?`,
reused here directly), so a single `ident` production in `lscExpr` covers plain local names,
`σ.field`, and `msg.sender` alike; the elaborator (`elabLscExpr`) dispatches on the parsed
`Name`'s shape. For the `σ.field` case specifically, this file resolves the field's storage
`Ty` by calling `Lsc.Deriving.getStructureFieldKinds` against the contract's *real* storage
`structure` — found via a new `Lsc.Deriving.contractStorageExt` registry (a same-namespace
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

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

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
`Lsc.Deriving.getStructureFieldKinds` directly (no reimplementation). -/
def storageFieldKind (storageName : Name) (field : String) : TermElabM Lsc.Deriving.FieldKind := do
  let kinds ← Lsc.Deriving.getStructureFieldKinds storageName
  match kinds.find? (fun p => p.1.toString == field) with
  | some (_, k) => return k
  | none => throwError "Syntax: unknown storage field `{field}` on `{storageName}`"

/-- Elaborate one `lscExpr` node into a `Lsc.Expr`-valued `Term`, alongside the `FieldKind`
tag it was resolved at (needed by callers, e.g. `require`/`if`'s `Bool`-kind check, `emit`'s
expected-argument-kind check, and `+?`/`-?`'s own dispatch). -/
partial def elabLscExpr (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind)) :
    TSyntax `lscExpr → TermElabM (Term × Lsc.Deriving.FieldKind)
  | `(lscExpr| ($e)) => elabLscExpr storageName locals e
  | `(lscExpr| msg.sender) => do
      return (← `(Lsc.CoreExpr.txField Lsc.TxField.caller), .address)
  | `(lscExpr| true) => do
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.bool (Lsc.Lit.bool true)), .bool)
  | `(lscExpr| false) => do
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.bool (Lsc.Lit.bool false)), .bool)
  | `(lscExpr| ! $e) => do
      let (t, k) ← elabLscExpr storageName locals e
      unless k == .bool do
        throwError "`!` expects a `Bool`-kind `lscExpr`, got a `{repr k}`-kind one"
      return (← `(Lsc.CoreExpr.not $t), .bool)
  | `(lscExpr| $a +? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wei do
        throwError "`+?`'s left-hand side must be `Wei`-kind, got `{repr ak}`"
      match lscExprAsNatLit? b with
      | some n => return (← `(Lsc.Wei.Expr.addCheckedNat $at_ $(quote n)), .wei)
      | none =>
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wei do
            throwError "`+?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
          return (← `(Lsc.Wei.Expr.addChecked $at_ $bt), .wei)
  | `(lscExpr| $a -? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wei do
        throwError "`-?`'s left-hand side must be `Wei`-kind, got `{repr ak}`"
      let bt ← match lscExprAsNatLit? b with
        | some n => `(Lsc.Wei.Expr.lit $(quote n))
        | none => do
            let (bt, bk) ← elabLscExpr storageName locals b
            unless bk == .wei do
              throwError "`-?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
            pure bt
      return (← `(Lsc.Wei.Expr.subChecked $at_ $bt), .wei)
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
      return (← `(@Lsc.CoreExpr.eqAuto $tyConst $at_ $bt), .bool)
  | `(lscExpr| $n:num) => do
      let litTerm ← `(Lsc.Lit.u256 $(quote n.getNat))
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.uint256 $litTerm), .uint256)
  | `(lscExpr| $x:ident) => do
      let name := x.getId
      match Lsc.sigmaFieldName? name with
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
                | .wei => `(Lsc.Wei.Expr.var $nameLit)
                | .bool => `(Lsc.CoreExpr.var Lsc.Ty.bool $nameLit)
                | .address => `(Lsc.CoreExpr.var Lsc.Ty.address $nameLit)
                | .uint256 => `(Lsc.CoreExpr.var Lsc.Ty.uint256 $nameLit)
              return (t, k)
          | none => throwErrorAt x "unbound identifier `{nameStr}` in `lscExpr`"
  | stx => throwErrorAt stx "Syntax.elabLscExpr: unsupported `lscExpr` node"

mutual

/-- Elaborate one `lscStmt` node into a `Lsc.Stmt`-valued `Term`, alongside the possibly-
extended `locals` list (extended only by `var`). -/
partial def elabLscStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind)) :
    TSyntax `lscStmt → TermElabM (Term × List (String × Lsc.Deriving.FieldKind))
  | `(lscStmt| require ( $cond ) else revert $errCtor:ident ( ) ;) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`require`'s condition must be `Bool`-kind, got `{repr k}`"
      let (errName, _) ← Lsc.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← Lsc.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(Lsc.Stmt.require $condTerm $(quote ctorStr)), locals)
  | `(lscStmt| revert $errCtor:ident ( ) ;) => do
      let (errName, _) ← Lsc.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← Lsc.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(Lsc.Stmt.revert $(quote ctorStr)), locals)
  | `(lscStmt| emit $ctor:ident ( ) ;) => do
      let (_, eventName) ← Lsc.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← Lsc.Deriving.getCtorFieldKind ctorName with
      | none => return (← `(Lsc.Stmt.emit $(quote ctorShort) ([] : List Lsc.ExprAny)), locals)
      | some _ => throwErrorAt ctor "`emit {ctorShort}` requires exactly one argument"
  | `(lscStmt| emit $ctor:ident ( $arg ) ;) => do
      let (_, eventName) ← Lsc.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← Lsc.Deriving.getCtorFieldKind ctorName with
      | none => throwErrorAt ctor "`emit {ctorShort}` takes no arguments"
      | some k => do
          let (argTerm, ak) ← elabLscExpr storageName locals arg
          unless ak == k do
            throwErrorAt ctor "`emit {ctorShort}` expects a `{repr k}`-kind argument, got `{repr ak}`"
          let tyConst ← k.tyConst
          return (← `(Lsc.Stmt.emit $(quote ctorShort) [⟨$tyConst, $argTerm⟩]), locals)
  | `(lscStmt| $x:ident = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let (eTerm, ek) ← elabLscExpr storageName locals e
          unless ek == k do
            throwErrorAt x "storage field `{field}` expects a `{repr k}`-kind value, got `{repr ek}`"
          let tyConst ← k.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $eTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| let $x:ident = $e ;) => do
      let (eTerm, k) ← elabLscExpr storageName locals e
      let tyConst ← k.tyConst
      let nameStr := x.getId.toString
      let stmtTerm ← `(Lsc.Stmt.letBind $(quote nameStr) ⟨$tyConst, $eTerm⟩)
      return (stmtTerm, (nameStr, k) :: locals)
  | `(lscStmt| if ( $cond ) { $thn* } else { $els* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      let (elsTerm, _) ← elabStmtList storageName locals els
      return (← `(Lsc.Stmt.ifThenElse $condTerm $thnTerm $elsTerm), locals)
  | `(lscStmt| if ( $cond ) { $thn* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      return (← `(Lsc.Stmt.ifThenElse $condTerm $thnTerm Lsc.Stmt.skip), locals)
  | stx => throwErrorAt stx "Syntax.elabLscStmt: unsupported `lscStmt` node"

/-- Fold a sequence of `lscStmt` nodes into one chained `Lsc.Stmt` term via
`Stmt.seq`/`Stmt.skip`, threading `locals` through so a `var` in an earlier statement is
visible to later ones (mirroring `TxM.run`'s fold, and the prototype's original loop). -/
partial def elabStmtList (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (stmts : Array (TSyntax `lscStmt)) : TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let mut result : Term ← `(Lsc.Stmt.skip)
  let mut locs := locals
  for s in stmts do
    let (t, locs') ← elabLscStmt storageName locs s
    result ← `(Lsc.Stmt.seq $result $t)
    locs := locs'
  return (result, locs)

end

/-- `tx <name> { <lscStmt>* }` — the delimiter/entry point, unchanged in shape from the
prototype (see that file's original docstring for why this command-level shape was chosen).
Unlike the prototype, this no longer elaborates the body immediately: doing so required
`σ.field`'s storage `Ty` (via `Lsc.Deriving.currContractStorageName`) to already be
registered, which forced `derive_contract_dsl` to run before every `tx` and `derive_contract_def`
to run after every `tx`, permanently straddling any single merged macro call. Instead, `tx` just
buffers its raw `lscStmt*` syntax under the current namespace
(`Lsc.Deriving.contractTxSyntaxExt`); `Lsc.Deriving.flushContractTxs` (run by
`derive_contract_def`/`derive_contract`) elaborates and emits the real `def name : Stmt := ...`
declarations later, all at once. -/
elab "tx " name:ident "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  -- `name.raw` (the plain, un-namespaced ident) is kept alongside `fnName` (the fully-qualified
  -- one) so `flushContractTxs` can later declare `def name : Stmt := ...` with the *plain* name
  -- — letting Lean prepend the (then-current) namespace itself, exactly once — while still using
  -- `fnName` for `contractFnsExt` bookkeeping/cross-referencing.
  modifyEnv fun env =>
    Lsc.Deriving.contractTxSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, name.raw, stmts.map (·.raw))])

/-- Elaborate and emit every `tx name { .. }` body buffered so far under the current namespace
(`Lsc.Deriving.contractTxSyntaxExt`) into a real `def name : Lsc.Stmt := ...`, exactly as
`tx` itself used to do inline — see `tx`'s docstring above for why this is now deferred rather
than immediate. Also pushes each name into `Lsc.Deriving.contractFnsExt`, matching `tx`'s old
self-registration, so `derive_contract_def`'s auto-derived `functions` list still works
unchanged. Clears the namespace's buffer once flushed, so re-running (e.g. a stray second
`derive_contract_def` in the same namespace) is a no-op rather than re-emitting duplicate
`def`s. -/
def flushContractTxs : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let pending := (Lsc.Deriving.contractTxSyntaxExt.getState (← getEnv)).find? ns |>.getD []
  for (fnName, nameRaw, stmtsRaw) in pending do
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName [] stmts
      return t
    -- The *plain* (un-namespaced) ident, so Lean prepends the current namespace itself, exactly
    -- once — see `tx`'s docstring above on why the fully-qualified `fnName` isn't used here.
    let nameId : Lean.Ident := ⟨nameRaw⟩
    elabCommand (← `(command| def $nameId : Lsc.Stmt := $bodyTerm))
    modifyEnv fun env =>
      Lsc.Deriving.contractFnsExt.modifyState env fun m =>
        m.insert ns ((m.find? ns |>.getD []) ++ [fnName])
  modifyEnv fun env => Lsc.Deriving.contractTxSyntaxExt.modifyState env (·.insert ns [])

/-- The shared body of `derive_contract_def`/`derive_contract` once their three trailing optional
groups have already been unwrapped to plain `Option Term`s (by each caller — see those
elaborators below) — kept as one ordinary function, rather than re-quoted/spliced `Syntax`,
since `Option Term` splices into a `command|` quotation's optional-group slots without the
anonymous-syntax-category antiquotation issues a raw `TSyntax` re-splice would hit. See
`Lang/Derive.lean`'s docstring (right before this logic's old location, before it moved here to
be able to call `flushContractTxs`, which needs `elabStmtList`) for the full rationale/defaults. -/
def elabContractDefBody (nameStrStx : TSyntax `Lean.Parser.Term.str) (storageId errId eventId : Lean.Ident)
    (explicitFunctions? explicitTopic0? explicitCtor? : Option Term) : CommandElabM Unit := do
  let nameStr : Term := quote (nameStrStx.raw.isStrLit?.getD "")
  let storageName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo storageId
  let errName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo errId
  let eventName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo eventId
  -- `storage : List (Ident × Ty × Option ExprAny)`, derived from `storageId`'s fields.
  let storageFields ← liftTermElabM <| Lsc.Deriving.getStructureFieldKinds storageName
  let storageEntries ← storageFields.mapM fun (fname, k) => liftTermElabM do
    let tyConst ← k.tyConst
    let fnameStr := quote fname.toString
    `(($fnameStr, $tyConst, (none : Option Lsc.ExprAny)))
  let storageTerm ← `([$storageEntries,*])
  -- `errors : List Ident`, derived from `errId`'s constructor names.
  let errIndVal ← liftTermElabM <| getConstInfoInduct errName
  let errCtorStrs := errIndVal.ctors.toArray.map (·.getString!)
  let errCtorLits : Array Term := errCtorStrs.map quote
  let errorsTerm ← `([$errCtorLits,*])
  -- `events : List (Ident × List (Ident × Ty))`, derived from `eventId`'s constructors.
  let eventIndVal ← liftTermElabM <| getConstInfoInduct eventName
  let eventEntries ← eventIndVal.ctors.toArray.mapM fun ctorName => liftTermElabM do
    let cStr := ctorName.getString!
    let cStrLit := quote cStr
    match ← Lsc.Deriving.getCtorFieldNameKind ctorName with
    | none => `(($cStrLit, ([] : List (Lsc.Ident × Lsc.Ty))))
    | some (paramName, k) =>
      let tyConst ← k.tyConst
      let paramStrLit := quote paramName.toString
      `(($cStrLit, [($paramStrLit, $tyConst)]))
  let eventsTerm ← `([$eventEntries,*])
  -- `functions : List (String × Stmt)` — either the explicit override, or every `tx`
  -- self-registered under this namespace so far (`Lsc.Deriving.contractFnsExt`), in
  -- declaration order.
  let functionsTerm ← match explicitFunctions? with
    | some t => pure t
    | none => do
      let ns ← getCurrNamespace
      let fnNames := (Lsc.Deriving.contractFnsExt.getState (← getEnv)).find? ns |>.getD []
      let fnEntries ← fnNames.toArray.mapM fun fnName => liftTermElabM do
        let fnId := mkIdent fnName
        let fnStrLit := quote fnName.componentsRev.head!.toString
        `(($fnStrLit, $fnId))
      `([$fnEntries,*])
  -- `topic0 : Ident → Option Nat` — either the explicit override, or a real Keccak256
  -- computation (`Lsc.computeEventTopic0`) over each event's already-derived ABI
  -- signature, matching `eventEntries` above exactly (replaces hand-written stub tables
  -- like the old non-cryptographic `name.hash.toNat` fallback).
  let topic0Term ← match explicitTopic0? with
    | some t => pure t
    | none => do
      let topic0NameId := mkIdent `name
      let topic0Arms ← eventIndVal.ctors.toArray.mapM fun ctorName => liftTermElabM do
        let cStr := ctorName.getString!
        let cStrLit := quote cStr
        let paramsTerm ← match ← Lsc.Deriving.getCtorFieldNameKind ctorName with
          | none => `(([] : List (Lsc.Ident × Lsc.Ty)))
          | some (paramName, k) =>
            let tyConst ← k.tyConst
            let paramStrLit := quote paramName.toString
            `([($paramStrLit, $tyConst)])
        `(matchAltExpr| | $cStrLit => some (Lsc.computeEventTopic0 $cStrLit $paramsTerm))
      let wc ← `(_)
      let defaultArm ← `(matchAltExpr| | $wc => none)
      let topic0Alts := topic0Arms.push defaultArm
      let topic0Discrs ← liftTermElabM <| #[(topic0NameId : Term)].mapM Lsc.Deriving.mkDiscr
      `(fun ($topic0NameId : Lsc.Ident) => match $[$topic0Discrs],* with $topic0Alts:matchAlt*)
  -- `ctor : Option Stmt` — either the explicit override, or (if `storageId` has an
  -- `owner : Address` field) the standard "set owner to the deployer" constructor, else
  -- `none`. Matches what `Counter`'s hand-written `owner := msg.sender` constructor did.
  let ctorTerm ← match explicitCtor? with
    | some t => pure t
    | none =>
      if storageFields.any fun (fname, k) => fname == `owner && k == Lsc.Deriving.FieldKind.address then
        `(some (Lsc.Stmt.storageSet "owner" ⟨Lsc.Ty.address, Lsc.CoreExpr.txField Lsc.TxField.caller⟩))
      else
        `((none : Option Lsc.Stmt))
  -- Built via `mkIdent` (not written as literal tokens inside the
  -- `command|` quotations below) so the declared names stay plain,
  -- externally-visible identifiers rather than hygienically macro-scoped
  -- ones local to this quotation.
  let contractDefId := mkIdent `contractDef
  let configId := mkIdent `config
  let bytecodeHexId := mkIdent `bytecodeHex
  let deployHexId := mkIdent `deployHex
  let nId := mkIdent `n
  let bodyId := mkIdent `body
  -- `${Name}M`, e.g. `CounterM` for `"Counter"` — the `ContractM` monad abbreviation a contract
  -- author used to have to hand-write themselves right next to this command (argument order
  -- swapped from `storageId errId eventId` to match `ContractM`'s own `S E Err` declaration
  -- order).
  let mId := mkIdent (Name.mkSimple ((nameStrStx.raw.isStrLit?.getD "") ++ "M"))
  Lean.Elab.Command.elabCommand (← `(command|
    abbrev $mId := Lsc.ContractM $storageId $eventId $errId))
  Lean.Elab.Command.elabCommand (← `(command|
    def $contractDefId : Lsc.ContractDef where
      name := $nameStr
      storage := $storageTerm
      errors := $errorsTerm
      events := $eventsTerm
      functions :=
        ($functionsTerm : List (String × Lsc.Stmt)).map fun ($nId, $bodyId) =>
          { name := $nId, kind := Lsc.FunctionKind.external, params := [],
            retTy := Lsc.Ty.unit, body := $bodyId }
      interfaces := []
      constructor := $ctorTerm))
  Lean.Elab.Command.elabCommand (← `(command|
    def $configId : Lsc.Compile.Config := Lsc.Compile.configFromContract $contractDefId $topic0Term))
  Lean.Elab.Command.elabCommand (← `(command|
    def $bytecodeHexId : String :=
      match Lsc.Compile.contractToBytecodeHex $contractDefId $topic0Term with
      | .ok hex => hex
      | .error _ => ""))
  Lean.Elab.Command.elabCommand (← `(command|
    def $deployHexId : String :=
      match Lsc.Compile.deployToBytecodeHex $contractDefId $topic0Term with
      | .ok hex => hex
      | .error _ => ""))

/-- Unwrap the shared `fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")?`
trailing-groups pattern (`derive_contract_def`/`derive_contract` both take it) into plain
`Option Term`s, consumed left-to-right (`functions`, then `topic0`, then `ctor`) — giving zero
groups means "auto-derive everything", giving one means "override just `functions`", etc. -/
def unwrapContractDefTrailingGroups
    (fnsStx topic0Stx ctorStx : Option (TSyntax Name.anonymous)) :
    Option Term × Option Term × Option Term :=
  (fnsStx.map fun s => ⟨s.raw[1]!⟩, topic0Stx.map fun s => ⟨s.raw[1]!⟩, ctorStx.map fun s => ⟨s.raw[1]!⟩)

/-- `derive_contract_def "Name" Storage Err Event (functions)? (topic0)? (ctor)?` — flushes any
buffered `tx` bodies, then re-derives the pieces of `ContractDef` (and the `config`/
`bytecodeHex`/`deployHex` compile outputs) already fully determined by `Storage`/`Err`/`Event`'s
declared fields/constructors — see `elabContractDefBody`/`Lang/Derive.lean`'s docstring for the
full rationale/defaults. -/
elab "derive_contract_def " nameStrStx:str storageId:ident errId:ident eventId:ident
    fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")? : command => do
  flushContractTxs
  let (fns?, topic0?, ctor?) := unwrapContractDefTrailingGroups fnsStx topic0Stx ctorStx
  elabContractDefBody nameStrStx storageId errId eventId fns? topic0? ctor?

/-- `derive_contract "Name" Storage Err Event (functions)? (topic0)? (ctor)?` — the single-call
merge of `derive_contract_dsl Storage Err Event` followed by `derive_contract_def "Name" Storage
Err Event ...`: runs the `derive_contract_dsl` assembly first (so `Lsc.ContractDSL`/
`σ.field`-resolution registries exist), then flushes and derives `ContractDef` exactly as
`derive_contract_def` does. Because `tx { .. }` bodies are now buffered rather than elaborated
immediately (see `tx`'s docstring above), this single call can sit once, *after* every `tx`
block, instead of needing one call before `tx` (for `σ.field`/`revert`/`emit` resolution) and a
separate one after (to collect the buffered bodies). -/
elab "derive_contract " nameStrStx:str storageId:ident errId:ident eventId:ident
    fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")? : command => do
  elabCommand (← `(command| derive_contract_dsl $storageId $errId $eventId))
  flushContractTxs
  let (fns?, topic0?, ctor?) := unwrapContractDefTrailingGroups fnsStx topic0Stx ctorStx
  elabContractDefBody nameStrStx storageId errId eventId fns? topic0? ctor?

end Lsc.Syntax
