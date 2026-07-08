import Lsc.Lang.AST
import Lsc.Lang.TxM
import Lsc.Lang.Derive
import Lean

/-!
# `lscExpr`/`lscStmt`: the `tx { ... }` grammar

The contract-author surface: a fresh `lscExpr` expression category plus `lscStmt` statement
productions (assignment, `require`/`revert`, `emit`, `if`/`else`, `let`), elaborated directly
into `Lsc.Stmt`/`Lsc.Expr` values. Reuses `Lang/Derive.lean`'s `FieldKind`/
`getStructureFieldKinds`/`elabErrorCtorName`/`getCtorFieldKind` machinery rather than
reimplementing it. See `docs/decisions/0001-txm-superseded-by-syntax.md` for why this grammar
exists instead of extending `TxM.lean`'s `do`-notation surface.

A few mechanisms worth knowing when reading this file:

- **`σ.field`** is not its own grammar production: Lean's lexer already tokenises the dotted
  identifier as one compound `Name`, so a single `ident` production in `lscExpr` covers plain
  local names, `σ.field`, and `msg.sender` alike; `elabLscExpr` dispatches on the parsed
  `Name`'s shape and resolves `σ.field`'s storage `Ty` via `Lsc.Deriving.getStructureFieldKinds`
  against the contract's real storage `structure`.
- **`let x = e;`** is implemented directly (not deferred behind a typeclass): the elaborator
  threads an explicit `locals : List (String × FieldKind)` association list through statement
  elaboration by hand, so every node's `FieldKind` is a static lookup. `let n = σ.number +? 1;`
  emits one `Stmt.letBind`; later references to `n` resolve to an `Expr.var`, not a re-evaluated
  `storageGet` — same once-evaluated semantics as `TxM.lean`'s `letWei`/`var`, without needing
  its typeclass dispatch.
- **`+?`/`-?`** pattern-match directly on the already-known left/right `FieldKind`s (no
  typeclass needed, unlike `TxM.lean`'s `WeiAddChecked`). A bare-`Nat` right-hand side (e.g.
  `σ.number +? 1`) is detected syntactically (`lscExprAsNatLit?`) before elaboration.
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

/-- `σ.field[key]` — read one entry of an address-keyed `Lsc.Wad.WadMap` storage field (e.g.
`σ.balances[to]`), where `key` is `msg.sender` or a bare local identifier (a `tx` parameter or
`let`-bound `Address` value) — see `Lsc.Wad.MapKey`'s docstring for why only these two forms are
supported. `σ.field` itself lexes as one dotted `ident` token (see this file's module
docstring), so this production is `ident "[" (ident | "msg.sender") "]"`. -/
syntax:max (name := lscExprMapGet) ident "[" lscExpr "]" : lscExpr

syntax:max (name := lscExprParen) "(" lscExpr ")" : lscExpr

/-- Boolean negation, binds tighter than `==`/`+?`/`-?`. -/
syntax:75 (name := lscExprNot) "!" lscExpr:75 : lscExpr

/-- Checked addition (`Wei`-kind or `Wad`-kind only), left-associative. -/
syntax:65 (name := lscExprAdd) lscExpr:65 " +? " lscExpr:66 : lscExpr

/-- Checked subtraction (`Wei`-kind or `Wad`-kind only), left-associative. -/
syntax:65 (name := lscExprSub) lscExpr:65 " -? " lscExpr:66 : lscExpr

/-- Checked, half-up-rounding `Wad` multiplication (`Wad.mulHalfUpChecked`), left-associative.
Surface syntax per `docs/reference/AMM.md`. -/
syntax:65 (name := lscExprMul) lscExpr:65 " ⸢*⸣? " lscExpr:66 : lscExpr

/-- Checked, round-down `Wad` division (`Wad.divDownChecked`), left-associative. Surface syntax
per `docs/reference/AMM.md`. -/
syntax:65 (name := lscExprDiv) lscExpr:65 " ⌊/⌋? " lscExpr:66 : lscExpr

/-- Equality (any matching non-`Wei`/`Wad` kind). -/
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

/-- `σ.field[key] = e;` — write one entry of an address-keyed `Lsc.Wad.WadMap` storage field
(e.g. `σ.balances[to] = newBalance;`) — see `lscExprMapGet`'s docstring for `key`'s two
supported forms. -/
syntax (name := lscMapAssign) ident "[" lscExpr "]" " = " lscExpr ";" : lscStmt

/-- `σ.field[key] +=? e;` — checked-add-and-write sugar for
`σ.field[key] = σ.field[key] +? e;` (e.g. `σ.balances[recipient] +=? amount;`, `docs/reference/
TOKEN.md`). Only ever `Wad`-kind, since a mapping field's value kind is always `Wad`
(`lscExprMapGet`'s docstring). -/
syntax (name := lscMapAssignAdd) ident "[" lscExpr "]" " +=? " lscExpr ";" : lscStmt

/-- `σ.field[key] -=? e;` — checked-sub-and-write sugar for
`σ.field[key] = σ.field[key] -? e;`, the subtraction counterpart of `lscMapAssignAdd`. -/
syntax (name := lscMapAssignSub) ident "[" lscExpr "]" " -=? " lscExpr ";" : lscStmt

/-- `σ.field +=? e;` — checked-add-and-write sugar for `σ.field = σ.field +? e;`, for a plain
(non-mapping) `Wei`- or `Wad`-kind storage field (e.g. `σ.totalSupply +=? amount;`). -/
syntax (name := lscAssignAdd) ident " +=? " lscExpr ";" : lscStmt

/-- `σ.field -=? e;` — checked-sub-and-write sugar for `σ.field = σ.field -? e;`, the
subtraction counterpart of `lscAssignAdd`. -/
syntax (name := lscAssignSub) ident " -=? " lscExpr ";" : lscStmt

/-- `let x = e;` — evaluate-once local binding (see module docstring's "`let x = e;`" section,
same semantics, Rust-shaped spelling: `let` keyword + plain `=`, chosen over `:=` since the
binding reads naturally either way and this isn't competing with `Eq`/`doReassign` the way
`TxM.lean`'s old `do`-notation attempts were). -/
syntax (name := lscLetBind) "let " ident " = " lscExpr ";" : lscStmt

/-- `if (cond) { ... } else { ... }`. -/
syntax (name := lscIfElse) "if" "(" lscExpr ")" "{" lscStmt* "}" "else" "{" lscStmt* "}" : lscStmt

/-- `if (cond) { ... }` — no-`else` form, compiles to `Stmt.ifThenElse cond thn Stmt.skip`. -/
syntax (name := lscIf) "if" "(" lscExpr ")" "{" lscStmt* "}" : lscStmt

/-- `return e;` — only ever valid inside a `view` function body (see `Lsc.Stmt.ret`'s docstring
in `Lang/AST.lean`); elaborating one inside an ordinary `tx` body is not itself a parse error
(`lscStmt` is one shared grammar), but `Checks.checkViewPurity`/`checkViewReturns` are only ever
run against `.view`-kind `FunctionDef`s, so a stray `return` inside a `tx` would silently compile
to a `Stmt.ret` node that `Stmt.eval`'s public entry point (`Eval.lean`) simply discards the
returned value of — harmless, but not a construct `tx` authors have any reason to reach for.
The `view` elaborator below is the only place that ever emits this node from surface syntax. -/
syntax (name := lscReturn) "return " lscExpr ";" : lscStmt

/-- `exec Target.fn(arg1, arg2);` / `read Target.fn(arg1, arg2);` — black-box cross-contract
invocations into a specific, statically-named other contract. `exec` is state-mutating; `read`
discards the callee's resulting state/log changes. See `Lsc.ContractM.PairM.exec`/`PairM.read`
(`Core/ContractM.lean`) for the semantics and `docs/decisions/0003-exec-read-black-box.md` for
why they're black box; `examples/escrow/src/Escrow.lean` has a real usage.

`Target.fn` is a single dotted identifier naming the callee's tx-derived function directly (e.g.
`Token.transfer`). Arguments must be plain identifiers — real Lean values (`tx` params or
in-scope contract-local `def`s), not arbitrary `lscExpr` sub-expressions like `amount +? 1` —
since the callee expects real Lean values, not this contract's own AST.

**Whole-`tx`-body monad switch:** a `tx` whose body contains one of these nodes at top level has
its *entire* body elaborated as a `PairM S T E Err Unit` term instead of the usual `Lsc.Stmt`
value (see `elabExecOrReadTerm`/`elabStmtListPairM`/`flushContractTxs` below); ordinary
statements around it are individually lifted into `PairM` via `PairM.liftCaller`.
`@nonreentrant` is required immediately by `tx`'s own elaborator, since a cross-contract `tx` is
never added to `ContractDef.functions` (`Lsc.Deriving.contractCrossCallExt`) and so couldn't be
caught by a later, `ContractDef`-walking check. -/
syntax (name := lscExec) "exec " ident " ( " ident,* " ) " ";" : lscStmt

/-- See `lscExec`'s docstring — the read-only counterpart. -/
syntax (name := lscRead) "read " ident " ( " ident,* " ) " ";" : lscStmt

/-! ## `tx` parameters -/

/-- One `tx` parameter declaration: `name : ty`, e.g. `amount : Wad`. `ty` is parsed as a
plain `ident` (not a dedicated keyword-token grammar) purely to avoid reserving `UInt256`/
`Bool`/`Address`/`Wei`/`Wad` as global tokens (see `elabLscTyIdent` below, which resolves the
five supported spellings by string match, the same style `emit $ctor:ident`/`revert
$errCtor:ident` already use for resolving *their* idents against real declarations). Declared
as its own `lscTxParam` syntax category so a comma-separated `lscTxParam,*` list can be wrapped
in a single, optional pair of parens on `tx`'s own `elab` declaration below — giving
`tx foo { .. }` (no parens) and `tx foo(a : ty1, b : ty2) { .. }` (one paren group, comma-
separated) the same shape/ergonomics as Solidity's (and most other languages') parameter
lists. -/
declare_syntax_cat lscTxParam
syntax (name := lscTxParamDecl) ident " : " ident : lscTxParam

/-- Resolve a `tx` parameter's `ty` identifier to a `FieldKind`, by string match against the
five supported spellings — the same five `Lsc.Deriving.FieldKind` already supports for storage
fields/`let`-locals, so a `tx` parameter is usable inside the body exactly like a `let`-bound
local (see this file's module docstring's "`let x = e;`" section: a parameter and a `let`-local
are structurally the same kind of thing, just supplied by the caller instead of computed by an
expression). Spelled capitalized (`UInt256`/`Bool`/`Address`/`Wei`/`Wad`) to match the real Lean
type names these already have everywhere else (storage fields, event payloads, `leanTypeStx`),
rather than a separate lowercase-only convention just for `tx` parameters. -/
def elabLscTyIdent (ty : Lean.Ident) : TermElabM Lsc.Deriving.FieldKind :=
  match ty.getId.toString with
  | "UInt256" => return .uint256
  | "Bool" => return .bool
  | "Address" => return .address
  | "Wei" => return .wei
  | "Wad" => return .wad
  | _ => do
    -- Not one of the five fixed keywords — try resolving `ty` as a named `Wad`(`= Fixed 18`)-
    -- shaped alias (e.g. `Token.Amount`, declared as `abbrev Token.Amount := Lsc.Wad` right next
    -- to a token's own storage) via the same alias resolution `Lsc.Deriving.fieldKindOfExprM`
    -- already uses for storage struct fields — so a `tx` parameter (e.g. `Escrow.release`'s
    -- `amount`) can name the specific token it moves, instead of the generic `Wad`. Only ever
    -- accepts a `Fixed 18` alias, never another `d` (`fieldKindOfExprM`/`fieldKindOfExpr`'s own
    -- docstrings explain why: this DSL's `.wad`-kind pipeline hardcodes the 18-decimals `WAD`
    -- scale, so accepting e.g. `Fixed 6` here would silently mis-scale `⸢*⸣?`/`⌊/⌋?` instead of
    -- rejecting it) — a genuinely non-18-decimals token must be authored as a hand-written
    -- `ContractM` contract (bypassing this grammar entirely), same as `Escrow.release` already
    -- does for its cross-contract `exec` call. -/
    let e ← Lean.Elab.Term.elabType ty
    match ← Lsc.Deriving.fieldKindOfExprM e with
    | some .wad => return .wad
    | _ => throwErrorAt ty "unsupported `tx` parameter type `{ty.getId}` \
        — expected one of `UInt256`/`Bool`/`Address`/`Wei`/`Wad`, or an alias resolving to \
        `Wad`/`Fixed 18` exactly (e.g. `Token.Amount`)"

/-- Elaborate one `(name : ty)` parameter group into `(paramNameString, FieldKind)`. -/
def elabTxParam : TSyntax `lscTxParam → TermElabM (String × Lsc.Deriving.FieldKind)
  | `(lscTxParam| $x:ident : $ty:ident) => do
      let k ← elabLscTyIdent ty
      return (x.getId.toString, k)
  | stx => throwErrorAt stx "Syntax.elabTxParam: unsupported `lscTxParam` node"

/-- The companion half of `elabTxParam`: pulls out the parameter's *un-resolved* `(name, ty)`
syntax pair verbatim (no `FieldKind` resolution at all) — used only by a cross-contract `tx`'s
`flushContractTxs` branch (`Lsc.Deriving.contractTxParamTyExt`, below) so it can rebuild the real
callable `def`'s parameter binder with the author's *exact* declared type (e.g. `Token.Amount`),
not `FieldKind.leanTypeStx`'s generic `Lsc.Wad` — see `Fixed`'s docstring
(`Lsc/Lib/Wad/Syntax.lean`) for why that distinction is exactly what makes mixing up two
different tokens' amounts a compile error at an `exec`/`read` call site. -/
def txParamNameAndTyIdent : TSyntax `lscTxParam → Option (String × Lean.Ident)
  | `(lscTxParam| $x:ident : $ty:ident) => some (x.getId.toString, ty)
  | _ => none

/-- Stash `fnName`'s parameters' declared types, resolved to their fully-qualified `Name`s, into
`Lsc.Deriving.contractParamTyExt` — shared by `tx`'s and `view`'s elaborators (both use the same
`lscTxParam` parameter grammar), see that extension's docstring for who consults this, why a
fully-qualified `Name` (rather than the raw `ty` syntax as written) is stored, and why. -/
def stashParamTys (fnName : Name) (paramsStx : Array (TSyntax `lscTxParam)) : CommandElabM Unit := do
  let paramTys ← liftTermElabM <|
    (paramsStx.toList.filterMap txParamNameAndTyIdent).mapM fun (n, ty) => do
      let e ← Lean.Elab.Term.elabType ty
      let some tyName := e.constName?
        | throwErrorAt ty "Syntax.stashParamTys: expected `{ty}` to resolve to a named type"
      return (n, tyName)
  modifyEnv fun env =>
    Lsc.Deriving.contractParamTyExt.modifyState env fun m => m.insert fnName paramTys

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

/-- Elaborate a `σ.field[key]`/`σ.field[key] = e;` node's `key` sub-`lscExpr` into a
`Lsc.Wad.MapKey`-valued `Term` — only `msg.sender` or a bare local identifier are supported
(see `lscExprMapGet`'s docstring). -/
def elabMapKey (key : TSyntax `lscExpr) : TermElabM Term :=
  match key with
  | `(lscExpr| msg.sender) => `(Lsc.Wad.MapKey.caller)
  | `(lscExpr| $x:ident) =>
    match Lsc.sigmaFieldName? x.getId with
    | some _ => throwErrorAt x "a mapping key cannot itself be a `σ.field` read"
    | none => `(Lsc.Wad.MapKey.var $(quote x.getId.toString))
  | stx => throwErrorAt stx "unsupported mapping key `{stx}` — expected `msg.sender` or a \
bare local identifier"

mutual

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
      elabCheckedAddWith storageName locals at_ ak b
  | `(lscExpr| $a -? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      elabCheckedSubWith storageName locals at_ ak b
  | `(lscExpr| $a ⸢*⸣? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wad do
        throwError "`⸢*⸣?`'s left-hand side must be `Wad`-kind, got `{repr ak}`"
      let (bt, bk) ← elabLscExpr storageName locals b
      unless bk == .wad do
        throwError "`⸢*⸣?`'s right-hand side must be `Wad`-kind, got `{repr bk}`"
      return (← `(Lsc.Wad.Expr.mulHalfUpChecked $at_ $bt), .wad)
  | `(lscExpr| $a ⌊/⌋? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wad do
        throwError "`⌊/⌋?`'s left-hand side must be `Wad`-kind, got `{repr ak}`"
      let (bt, bk) ← elabLscExpr storageName locals b
      unless bk == .wad do
        throwError "`⌊/⌋?`'s right-hand side must be `Wad`-kind, got `{repr bk}`"
      return (← `(Lsc.Wad.Expr.divDownChecked $at_ $bt), .wad)
  | `(lscExpr| $a == $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      let (bt, bk) ← elabLscExpr storageName locals b
      unless ak == bk do
        throwError "`==` between mismatched kinds `{repr ak}` and `{repr bk}`"
      if ak == .wei || ak == .wad then
        throwError "`==` is not yet supported on `{repr ak}`-kind expressions"
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
  | `(lscExpr| $x:ident [ $key ]) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless k == .wadMap do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          return (← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm), .wad)
      | none => throwErrorAt x "expected `σ.field[key]`, got `{x.getId}[..]`"
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
                | .wad => `(Lsc.Wad.Expr.var $nameLit)
                | .bool => `(Lsc.CoreExpr.var Lsc.Ty.bool $nameLit)
                | .address => `(Lsc.CoreExpr.var Lsc.Ty.address $nameLit)
                | .uint256 => `(Lsc.CoreExpr.var Lsc.Ty.uint256 $nameLit)
                | .wadMap => throwErrorAt x "`{nameStr}` is a mapping field, not a local value"
              return (t, k)
          | none => throwErrorAt x "unbound identifier `{nameStr}` in `lscExpr`"
  | stx => throwErrorAt stx "Syntax.elabLscExpr: unsupported `lscExpr` node"

/-- Checked addition, given the already-elaborated left-hand side (`at_`/`ak`) — shared by
`+?`'s own `lscExpr` production and the `+=?` compound-assignment statement sugar
(`lscMapAssignAdd`/`lscAssignAdd`), which both need to build "current value +? rhs" without
re-parsing a synthetic `lscExpr` node. -/
partial def elabCheckedAddWith (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (at_ : Term) (ak : Lsc.Deriving.FieldKind) (b : TSyntax `lscExpr) :
    TermElabM (Term × Lsc.Deriving.FieldKind) := do
  match ak with
  | .wei =>
    match lscExprAsNatLit? b with
    | some n => return (← `(Lsc.Wei.Expr.addCheckedNat $at_ $(quote n)), .wei)
    | none =>
        let (bt, bk) ← elabLscExpr storageName locals b
        unless bk == .wei do
          throwError "`+?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
        return (← `(Lsc.Wei.Expr.addChecked $at_ $bt), .wei)
  | .wad =>
    match lscExprAsNatLit? b with
    | some n => return (← `(Lsc.Wad.Expr.addCheckedNat $at_ $(quote n)), .wad)
    | none =>
        let (bt, bk) ← elabLscExpr storageName locals b
        unless bk == .wad do
          throwError "`+?`'s right-hand side must be `Wad`-kind or a numeral, got `{repr bk}`"
        return (← `(Lsc.Wad.Expr.addChecked $at_ $bt), .wad)
  | _ => throwError "`+?`'s left-hand side must be `Wei`- or `Wad`-kind, got `{repr ak}`"

/-- Checked subtraction — the `-?`/`-=?` counterpart of `elabCheckedAddWith`. -/
partial def elabCheckedSubWith (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (at_ : Term) (ak : Lsc.Deriving.FieldKind) (b : TSyntax `lscExpr) :
    TermElabM (Term × Lsc.Deriving.FieldKind) := do
  match ak with
  | .wei =>
    let bt ← match lscExprAsNatLit? b with
      | some n => `(Lsc.Wei.Expr.lit $(quote n))
      | none => do
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wei do
            throwError "`-?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
          pure bt
    return (← `(Lsc.Wei.Expr.subChecked $at_ $bt), .wei)
  | .wad =>
    let bt ← match lscExprAsNatLit? b with
      | some n => `(Lsc.Wad.Expr.lit $(quote n))
      | none => do
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wad do
            throwError "`-?`'s right-hand side must be `Wad`-kind or a numeral, got `{repr bk}`"
          pure bt
    return (← `(Lsc.Wad.Expr.subChecked $at_ $bt), .wad)
  | _ => throwError "`-?`'s left-hand side must be `Wei`- or `Wad`-kind, got `{repr ak}`"

end

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
  | `(lscStmt| $x:ident [ $key ] = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless k == .wadMap do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let (eTerm, ek) ← elabLscExpr storageName locals e
          unless ek == .wad do
            throwErrorAt x "mapping field `{field}` expects a `Wad`-kind value, got `{repr ek}`"
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $eTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key ] +=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless k == .wadMap do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let curTerm ← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm)
          let (sumTerm, _) ← elabCheckedAddWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $sumTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] +=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key ] -=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless k == .wadMap do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let curTerm ← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm)
          let (diffTerm, _) ← elabCheckedSubWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $diffTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] -=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident +=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let curTerm ← k.storageGetStx field
          let (sumTerm, sk) ← elabCheckedAddWith storageName locals curTerm k e
          let tyConst ← sk.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $sumTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field +=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident -=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let curTerm ← k.storageGetStx field
          let (diffTerm, sk) ← elabCheckedSubWith storageName locals curTerm k e
          let tyConst ← sk.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $diffTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field -=? e;` on the left-hand side, got `{x.getId}`"
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
  | `(lscStmt| return $e ;) => do
      let (eTerm, k) ← elabLscExpr storageName locals e
      let tyConst ← k.tyConst
      return (← `(Lsc.Stmt.ret ⟨$tyConst, $eTerm⟩), locals)
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

/-! ## Real cross-contract calls (`exec`/`read`): detection + `PairM` codegen -/

/-- Whether `s` is (syntactically) one `exec Target.fn(..);` or `read Target.fn(..);` node —
see `lscExec`'s docstring above. -/
def isExecOrReadStmt (s : TSyntax `lscStmt) : Bool :=
  match s with
  | `(lscStmt| exec $_:ident ( $_,* ) ;) => true
  | `(lscStmt| read $_:ident ( $_,* ) ;) => true
  | _ => false

/-- Whether any *top-level* statement in `stmts` is an `exec`/`read` node — the pre-elaboration
scan `tx`'s own elaborator uses to decide, before elaborating anything at all, whether this
`tx`'s whole body must target `Lsc.ContractM.PairM` rather than plain `Lsc.Stmt` (see `lscExec`'s
docstring's "Whole-`tx`-body monad switch" section).

**Scope note:** deliberately *not* recursive into `if`'s nested `lscStmt*` bodies — a real
cross-contract call is only supported as a direct top-level statement of the `tx` body it
appears in (exactly the shape `Escrow.release` needs), not nested inside conditionals. A future
extension could recurse the same way `Checks.visitStmt` does once `Stmt` itself can represent
(or a moral-equivalent representation of) a cross-contract call node — see this feature's
docstring/report for the concrete follow-up this leaves. -/
def stmtsUseExecOrRead (stmts : Array (TSyntax `lscStmt)) : Bool :=
  stmts.any isExecOrReadStmt

/-- Resolve the real callee `Ident` an `exec`/`read` call to `fn` should actually apply its
arguments to: `fn`'s own `.Typed` companion (`flushContractTxs`'s parameterized non-cross-call
branch, above) if one was generated, else `fn` itself unchanged (e.g. a zero-arg `tx`, or a
hand-written `ContractM` function this DSL never saw). When `.Typed` exists, its signature
already carries every parameter's *exact* author-declared type (e.g. `Token.Amount`, not the
generic `Wad` `fn` itself is stuck with) — so simply applying arguments to it and letting Lean's
ordinary application elaboration/unification do the rest is what turns "passed the wrong token's
amount" into a ordinary compile error, with no manual per-argument type bookkeeping needed at this
call site at all. -/
def resolveExecReadCallee (fn : Lean.Ident) : TermElabM Lean.Ident := do
  -- `fn`'s own literal syntax (e.g. `Token.transfer`, as the author wrote it) may not already be
  -- fully-qualified — resolve it to the real, absolute constant name first (exactly what plain
  -- application elaboration of `$fn` would do anyway), so the sibling `..Typed` name below is
  -- built from the *actual* declaration's full name, not whatever prefix happened to be visible
  -- at this particular call site's own namespace/`open` scope.
  let fnName ← Lean.resolveGlobalConstNoOverload fn
  -- Sibling-flat naming (`Token.transferTyped`), matching `flushContractTxs`'s own
  -- `nameImpl`/`nameTyped` convention (`Name.mkSimple (.. ++ "Typed")`) — not a dotted
  -- `Token.transfer.Typed`, which would need a different declaration shape entirely.
  let typedName := fnName.getPrefix ++ Name.mkSimple (fnName.componentsRev.head!.toString ++ "Typed")
  if (← getEnv).find? typedName |>.isSome then
    return mkIdent typedName
  else
    return fn

/-- Elaborate one `exec Target.fn(arg1, ..);` or `read Target.fn(arg1, ..);` node directly into
a `Lsc.ContractM.PairM S T E Err Unit`-valued `Term` (never a `Lsc.Stmt` — there is no `Stmt`
constructor for this, see `lscExec`'s docstring). `arg1`, ... are spliced as bare identifier
*terms* (real Lean values — `tx` parameters, typically), directly into the callee application
`$fn $args*` (bridged first via `bridgeCalleeArgs`, above); `T`/`ET`/`ErrT` are left to Lean's
ordinary unification (against `$fn`'s `Coe Stmt (ContractM T ET ErrT Unit)`-mediated result type,
`Lang/TxM.lean`) rather than being named anywhere in this function. Both `exec`/`read` are black
box — no `toErr`/`toEvent` conversion functions are needed at all (see `lscExec`'s docstring). -/
def elabExecOrReadTerm : TSyntax `lscStmt → TermElabM Term
  | `(lscStmt| exec $fn:ident ( $args,* ) ;) => do
      -- `$fn` (e.g. `Token.transfer`) returns a bare `Lsc.Stmt`, which only coerces to the
      -- right `ContractM T ET ErrT A` (`Lang/TxM.lean`'s `Coe Stmt (ContractM S E Err Unit)`
      -- instance) once `T`/`ET`/`ErrT` are already resolved — plain application leaves them as
      -- unresolved metavariables (nothing here pins them), so this pins `T` explicitly via an
      -- ascription to `$targetNs.${targetNs}M`, the `derive_contract`-generated `ContractM`-
      -- abbrev naming convention (`Lang/Syntax.lean`'s `elabContractDefBody`'s `mId`) every
      -- `derive_contract "Name" ...`-declared contract already follows.
      let targetNs := fn.getId.getPrefix
      if targetNs == Name.anonymous then
        throwErrorAt fn "`exec` expects a dotted `Target.fn` name (e.g. `Token.transfer`), \
got `{fn.getId}`"
      let monadName := targetNs ++ Name.mkSimple (targetNs.componentsRev.head!.toString ++ "M")
      let monadId := mkIdent monadName
      let callee ← resolveExecReadCallee fn
      `(Lsc.ContractM.PairM.exec (($callee $args*) : $monadId Unit))
  | `(lscStmt| read $fn:ident ( $args,* ) ;) => do
      let targetNs := fn.getId.getPrefix
      if targetNs == Name.anonymous then
        throwErrorAt fn "`read` expects a dotted `Target.fn` name (e.g. `Token.balanceOf`), \
got `{fn.getId}`"
      let monadName := targetNs ++ Name.mkSimple (targetNs.componentsRev.head!.toString ++ "M")
      let monadId := mkIdent monadName
      let callee ← resolveExecReadCallee fn
      `(Lsc.ContractM.PairM.read (($callee $args*) : $monadId Unit))
  | stx => throwErrorAt stx "Syntax.elabExecOrReadTerm: unsupported `lscStmt` node"

/-- Fold a list of already-elaborated `PairM`-valued segment `Term`s into one right-associated
`>>=` chain (`s1 >>= fun _ => s2 >>= fun _ => ... >>= fun _ => sN`) — the `PairM` analogue of
`elabStmtList`'s `Stmt.seq` fold, needed here since `PairM` has no first-order `Stmt`-like AST
node to fold into; ordinary `Monad.bind` is the only "sequencing" `PairM` has. -/
def composeSegments : List Term → TermElabM Term
  | [] => `(pure ())
  | [s] => pure s
  | s :: rest => do
      let restTerm ← composeSegments rest
      `($s >>= fun _ => $restTerm)

/-- Wrap an ordinary (non-`exec`/`read`) `Lsc.Stmt` segment's `Term` with one
`Stmt.letBind param ⟨ty, <embedded literal>⟩` per `tx` parameter, mirroring
`flushContractTxs`'s existing parameter-embedding wrapping for the plain zero-cross-call
`Stmt`-only case exactly (see `Lsc.Deriving.FieldKind.embedLitStx`'s docstring) — needed because
each segment is `Lsc.Stmt.eval`'d independently (starting from a fresh `LocalEnv.empty`, see
`elabStmtListPairM` below), so a segment after the cross-contract call still needs its own
binding for a `tx` parameter used again there (e.g. `amount` in both the `exec`/`read` call
itself *and* a later `σ.field +? amount`). -/
def wrapSegmentParams (params : List (String × Lsc.Deriving.FieldKind)) (stmtTerm : Term) :
    TermElabM Term :=
  params.foldrM (init := stmtTerm) fun (pname, k) acc => do
    let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
    let tyConst ← k.tyConst
    let litStx ← k.embedLitStx pid
    `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)

/-- Elaborate a run of consecutive ordinary (non-`exec`/`read`) `lscStmt`s into one `PairM`
segment `Term`: builds the plain `Lsc.Stmt` via the existing `elabStmtList` (unchanged, reused
as-is), wraps it with `wrapSegmentParams`, then lifts the whole thing into `PairM` via
`PairM.liftCaller ∘ Stmt.eval` (`Lsc.ContractM.PairM.liftCaller`, `Core/ContractM.lean`) — the
"ordinary statements just get individually lifted" half of the whole-body monad switch (see
`lscExec`'s docstring). -/
def elabOrdinarySegment (storageName : Name) (locals params : List (String × Lsc.Deriving.FieldKind))
    (buf : Array (TSyntax `lscStmt)) : TermElabM Term := do
  let (stmtTerm, _) ← elabStmtList storageName locals buf
  let wrapped ← wrapSegmentParams params stmtTerm
  -- `(S := ..)` pins the caller's storage type explicitly — without it, `ContractDSL`
  -- instance search for `Stmt.eval` gets stuck on an unresolved metavariable, since this
  -- segment is elaborated bottom-up (no top-down expected type comes from the surrounding
  -- `>>=` chain `composeSegments` builds, see that function's docstring).
  let storageId := mkIdent storageName
  `(Lsc.ContractM.PairM.liftCaller (S := $storageId) (Lsc.Stmt.eval $wrapped))

/-- Elaborate a full cross-contract-call `tx` body (one containing one or more top-level
`exec`/`read` nodes, per `stmtsUseExecOrRead`) into a single `PairM`-valued `Term`: splits
`stmts` at each `exec`/`read` node into alternating ordinary/cross-call segments (in order),
elaborates each (`elabOrdinarySegment`/`elabExecOrReadTerm`), then chains them all together
with `composeSegments`. -/
def elabStmtListPairM (storageName : Name) (locals params : List (String × Lsc.Deriving.FieldKind))
    (stmts : Array (TSyntax `lscStmt)) : TermElabM Term := do
  let mut segments : Array Term := #[]
  let mut buf : Array (TSyntax `lscStmt) := #[]
  for s in stmts do
    if isExecOrReadStmt s then
      if buf.size > 0 then
        segments := segments.push (← elabOrdinarySegment storageName locals params buf)
        buf := #[]
      segments := segments.push (← elabExecOrReadTerm s)
    else
      buf := buf.push s
  if buf.size > 0 then
    segments := segments.push (← elabOrdinarySegment storageName locals params buf)
  composeSegments segments.toList

/-- `tx <name> { <lscStmt>* }` — the delimiter/entry point. Buffers its raw `lscStmt*` syntax
under the current namespace (`Lsc.Deriving.contractTxSyntaxExt`) rather than elaborating
immediately; `Lsc.Deriving.flushContractTxs` (run by `derive_contract_def`/`derive_contract`)
elaborates and emits the real `def name : Stmt := ...` declarations later, all at once — see
`docs/decisions/0007-tx-body-elaboration-deferred.md` for why.

`@nonreentrant` — decorates the immediately-following `tx`, marking it as expected to perform a
real cross-contract call (`exec`/`read`). This `elab` itself requires the decorator on (and only
on) any `tx` whose body actually contains a top-level `exec`/`read` node (see below); a `tx`
with neither at all compiles the same whether or not it is decorated (the decorator is a
requirement, not a universal precondition). Modeled as a plain optional leading atom on `tx`'s
own `elab` (rather than Lean's general `declModifiers`/`@[attr]` machinery, which targets
`structure`/`def`/... declarations `tx` isn't one of) — the same "optional trailing/leading
Syntax group" technique `derive_contract_def`'s `(functions)?`/`(topic0)?`/`(ctor)?` groups
already use just below. -/
elab nrStx:("@nonreentrant")? "tx " name:ident params:(optional("(" lscTxParam,* ")")) "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let isNonReentrant := nrStx.isSome
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  -- `name.raw` (the plain, un-namespaced ident) is kept alongside `fnName` (the fully-qualified
  -- one) so `flushContractTxs` can later declare `def name : Stmt := ...` with the *plain* name
  -- — letting Lean prepend the (then-current) namespace itself, exactly once — while still using
  -- `fnName` for `contractFnsExt` bookkeeping/cross-referencing.
  modifyEnv fun env =>
    Lsc.Deriving.contractTxSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, name.raw, paramsResolved, stmts.map (·.raw))])
  -- Also stash each parameter's *un-resolved* `(name, ty)` syntax verbatim, keyed by this `tx`'s
  -- own fully-qualified `fnName` (`Lsc.Deriving.contractParamTyExt`'s docstring) — consulted both
  -- by `flushContractTxs`'s cross-contract-call branch (for *this* `tx`'s own signature) and, from
  -- a different contract's module entirely, by `elabExecOrReadTerm` (to bridge an `exec`/`read`
  -- call's arguments against *this* `tx`'s real declared parameter types).
  stashParamTys fnName paramsStx
  if isNonReentrant then
    modifyEnv fun env => Lsc.Deriving.contractNonReentrantExt.modifyState env (·.insert fnName true)
  -- Real cross-contract call detection (`exec`/`read`, see that syntax's docstring's
  -- "Whole-`tx`-body monad switch" section): a cross-contract `tx` is never added to
  -- `ContractDef.functions` at all (see `Lsc.Deriving.contractCrossCallExt`'s docstring), so it
  -- could never be reached by a deferred, `ContractDef`-walking check — `@nonreentrant` is
  -- instead required immediately, right here, before this `tx`'s body is even buffered.
  if stmtsUseExecOrRead stmts then
    unless isNonReentrant do
      throwErrorAt name "`{name.getId}` uses `exec`/`read`, but is not marked \
`@nonreentrant` — add `@nonreentrant` immediately before `tx {name.getId}(...)` \
(i.e. `@nonreentrant tx {name.getId}(...) \{ ... }`)"
    modifyEnv fun env => Lsc.Deriving.contractCrossCallExt.modifyState env (·.insert fnName true)

/-- `view name(params) : RetTy { <lscStmt>* }` — a read-only, value-returning function
declaration (the DSL counterpart of a hand-written hand-written `def balanceOf (..) : ContractM
... Wad := fun s => ...`, see `examples/escrow/src/Token.lean`'s pre-`view` `balanceOf`). Every
control-flow path through the body must end in a `return e;` of the declared `RetTy`
(`Checks.checkViewReturns`, enforced once the full `ContractDef` exists — at buffering time here
we only resolve `RetTy` itself, exactly like a `tx` parameter's `ty`). The body must also never
mutate storage or emit an event (`Checks.checkViewPurity`) — a `view` is meant to be a pure,
`STATICCALL`-style read (`Core/ContractM.lean`'s `PairM.read`).

Like `tx`, buffers its raw `lscStmt*` syntax under the current namespace
(`Lsc.Deriving.contractViewSyntaxExt`) rather than elaborating immediately, for the same reason
(`σ.field`'s storage `Ty` isn't registered yet) — `flushContractViews` (run by
`derive_contract_def`/`derive_contract`, alongside `flushContractTxs`) elaborates and emits the
real `def`s later.

**Why the generated return type stays generic `Val Ty.wad` (no per-token tag), unlike a
cross-contract `tx`'s parameter (see `flushContractTxs`'s cross-call branch):** `Val`/`Ty`
(`Lsc/Lang/AST.lean`, `Lsc/Core/ContractM.lean`) are the DSL's single, global, tag-erased sum
types — `Ty.wad` has no slot for `Fixed`'s `tag` parameter at all, so there is no Lean type to
attach the author's declared `RetTy` (e.g. `Token.Amount`) to at this boundary; retagging the
`Wad` payload *inside* a `Val.wad` before returning it would change nothing about the function's
visible return type, which stays `Val Ty.wad` either way. This is consistent with today's actual
attack surface: a `read`'s result is always discarded (`composeSegments`'s `>>= fun _ => ..`,
`isExecOrReadStmt`'s docstring) — there is no `let x = read Target.fn(..);` syntax yet to capture
it into a tagged local at all. `Fixed.retag` (`Lsc/Lib/Wad/Syntax.lean`) exists precisely for the
day that changes: once a `view`'s result can be captured by name with its own declared `RetTy`,
the capture site (not this generated `def`'s signature) is where `Fixed.retag` should be applied,
exactly the same way a cross-contract `tx` parameter's exact declared type is threaded through
today. -/
elab "view " name:ident params:(optional("(" lscTxParam,* ")")) " : " retTy:ident
    "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  let retKind ← liftTermElabM <| elabLscTyIdent retTy
  stashParamTys fnName paramsStx
  modifyEnv fun env =>
    Lsc.Deriving.contractViewSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++
        [(fnName, name.raw, paramsResolved, retKind, stmts.map (·.raw))])

/-- `view name(params) : RetTy => e;` — expression-shorthand form of `view`, for the common
single-expression case (e.g. `view balanceOf(who : Address) : Wad => σ.balances[who];`).
Desugars to the block form's `return e;`, then buffers exactly the same way. -/
elab "view " name:ident params:(optional("(" lscTxParam,* ")")) " : " retTy:ident
    " => " e:lscExpr ";" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  let retKind ← liftTermElabM <| elabLscTyIdent retTy
  let retStmt ← `(lscStmt| return $e ;)
  stashParamTys fnName paramsStx
  modifyEnv fun env =>
    Lsc.Deriving.contractViewSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++
        [(fnName, name.raw, paramsResolved, retKind, #[retStmt.raw])])

/-- Elaborate and emit every `view name(..) : Ty { .. }`/`view name(..) : Ty => e;` body buffered
so far under the current namespace (`Lsc.Deriving.contractViewSyntaxExt`) into real `def`s,
mirroring `flushContractTxs` — see that function's docstring for the general shape. Two `def`s
are always emitted per `view` (unlike `flushContractTxs`'s zero-arg optimization): a hidden
`name.Impl : Lsc.Stmt` holding the raw, `Expr.var`-parameterized body (the one
`elabContractDefBody` embeds into `FunctionDef.body` for the bytecode/Yul pipeline, via
`Lsc.Deriving.contractViewFnsExt`), and the real, callable `name : .. → ContractM S E Err (Val
retKind) := ..` built with `Stmt.evalView`, which literal-embeds each parameter into a fresh
`Stmt.letBind` (exactly like `flushContractTxs`'s parameterized case) before calling
`Stmt.evalView` on the result. -/
def flushContractViews : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let pending := (Lsc.Deriving.contractViewSyntaxExt.getState (← getEnv)).find? ns |>.getD []
  for (fnName, nameRaw, params, retKind, stmtsRaw) in pending do
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    let nameId : Lean.Ident := ⟨nameRaw⟩
    let implId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName params stmts
      return t
    elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
    let retTypeTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (errName, eventName) ← Lsc.Deriving.currContractTypes
      let storageId := mkIdent storageName
      let errId := mkIdent errName
      let eventId := mkIdent eventName
      let retTyConst ← retKind.tyConst
      `(Lsc.ContractM $storageId $eventId $errId (Lsc.Val $retTyConst))
    if params.isEmpty then
      let bodyTerm2 ← liftTermElabM do
        let retTyConst ← retKind.tyConst
        `(Lsc.Stmt.evalView $retTyConst $implId)
      elabCommand (← `(command| def $nameId : $retTypeTerm := $bodyTerm2))
    else
      let sigTerm ← liftTermElabM do
        let paramTys ← params.mapM (·.2.leanTypeStx)
        paramTys.foldrM (init := retTypeTerm) fun ty acc => `($ty → $acc)
      let fullBody ← liftTermElabM do
        let wrappedBody ← params.foldrM (init := (← `($implId))) fun (pname, k) acc => do
          let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
          let tyConst ← k.tyConst
          let litStx ← k.embedLitStx pid
          `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)
        let retTyConst ← retKind.tyConst
        let evalTerm ← `(Lsc.Stmt.evalView $retTyConst $wrappedBody)
        params.foldrM (init := evalTerm) fun (pname, _) acc => do
          let pid := mkIdent (Name.mkSimple pname)
          `(fun $pid:ident => $acc)
      elabCommand (← `(command| def $nameId : $sigTerm := $fullBody))
    let implFnName := ns ++ Name.mkSimple (nameRaw.getId.toString ++ "Impl")
    modifyEnv fun env =>
      Lsc.Deriving.contractViewFnsExt.modifyState env fun m =>
        m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, implFnName, params, retKind)])
  modifyEnv fun env => Lsc.Deriving.contractViewSyntaxExt.modifyState env (·.insert ns [])

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
  let crossCallState := Lsc.Deriving.contractCrossCallExt.getState (← getEnv)
  let paramTyState := Lsc.Deriving.contractParamTyExt.getState (← getEnv)
  for (fnName, nameRaw, params, stmtsRaw) in pending do
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    -- The *plain* (un-namespaced) ident, so Lean prepends the current namespace itself, exactly
    -- once — see `tx`'s docstring above on why the fully-qualified `fnName` isn't used here.
    let nameId : Lean.Ident := ⟨nameRaw⟩
    if (crossCallState.find? fnName).getD false then
      -- Real cross-contract call (`exec`/`read`, see that syntax's docstring): the WHOLE body
      -- elaborates directly to a `Lsc.ContractM.PairM S T E Err Unit`-valued `Term`, never a
      -- `Lsc.Stmt` — so this emits a real, callable, ordinary Lean `def` (exactly like the
      -- hand-written `Escrow.release` this feature replaces), deliberately NOT registered in
      -- `Lsc.Deriving.contractFnsExt`/`ContractDef.functions` (see
      -- `Lsc.Deriving.contractCrossCallExt`'s docstring for why) — so it is also, correctly,
      -- never reached by `Checks.lean`'s `ContractDef`-walking passes or the bytecode/Yul
      -- pipeline (`Compile/Lower.lean` simply never sees it at all, rather than needing to
      -- reject it — see that file's module docstring for the precise, documented boundary).
      let bodyTerm ← liftTermElabM do
        let storageName ← Lsc.Deriving.currContractStorageName
        let (errName, eventName) ← Lsc.Deriving.currContractTypes
        let raw ← elabStmtListPairM storageName params params stmts
        -- Pin `S`/`E`/`Err` explicitly to this contract's own storage/event/error types: a body
        -- consisting of *only* a top-level `exec`/`read` (no surrounding ordinary segment, unlike
        -- `Escrow.release`'s `σ.released +? amount` bracketing) never otherwise gets its caller-
        -- side `PairM S T E Err A` pinned (`elabOrdinarySegment`'s own `(S := ..)` annotation is
        -- the only place that normally happens), leaving typeclass resolution for `[ContractErrors
        -- Err]` stuck on a bare metavariable.
        let storageId := mkIdent storageName
        let errId := mkIdent errName
        let eventId := mkIdent eventName
        `(($raw : Lsc.ContractM.PairM $storageId _ $eventId $errId _))
      -- Look up this `tx`'s author-declared parameter types verbatim
      -- (`Lsc.Deriving.contractTxParamTyExt`) — a cross-contract `tx`'s real callable `def`
      -- parameter binder uses the *exact* declared type (e.g. `Token.Amount`), not
      -- `FieldKind.leanTypeStx`'s generic `Lsc.Wad`, so that two different tokens' amounts
      -- (even same-decimals ones) are genuinely different Lean types at the one place — an
      -- `exec`/`read` call site — where mixing them up would otherwise be possible (see
      -- `Lsc.Wad.Fixed`'s docstring, `Lsc/Lib/Wad/Syntax.lean`).
      let origParamTys : List (String × Name) := paramTyState.find? fnName |>.getD []
      let wrappedBody ← liftTermElabM do
        params.foldrM (init := bodyTerm) fun (pname, k) acc => do
          let pid := mkIdent (Name.mkSimple pname)
          let tyStx : Term ← match origParamTys.find? (·.1 == pname) with
            | some (_, tyName) => pure ⟨mkIdent tyName⟩
            | none => k.leanTypeStx
          `(fun ($pid : $tyStx) => $acc)
      elabCommand (← `(command| def $nameId := $wrappedBody))
      continue
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName params stmts
      return t
    -- `stmtDefFnName` is the fully-qualified name of whichever `def` actually holds the
    -- parameter-free `Stmt` value (`fn.body`'s ABI/bytecode-facing shape — see
    -- `Lsc.Deriving.contractFnsExt`'s docstring): for the zero-arg (unchanged) case that's just
    -- `nameId` itself; for the parameterized case it's a separate, hidden `nameId.Impl` def
    -- holding the raw (still-`Expr.var`-parameterized) body, with `nameId` itself instead
    -- becoming the real *callable* `def nameId (p1 : ty1) ... : Stmt := ...` — see this
    -- function's module-level design note in `Lsc.Deriving.contractFnsExt`.
    let stmtDefFnName ← if params.isEmpty then
        elabCommand (← `(command| def $nameId : Lsc.Stmt := $bodyTerm))
        pure fnName
      else do
        let implId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
        elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
        let sigTerm ← liftTermElabM do
          let paramTys ← params.mapM (·.2.leanTypeStx)
          paramTys.foldrM (init := (← `(Lsc.Stmt))) fun ty acc => `($ty → $acc)
        let lamBody ← liftTermElabM do
          params.foldrM (init := (← `($implId))) fun (pname, k) acc => do
            let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
            let tyConst ← k.tyConst
            let litStx ← k.embedLitStx pid
            `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)
        -- Fold `fun p1 => fun p2 => ... => lamBody` from the *last* parameter inward, rather
        -- than a single `fun p1 p2 ... => lamBody` splice, to avoid needing a
        -- `TSyntaxArray \`Lean.Parser.Term.funBinder` (plain `Ident`s aren't directly
        -- splice-compatible with that category).
        let wrappedBody ← liftTermElabM do
          params.foldrM (init := lamBody) fun (pname, _) acc => do
            let pid := mkIdent (Name.mkSimple pname)
            `(fun $pid:ident => $acc)
        elabCommand (← `(command| def $nameId : $sigTerm := $wrappedBody))
        -- Also emit a `.Typed` companion preserving each parameter's exact author-declared type
        -- (e.g. `Token.Amount`, not this def's own generic `Wad`) — this is what a *different*
        -- module's `exec`/`read` call site (`elabExecOrReadTerm`) actually calls, when present,
        -- so that mixing up two different tokens' amounts across a cross-contract call is a
        -- compile error even though `nameId` itself must stay generic (see `Lsc.Wad.Fixed`'s
        -- docstring for why `nameId` can't just be tagged directly: same-contract internal/test
        -- code, e.g. `TokenTheorem.lean`, calls it directly with plain untagged `Wad` literals).
        -- A companion `def` (rather than reusing `Lsc.Deriving.contractParamTyExt` directly from
        -- `elabExecOrReadTerm`) is what makes this work *across* module/import boundaries at
        -- all — that plain in-memory `EnvExtension` doesn't survive a `.olean` round-trip, but an
        -- ordinary declaration like this one naturally does.
        unless params.isEmpty do
          let origParamTys : List (String × Name) := paramTyState.find? fnName |>.getD []
          let typedId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Typed"))
          let typedSigTerm ← liftTermElabM do
            let paramTys ← params.mapM fun (pname, k) =>
              match origParamTys.find? (·.1 == pname) with
              | some (_, tyName) => pure (⟨mkIdent tyName⟩ : Term)
              | none => k.leanTypeStx
            paramTys.foldrM (init := (← `(Lsc.Stmt))) fun ty acc => `($ty → $acc)
          let typedBody ← liftTermElabM do
            let argTerms ← params.mapM fun (pname, k) => do
              let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
              if k == .wad then `(Lsc.Wad.Fixed.retag $pid) else pure pid
            argTerms.foldlM (init := (← `($nameId))) fun acc a => `($acc $a)
          let typedWrapped ← liftTermElabM do
            params.foldrM (init := typedBody) fun (pname, _) acc => do
              let pid := mkIdent (Name.mkSimple pname)
              `(fun $pid:ident => $acc)
          elabCommand (← `(command| def $typedId : $typedSigTerm := $typedWrapped))
        pure (ns ++ Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
    modifyEnv fun env =>
      Lsc.Deriving.contractFnsExt.modifyState env fun m =>
        m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, stmtDefFnName, params)])
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
  -- `wadMap` fields have no `Ty` at all (storage-only, see `FieldKind.wadMap`'s docstring) —
  -- `ContractDef.storage` has no representation for a mapping field, so they're excluded here,
  -- same as `mkGetFieldCmd`/`mkSigmaFieldCmds` (`Lang/Derive.lean`) already exclude them.
  let scalarStorageFields := storageFields.filter (·.2 != Lsc.Deriving.FieldKind.wadMap)
  let storageEntries ← scalarStorageFields.mapM fun (fname, k) => liftTermElabM do
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
  -- `paramsForFn : String → List (Lsc.Ident × Lsc.Ty)` — a per-function-name lookup for
  -- `FunctionDef.params`, built from the same `tx (p : ty, ...)` declarations
  -- `Lsc.Deriving.contractFnsExt` records. Only meaningful (non-`[]`-defaulting) when
  -- `functions` itself is auto-derived: an explicit `functions` override has no matching
  -- per-name param info available here, so every function it lists gets `params := []` (an
  -- existing, documented limitation of overriding `functions` explicitly, not a regression —
  -- an override can always be written with a real ABI signature by hand if needed).
  let ns ← getCurrNamespace
  let fnEntries2 := (Lsc.Deriving.contractFnsExt.getState (← getEnv)).find? ns |>.getD []
  let paramsForFnTerm ← liftTermElabM do
    let nId := mkIdent `n
    let paramsArms ← fnEntries2.toArray.mapM fun (fnName, _stmtDefName, params) => do
      let fnStrLit := quote fnName.componentsRev.head!.toString
      let paramEntries ← params.toArray.mapM fun (pname, k) => do
        let tyConst ← k.tyConst
        `(($(quote pname), $tyConst))
      let paramsListTerm ← `([$paramEntries,*])
      `(matchAltExpr| | $fnStrLit => $paramsListTerm)
    let wc ← `(_)
    let defaultArm ← `(matchAltExpr| | $wc => ([] : List (Lsc.Ident × Lsc.Ty)))
    let alts := paramsArms.push defaultArm
    let discrs ← #[(nId : Term)].mapM Lsc.Deriving.mkDiscr
    `(fun ($nId : String) => match $[$discrs],* with $alts:matchAlt*)
  -- `nonReentrantForFnTerm : String → Bool` — mirrors `paramsForFnTerm` immediately above, but
  -- looks up each function's `@nonreentrant` decoration (`Lsc.Deriving.contractNonReentrantExt`,
  -- populated by `tx`'s own elaborator) by its fully-qualified `fnName` instead.
  let nonReentrantExtState := Lsc.Deriving.contractNonReentrantExt.getState (← getEnv)
  let nonReentrantForFnTerm ← liftTermElabM do
    let nId2 := mkIdent `n
    let nrArms ← fnEntries2.toArray.filterMapM fun (fnName, _stmtDefName, _params) => do
      if (nonReentrantExtState.find? fnName).getD false then
        let fnStrLit := quote fnName.componentsRev.head!.toString
        some <$> `(matchAltExpr| | $fnStrLit => true)
      else
        pure none
    let wc ← `(_)
    let defaultArm ← `(matchAltExpr| | $wc => false)
    let alts := nrArms.push defaultArm
    let discrs ← #[(nId2 : Term)].mapM Lsc.Deriving.mkDiscr
    `(fun ($nId2 : String) => match $[$discrs],* with $alts:matchAlt*)
  let functionsTerm ← match explicitFunctions? with
    | some t => pure t
    | none => do
      let fnEntries ← fnEntries2.toArray.mapM fun (fnName, stmtDefName, _params) => liftTermElabM do
        let fnId := mkIdent stmtDefName
        let fnStrLit := quote fnName.componentsRev.head!.toString
        `(($fnStrLit, $fnId))
      `([$fnEntries,*])
  -- `view` functions (`Lsc.Deriving.contractViewFnsExt`) are never part of the plain
  -- `String × Stmt` shape above (they carry their own `retTy`/`kind` directly, unlike a `tx`,
  -- which is always `.external`/`Ty.unit`) — built as a separate `List Lsc.FunctionDef` term and
  -- `++`-ed onto `functions` below, regardless of whether `functions` itself was overridden.
  let viewEntries := (Lsc.Deriving.contractViewFnsExt.getState (← getEnv)).find? ns |>.getD []
  let viewFnDefs ← viewEntries.toArray.mapM fun (fnName, implName, params, retKind) => liftTermElabM do
    let implId := mkIdent implName
    let fnStrLit := quote fnName.componentsRev.head!.toString
    let paramEntries ← params.toArray.mapM fun (pname, k) => do
      let tyConst ← k.tyConst
      `(($(quote pname), $tyConst))
    let paramsListTerm ← `([$paramEntries,*])
    let retTyConst ← retKind.tyConst
    `(Lsc.FunctionDef.mk $fnStrLit Lsc.FunctionKind.view $paramsListTerm $retTyConst $implId false)
  let viewFunctionsTerm ← `([$viewFnDefs,*])
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
        (($functionsTerm : List (String × Lsc.Stmt)).map fun ($nId, $bodyId) =>
          { name := $nId, kind := Lsc.FunctionKind.external, params := $paramsForFnTerm $nId,
            retTy := Lsc.Ty.unit, body := $bodyId, nonReentrant := $nonReentrantForFnTerm $nId })
        ++ $viewFunctionsTerm
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

/-- Shared body of `derive_contract`: DSL assembly, flush buffered `tx`/`view` bodies, then
emit `ContractDef` + compile outputs. -/
def elabDeriveContract (nameStrStx : TSyntax `Lean.Parser.Term.str)
    (storageId errId eventId : Lean.Ident)
    (fnsStx topic0Stx ctorStx : Option (TSyntax Name.anonymous)) : CommandElabM Unit := do
  Lsc.Deriving.elabDeriveContractDsl storageId errId eventId
  flushContractTxs
  flushContractViews
  let (fns?, topic0?, ctor?) := unwrapContractDefTrailingGroups fnsStx topic0Stx ctorStx
  elabContractDefBody nameStrStx storageId errId eventId fns? topic0? ctor?

/-- `derive_contract "Name" Storage Err Event (functions)? (topic0)? (ctor)?` — the single
author-facing closing command for a contract module: assembles `ContractDSL` from the three
`deriving`-generated glue defs, flushes every buffered `tx`/`view` body into real `def`s, and
emits `{Name}M`, `contractDef`, `config`, `bytecodeHex`, `deployHex`. Because `tx { .. }`
bodies are buffered rather than elaborated immediately (see `tx`'s docstring above), this call
sits once, *after* every `tx`/`view` block. -/
elab "derive_contract " nameStrStx:str storageId:ident errId:ident eventId:ident
    fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")? : command => do
  elabDeriveContract nameStrStx storageId errId eventId fnsStx topic0Stx ctorStx

end Lsc.Syntax
