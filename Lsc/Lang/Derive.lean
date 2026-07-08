import Lsc.Core.ContractM
import Lsc.Lang.AST
import Lsc.Lang.TxM
import Lsc.Compile.Bytecode.Contract
import Lean

/-!
# Custom `deriving` handlers for the storage/error/event glue

Three `deriving` handlers (`ContractStorage`/`ContractEvent`/`ContractError`), attached directly
to plain `structure`/`inductive` declarations, plus internal `elabDeriveContractDsl` (invoked by
the author-facing `derive_contract` command in `Lang/Syntax.lean`) that wires their output into a
`ContractDSL` instance and `ContractDef`. See
`docs/decisions/0006-deriving-handlers-replace-contractgen.md` for why this replaced an earlier
bespoke-syntax codegen approach, including the resolved `Address`/`UInt256` field-kind ambiguity
`fieldKindOfExpr` (below) relies on.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Deriving

/-- Maps a contract's namespace (the namespace `derive_contract_dsl` ran in, i.e. the same
one its function bodies are written in) to its `(errorTypeName, eventTypeName)`, so the
`revert`/`require ... else revert`/`emitEvent` real-constructor sugar below (which need to
know *which* inductive to elaborate `.Paused`/`.Incremented` against) can find it without the
contract author repeating it. Populated by `derive_contract_dsl`; a plain (non-persistent)
`EnvExtension` suffices since storage/error/event types and function bodies always live in
the same file/compilation unit. -/
initialize contractTypesExt : EnvExtension (NameMap (Name × Name)) ←
  registerEnvExtension (pure {})

/-- Maps a contract's namespace to its storage `structure`'s name, so the `lscExpr`/`lscStmt`
grammar's `σ.field` resolution (`Lang/Syntax.lean`) can find *which* structure to run
`getStructureFieldKinds` against without the contract author repeating it — the same
`derive_contract_dsl`-populated-registry pattern as `contractTypesExt` above, kept as a
separate extension (rather than widening `contractTypesExt`'s tuple) so existing
`currContractTypes` callers are unaffected. -/
initialize contractStorageExt : EnvExtension (NameMap Name) ←
  registerEnvExtension (pure {})

/-- Storage-field type tag. See the module docstring for why/how
`Address` and `UInt256` are distinguishable here despite both being
`abbrev`s for the same underlying `Word`/`BitVec 256` type. Moved above
`contractFnsExt`/`contractTxSyntaxExt` (which both reference it) — was
originally declared further below, alongside `fieldKindOfExpr`/`tyConst`/etc. -/
inductive FieldKind
  | wei | wad | bool | address | uint256
  /-- An address-keyed `Lsc.Wad.WadMap` storage field (e.g. ERC20-style per-holder balances,
      `docs/reference/TOKEN.md`) — storage-only: unlike the other five kinds, there is no `Ty`
      case for it at all (it can't be a `tx` parameter, `let`-local, or event payload), so it is
      excluded from every scalar-`Val`-based helper below (`tyConst`/`leanTypeStx`/`valCtor`/...)
      and instead handled by its own dedicated `getMapField`/`setMapField` codegen. -/
  | wadMap
  deriving Repr, DecidableEq

def FieldKind.toTy : FieldKind → Ty
  | .wei => .wei
  | .wad => .wad
  | .bool => .bool
  | .address => .address
  | .uint256 => .uint256
  | .wadMap => .uint256

/-- Callee module prefix → caller storage field holding its address (`Token` → `"token"`). -/
def moduleTargetField (moduleName : Name) : String :=
  let s := moduleName.componentsRev.head!.toString
  if s.isEmpty then s else s.set 0 s.front.toLower

/-- Each registered function's `(abiName, stmtDefName, params)`:
* `abiName` is the fully-qualified name `tx` itself was declared under (e.g. `Smoke.deposit`) —
  the one whose *last component* becomes the ABI-visible function name (`FunctionDef.name`,
  `fnSignature`'s `"deposit(uint256)"`).
* `stmtDefName` is the fully-qualified name of whichever `def` actually holds the parameter-free
  `Stmt` value: for the original zero-arg `tx name { .. }` shape these two coincide (`name`
  itself is both); for a parameterized `tx name(p : ty) { .. }`, `name` instead becomes the real
  *callable* `def name (p : ty) : Stmt := ...` (see `Lang/Syntax.lean`'s `flushContractTxs`), so
  `stmtDefName` points at a separate, hidden `name.Impl` def holding the raw
  (still-`Expr.var`-parameterized) body instead.
* `params` is the declared parameter list (`[]` for the zero-arg shape) — lets
  `derive_contract_def`'s auto-derived `functions` default fill in `FunctionDef.params` for real
  (previously always `[]`), which in turn is what `Lsc.fnSignature`/`Lsc.computeSelector`
  (`Selectors.lean`) need to compute a parameterized function's real ABI selector (e.g.
  `deposit(uint256)`, not `deposit()`). -/
initialize contractFnsExt :
    EnvExtension (NameMap (List (Name × Name × List (String × FieldKind)))) ←
  registerEnvExtension (pure {})

/-- Buffered `tx` entries: `(fnName, plainNameSyntax, params, stmtsSyntax)`, where `params` is
the declared `tx name(p1 : ty1, p2 : ty2) { .. }` parameter list (`[]` for the zero-arg shape),
each resolved to its `FieldKind` already (parsing/resolving the type annotation happens in
`tx`'s own elaborator, immediately — only the `lscStmt*` body needs to stay unelaborated, since
only *that* depends on the not-yet-registered storage/error/event types; a parameter's `ty`
annotation is one of the five fixed `FieldKind` names and needs no such deferral). -/
initialize contractTxSyntaxExt :
    EnvExtension (NameMap (List (Name × Syntax × List (String × FieldKind) × Array Syntax))) ←
  registerEnvExtension (pure {})

/-- `fnName ↦ [(paramName, originalTypeName), ...]` — the author's exact, fully-resolved declared
type for each parameter of a `tx`/`view` (e.g. `Token.Amount`, not the generic `FieldKind` it
resolves to), keyed by fully-qualified `fnName`. Unlike `contractTxSyntaxExt`/
`contractViewSyntaxExt`, this is **not** namespace-scoped/cleared on flush, since it's looked up
from a *different* contract's module later: an `exec`/`read` call site
(`Lang/Syntax.lean`'s `elabExecOrReadTerm`) needs `fn`'s real declared parameter types to
correctly ascribe/`Fixed.retag`-bridge each argument. Stored as a fully-resolved `Name` (not the
raw, possibly namespace-relative syntax as written) so it can be soundly re-spliced from a
different module's namespace later — see `Lsc.Wad.Fixed`'s docstring for why this exact-type
preservation is what makes mixing up two different tokens' amounts a compile error. -/
initialize contractParamTyExt : EnvExtension (NameMap (List (String × Name))) ←
  registerEnvExtension (pure {})

/-- Set of fully-qualified `tx` names (`fnName`, as recorded in `contractFnsExt`) declared
`@nonreentrant` (`Lang/Syntax.lean`'s `tx` decorator). Populated by `tx`'s own elaborator at
buffering time (the decorator is parsed and known immediately, unlike the body, which stays
deferred) and consulted by `elabContractDefBody` when assembling each auto-derived
`FunctionDef.nonReentrant`. -/
initialize contractNonReentrantExt : EnvExtension (NameMap Bool) ←
  registerEnvExtension (pure {})

/-- Set of fully-qualified `tx` names whose raw body contains a top-level `exec` node.
   Used to additionally emit a `PairM` Lean `def` for proof-layer compatibility
   (`examples/escrow/test/EscrowProofs.lean`) while the `Stmt` body is in `ContractDef`. -/
initialize contractExecCallExt : EnvExtension (NameMap Bool) ←
  registerEnvExtension (pure {})

/-- Buffered `view` entries: `(fnName, plainNameSyntax, params, retKind, stmtsSyntax)` — the
`view` counterpart of `contractTxSyntaxExt`, with one extra `retKind` (the declared `: RetTy`
return kind, resolved the same way a `tx` parameter's kind already is — immediately, at
buffering time — see `contractTxSyntaxExt`'s docstring for why the body itself still has to
wait). `stmtsSyntax` is always a real `lscStmt*` block by the time it is buffered here: the
expression-shorthand `view name(..) : Ty => e;` surface form is desugared into a single
synthetic `return e;` node before buffering, so `flushContractViews` only ever has one shape to
elaborate (see `Lang/Syntax.lean`'s `view` elaborators). -/
initialize contractViewSyntaxExt :
    EnvExtension (NameMap (List (Name × Syntax × List (String × FieldKind) × FieldKind × Array Syntax))) ←
  registerEnvExtension (pure {})

/-- Registered `view` functions: `(abiName, stmtDefName, params, retKind)` — the `view`
counterpart of `contractFnsExt`. Unlike `contractFnsExt`, `stmtDefName` *always* points at a
separate hidden `name.Impl` def holding the raw, `Expr.var`-parameterized body (even for a
zero-parameter `view`), since the real, ABI-facing `name` def here is never `Stmt`-valued at all
— it's a callable `ContractM S E Err (Val retKind)` value/function built via `Stmt.evalView`
(`Lang/Syntax.lean`'s `flushContractViews`), so it can never double as the raw body
`elabContractDefBody` needs to embed into `FunctionDef.body` for the bytecode/Yul pipeline. -/
initialize contractViewFnsExt :
    EnvExtension (NameMap (List (Name × Name × List (String × FieldKind) × FieldKind))) ←
  registerEnvExtension (pure {})

/-- Marker classes used purely as `deriving` targets — they carry no data
or methods themselves; all the generated code lives in plain top-level
`def`s/`instance`s emitted by the handlers below (see each handler's
naming convention). Needing `ContractStorage`/`ContractEvent`/
`ContractError` to resolve to *some* declaration is all
`deriving ContractStorage` etc. requires; they don't need to be
"real" type classes with members. -/
class ContractStorage where
class ContractEvent where
class ContractError where

/-- Run `cont` with the *root* namespace as the ambient one, so that
`elabCommand`s issued inside it which use already-fully-qualified
identifiers (e.g. `mkIdent (structName ++ \`getField)`, where `structName`
is itself the fully-resolved, possibly-namespaced name of the user's
`structure`/`inductive`) declare exactly that name, rather than having the
*caller's* current namespace prepended a second time (which would
otherwise produce e.g. `Foo.Foo.TStorage.getField` when `deriving` runs
inside `namespace Foo`). -/
def atRootNamespace (cont : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with currNamespace := Name.anonymous, openDecls := [] }) cont

/-- Pull a raw `Nat` literal out of `e` without ever calling `whnf` (matching `fieldKindOfExpr`'s
own "never `whnf`" discipline, see its docstring below) — a plain numeral like `18`, once
elaborated against an expected `Nat` type, is actually `@OfNat.ofNat Nat 18 (instOfNatNat 18)`,
not a bare `Expr.lit` (`Expr.rawNatLit?` only ever matches the latter); the literal `18` is
nonetheless sitting right there, un-reduced, as `OfNat.ofNat`'s own `n` argument, needing no
`whnf` at all to reach. -/
def natLitOfExpr? (e : Lean.Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none =>
    if e.getAppFn.isConstOf ``OfNat.ofNat then
      match e.getAppArgs with
      | #[_, nExpr, _] => nExpr.rawNatLit?
      | _ => none
    else none

/-- Classify a (necessarily un-`whnf`'d) field-type `Expr` by its literal
head constant. Returns `none` for any type other than the five supported
ones (see module docstring).

**Only `Lsc.Wad.Fixed 18` is accepted** for the `Fixed`-applied case (matching `Lsc.Wad` itself)
— not an arbitrary `Fixed d`: the rest of the `.wad`-kind pipeline (`Wad.Expr`'s
`⸢*⸣?`/`⌊/⌋?` operators, `Lsc/Lib/Wad/Eval.lean`'s `mulHalfUpChecked`/`divDownChecked`) hardcodes
the `WAD = 10^18` scale, so silently accepting e.g. `Fixed 6` here would let a mis-scaled `⸢*⸣?`/
`⌊/⌋?` compile without error instead of being rejected. A genuinely non-18-decimals `Fixed d`
token needs to be authored as a hand-written `ContractM` contract (bypassing this DSL layer
entirely, exactly like `Escrow.release`'s `exec`/`read` already do) until `FieldKind`/`Wad.Expr`
gain real per-`d` scaling — tracked as a follow-up in `docs/todo/backlog.md`. -/
def fieldKindOfExpr (e : Lean.Expr) : Option FieldKind :=
  if e.isConstOf ``Lsc.Wei then some .wei
  else if e.isConstOf ``Lsc.Wad then some .wad
  else if e.isConstOf ``Bool then some .bool
  else if e.isConstOf ``Lsc.Address then some .address
  else if e.isConstOf ``Lsc.UInt256 then some .uint256
  else if e.isConstOf ``Lsc.Wad.WadMap then some .wadMap
  else if e.getAppFn.isConstOf ``Lsc.Wad.Fixed then
    -- `Fixed` now takes two explicit args (`decimals`, `tag` — see that structure's docstring);
    -- `tag` is intentionally ignored here: it's purely a Lean-level nominal marker distinguishing
    -- *which token* an amount belongs to, invisible to `FieldKind`/`Ty`/`Val`/codegen, which stay
    -- homogeneous across every token (the tag is threaded through separately, at the
    -- `tx`/`view` Lean-signature level only — see `Lang/Syntax.lean`'s `flushContractTxs`/
    -- `flushContractViews`).
    match e.getAppArgs with
    | #[dExpr, _tagExpr] => if natLitOfExpr? dExpr == some 18 then some .wad else none
    | _ => none
  else none

/-- Best-effort alias resolution for a field type that isn't *literally* `Lsc.Wad`/
`Lsc.Wad.Fixed 18` (`fieldKindOfExpr`'s own two `Wad`-shaped cases above), e.g. a token
declaring `abbrev Token.Amount := Lsc.Wad` right next to its storage, so `Escrow`-style callers
can name that token's own unit instead of the generic `Wad` (see `docs/reference/TOKEN.md`).
Only ever unfolds a chain of bare `def`/`abbrev` *names* one level at a time, stopping the
moment a level's value isn't itself a plain constant — it deliberately never calls `whnf`, so it
can never walk into `BitVec 256` and collapse `Address`/`UInt256` into each other (see this
file's module docstring's "`Address`/`UInt256` ambiguity" section: that guarantee depends on
*never* generically unfolding, which this preserves — the fallback below only ever fires for a
name whose *unfolded* value is itself found to be `Wad`-shaped, never for `BitVec`/`Address`/
`UInt256` itself, since those never reduce to that shape). Still only ever accepts an eventual
`Fixed 18` (never a different `d`), for the same soundness reason `fieldKindOfExpr` restricts its
own direct `Fixed`-applied case — see that docstring. Bounded fuel purely to guarantee
termination against a (framework-impossible, since `deriving` runs on well-founded declarations)
cyclic alias chain. -/
partial def resolveFixedAlias (e : Lean.Expr) (fuel : Nat := 8) : TermElabM Bool := do
  if fieldKindOfExpr e == some .wad then return true
  else
    match fuel, e.constName? with
    | 0, _ | _, none => return false
    | fuel + 1, some n =>
      match (← getConstInfo n).value? with
      | some v => resolveFixedAlias v fuel
      | none => return false

/-- `fieldKindOfExpr`'s monadic counterpart — tries the pure, purely-syntactic check first, then
falls back to `resolveFixedAlias` for a `Wad`-shaped named alias (e.g. `Token.Amount`). All three
call sites below are already in `TermElabM`, so this costs nothing extra when the pure check
already succeeds (the common case for the original five keyword-named types). -/
def fieldKindOfExprM (e : Lean.Expr) : TermElabM (Option FieldKind) := do
  match fieldKindOfExpr e with
  | some k => return some k
  | none => return if (← resolveFixedAlias e) then some .wad else none

def FieldKind.tyConst : FieldKind → TermElabM Term
  | .wei => `(Lsc.Ty.wei)
  | .wad => `(Lsc.Ty.wad)
  | .bool => `(Lsc.Ty.bool)
  | .address => `(Lsc.Ty.address)
  | .uint256 => `(Lsc.Ty.uint256)
  | .wadMap => throwError "internal error: `FieldKind.wadMap` has no `Ty` (storage-only kind)"

/-- The real Lean *value* type a `tx` parameter of this kind is declared with on the generated
callable `def name (p : <leanTypeStx>) : Stmt := ...` (see `Lang/Syntax.lean`'s `flushContractTxs`)
— distinct from `exprTypeStx` above, which is the *expression-builder* type (`Wei.Expr`/
`CoreExpr _`) used while a `Stmt`/`Expr` AST fragment is still being built, not the concrete
runtime value type a caller actually supplies. -/
def FieldKind.leanTypeStx : FieldKind → TermElabM Term
  | .wei => `(Lsc.Wei)
  | .wad => `(Lsc.Wad)
  | .bool => `(Bool)
  | .address => `(Lsc.Address)
  | .uint256 => `(Lsc.UInt256)
  | .wadMap => throwError "internal error: `FieldKind.wadMap` is storage-only (not a `tx` parameter kind)"

/-- Embed a `tx` parameter's real Lean *value* (`paramId : leanTypeStx`) as a literal
`Expr`/`CoreExpr` AST node of the matching kind — the bridge between "generated `def` takes a
real Lean function argument" and "the `Stmt` AST's `Expr.var` needs a `LocalEnv` binding": rather
than threading a `LocalEnv` through `Stmt.eval`'s public entry point (a much larger change), the
generated callable `def` instead wraps the parameter-free body `Stmt` in one extra
`Stmt.letBind paramName ⟨ty, <this literal>⟩` per parameter, so `Stmt.eval`'s existing
`LocalEnv.empty` start is populated by the *first* statements it evaluates, exactly the same
"evaluate-once local binding" mechanism `let x = e;`/`letWei`/... already rely on (see
`Lang/Syntax.lean`'s module docstring). `Wei`/`Wad`'s `Expr.lit` only stores a `Nat`
(`w.raw.toNat`), which round-trips exactly back to `w` via `Wei.mkNat`/`Wad.mkNat` since `raw` is
already a 256-bit `BitVec`; `CoreExpr.lit`'s `Lit` constructors instead store the real value
type directly (`UInt256`/`Bool`/`Address`), needing no such round-trip. -/
def FieldKind.embedLitStx (k : FieldKind) (paramId : Term) : TermElabM Term :=
  match k with
  | .wei => `(Lsc.Wei.Expr.lit ($paramId).raw.toNat)
  | .wad => `(Lsc.Wad.Expr.lit ($paramId).raw.toNat)
  | .bool => `(Lsc.CoreExpr.lit Lsc.Ty.bool (Lsc.Lit.bool $paramId))
  | .address => `(Lsc.CoreExpr.lit Lsc.Ty.address (Lsc.Lit.addr $paramId))
  | .uint256 => `(Lsc.CoreExpr.lit Lsc.Ty.uint256 (Lsc.Lit.u256 $paramId))
  | .wadMap => throwError "internal error: `FieldKind.wadMap` is storage-only (not embeddable as a literal)"

/-- Wrap a plain term as a `matchDiscr` for splicing into `match $[$discrs],* with …`. -/
def mkDiscr (t : Term) : TermElabM (TSyntax ``Lean.Parser.Term.matchDiscr) :=
  `(Lean.Parser.Term.matchDiscr| $t:term)

def FieldKind.valCtor : FieldKind → TermElabM Term
  | .wei => `(Lsc.Val.wei)
  | .wad => `(Lsc.Val.wad)
  | .bool => `(Lsc.Val.bool)
  | .address => `(Lsc.Val.addr)
  | .uint256 => `(Lsc.Val.u256)
  | .wadMap => throwError "internal error: `FieldKind.wadMap` has no `Val` case (storage-only kind)"

/-- Bridge a `.wad`-kind value between its field's *own* possibly-tagged type (e.g.
`Token.Amount`, `Lsc.Wad.Fixed 18 Token.Tag`) and `Val.wad`'s generic, always-`Untagged`-tagged
`Lsc.Wad` — a plain identity for every other `FieldKind` (whose declared type is never an alias
at all, only ever the one literal type `fieldKindOfExpr` accepts). Needed at every
`getField`/`setField`/`buildEvent` call site touching a `.wad`-kind field/event-payload: since
`Val`/`Ty` (`valCtor`'s targets) are the DSL's single, global, tag-erased types (see
`Lang/Syntax.lean`'s `flushContractViews`' docstring for the fuller story), a storage field or
event payload declared with a token's own tagged `Amount` is no longer *defeq* to the generic
`Wad` `Val.wad`/`Val.wadOf` expect, now that `Fixed`'s `tag` parameter is a genuine nominal
marker (`Lsc.Wad.Fixed`'s docstring) — `Fixed.retag` is the sound, zero-cost (same `raw` field,
no value change at all) bridge in both directions. -/
def FieldKind.bridgeGeneric (k : FieldKind) (e : Term) : TermElabM Term :=
  match k with
  | .wad => `(Lsc.Wad.Fixed.retag $e)
  | _ => pure e

/-- The *expression* (not value) Lean type carrying a field of this kind while a
`Stmt`/`Expr` AST fragment is being built — `Wei.Expr` for `.wei`, `CoreExpr <tyConst>`
otherwise. Used by the `σ.field`-generation below, so `σ.number : Wei.Expr` and
`σ.paused : CoreExpr Ty.bool` come out with exactly the same Lean types the hand-written
`wei σ.field`/`bool σ.field` notation family (`TxM.lean`) already produces. -/
def FieldKind.exprTypeStx : FieldKind → TermElabM Term
  | .wei => `(Lsc.Wei.Expr)
  | .wad => `(Lsc.Wad.Expr)
  | .bool => `(Lsc.CoreExpr Lsc.Ty.bool)
  | .address => `(Lsc.CoreExpr Lsc.Ty.address)
  | .uint256 => `(Lsc.CoreExpr Lsc.Ty.uint256)
  | .wadMap =>
    throwError "internal error: `FieldKind.wadMap` has no plain `σ.field` expression form \
      (index it with `σ.field[key]` instead)"

/-- The default (i.e. only, since these are never written by contract authors — they're
generated) value of a `σ.field` constant: a fresh `storageGet` expression fragment
referencing `fieldStr`, identical in shape to what `wei σ.field`/`bool σ.field`/... build
today (`TxM.lean`'s `weiField`/`boolField`/`addrField`/`u256Field`). -/
def FieldKind.storageGetStx (k : FieldKind) (fieldStr : String) : TermElabM Term := do
  let fieldLit := quote fieldStr
  match k with
  | .wei => `(Lsc.Wei.Expr.storageGet $fieldLit)
  | .wad => `(Lsc.Wad.Expr.storageGet $fieldLit)
  | .bool => `(Lsc.CoreExpr.storageGet Lsc.Ty.bool $fieldLit)
  | .address => `(Lsc.CoreExpr.storageGet Lsc.Ty.address $fieldLit)
  | .uint256 => `(Lsc.CoreExpr.storageGet Lsc.Ty.uint256 $fieldLit)
  | .wadMap =>
    throwError "internal error: `FieldKind.wadMap` has no plain `σ.field` expression form \
      (index it with `σ.field[key]` instead)"

/-! ## `deriving ContractStorage`

Naming convention: for a storage structure `S`, this emits top-level defs
`S.getField`/`S.setField` (i.e. `def S.getField …`/`def S.setField …`,
found later by `derive_contract_dsl` via plain dot-notation, e.g.
`$S.getField`). -/

/-- Introspect `structName`'s fields, classifying each one's `FieldKind`.
Throws a clear error (naming the offending field) for any field whose
type isn't one of the four supported tags. -/
def getStructureFieldKinds (structName : Name) : TermElabM (Array (Name × FieldKind)) := do
  let env ← getEnv
  let fieldNames := getStructureFields env structName
  fieldNames.mapM fun fname => do
    let some info := getFieldInfo? env structName fname
      | throwError "deriving ContractStorage: internal error, no field info for `{fname}`"
    let ci ← getConstInfo info.projFn
    -- `ci.type : (s : structName) → FieldType` (no dependency on `s` in our
    -- supported cases) — `bindingBody!` extracts `FieldType` without
    -- triggering any `whnf`/unfolding (see module docstring).
    let fieldTy := ci.type.bindingBody!
    match ← fieldKindOfExprM fieldTy with
    | some k => return (fname, k)
    | none =>
      throwError "deriving ContractStorage: field `{fname}` of `{structName}` has unsupported type `{fieldTy}` \
        — storage fields must be declared with exactly one of `Wei`/`Wad`/`Bool`/`Address`/`UInt256` written literally, \
        or a named `Wad`/`Lsc.Wad.Fixed d`-shaped alias (e.g. `Token.Amount`) \
        (see `Lsc.Deriving`'s module docstring for why this can't be fully generic)"

def mkGetFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let getFieldName := mkIdent (structName ++ `getField)
  let tId := mkIdent `t
  let fieldId := mkIdent `field
  let sId := mkIdent `s
  -- `wadMap` fields have no `Ty`/`Val` case at all (storage-only, see `FieldKind.wadMap`'s
  -- docstring) — never matched here, only through the dedicated `getMapField` below.
  let fields := fields.filter (·.2 != .wadMap)
  let arms ← fields.mapM fun (fname, k) => do
    let tyConst ← k.tyConst
    let valCtor ← k.valCtor
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    let pats : Array Term := #[tyConst, fieldStr]
    let bridged ← k.bridgeGeneric (← `($sId.$fId))
    `(matchAltExpr| | $[$pats],* => some ($valCtor $bridged))
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => none)
  let alts := arms.push defaultArm
  let discrs ← #[tId, fieldId].mapM mkDiscr
  `(command| def $getFieldName ($tId : Lsc.Ty) ($fieldId : String) ($sId : $structId) : Option (Lsc.Val $tId) :=
      match $[$discrs],* with
      $alts:matchAlt*)

def mkSetFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let setFieldName := mkIdent (structName ++ `setField)
  let tId := mkIdent `t
  let fieldId := mkIdent `field
  let vId := mkIdent `v
  let sId := mkIdent `s
  let fields := fields.filter (·.2 != .wadMap)
  let arms ← fields.mapM fun (fname, k) => do
    let valCtor ← k.valCtor
    let tyConst ← k.tyConst
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    let varId ← `(x)
    let valPat ← `($valCtor $varId)
    let bridged ← k.bridgeGeneric varId
    let body ← `({ $sId with $fId:ident := $bridged })
    let pats : Array Term := #[tyConst, fieldStr, valPat]
    `(matchAltExpr| | $[$pats],* => $body)
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => $sId)
  let alts := arms.push defaultArm
  let discrs ← #[tId, fieldId, vId].mapM mkDiscr
  `(command| def $setFieldName ($tId : Lsc.Ty) ($fieldId : String) ($vId : Lsc.Val $tId) ($sId : $structId) : $structId :=
      match $[$discrs],* with
      $alts:matchAlt*)

/-- `def S.getMapField (field : String) (a : Lsc.Address) (s : S) : Option Lsc.Wad.Wad`, one
match arm per `wadMap`-kinded field of `structName` — always generated (even as just the
default `| _ => none` arm, if `structName` declares no `wadMap` field at all), so
`derive_contract_dsl`'s generated `ContractDSL` instance can uniformly reference
`S.getMapField` regardless of whether `S` happens to have a mapping field. -/
def mkGetMapFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let getMapFieldName := mkIdent (structName ++ `getMapField)
  let fieldId := mkIdent `field
  let aId := mkIdent `a
  let sId := mkIdent `s
  let mapFields := fields.filter (·.2 == .wadMap)
  let arms ← mapFields.mapM fun (fname, _) => do
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    `(matchAltExpr| | $fieldStr => some ($sId.$fId $aId))
  let wc ← `(_)
  let defaultArm ← `(matchAltExpr| | $wc => none)
  let alts := arms.push defaultArm
  let discrs ← #[(fieldId : Term)].mapM mkDiscr
  `(command|
    def $getMapFieldName ($fieldId : String) ($aId : Lsc.Address) ($sId : $structId) :
        Option Lsc.Wad.Wad :=
      match $[$discrs],* with
      $alts:matchAlt*)

/-- `def S.setMapField (field : String) (a : Lsc.Address) (v : Lsc.Wad.Wad) (s : S) : S`, the
write-side counterpart of `mkGetMapFieldCmd` — a no-op (`s` unchanged) if `field` doesn't name a
`wadMap` field. The generated `fun a' => if a' == a then v else $fId a'` update matches
`Lsc.Wad.WadMap`'s "total function" model exactly (see that type's docstring). -/
def mkSetMapFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let setMapFieldName := mkIdent (structName ++ `setMapField)
  let fieldId := mkIdent `field
  let aId := mkIdent `a
  let vId := mkIdent `v
  let sId := mkIdent `s
  let mapFields := fields.filter (·.2 == .wadMap)
  let arms ← mapFields.mapM fun (fname, _) => do
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    let aPrimeId := mkIdent `a'
    let updated ← `(fun ($aPrimeId : Lsc.Address) => if $aPrimeId == $aId then $vId else $sId.$fId $aPrimeId)
    let body ← `({ $sId with $fId:ident := $updated })
    `(matchAltExpr| | $fieldStr => $body)
  let wc ← `(_)
  let defaultArm ← `(matchAltExpr| | $wc => $sId)
  let alts := arms.push defaultArm
  let discrs ← #[(fieldId : Term)].mapM mkDiscr
  `(command|
    def $setMapFieldName ($fieldId : String) ($aId : Lsc.Address) ($vId : Lsc.Wad.Wad) ($sId : $structId) :
        $structId :=
      match $[$discrs],* with
      $alts:matchAlt*)

/-- One `def $ns.σ.$field : <exprTy> := <storageGet>` per storage field, where `$ns` is the
namespace the storage `structure` was declared in (`structName`'s namespace — i.e. the same
namespace a contract's function bodies are written in). This makes `σ` a plain Lean
*namespace* (not a value + structure-field-projection trick), so `σ.number`/`σ.paused`/...
resolve via ordinary unqualified-name lookup exactly like `getField`/`setField` already do —
no custom parsing, no tokeniser risk, no environment-extension lookup needed at use sites.
Replaces the hand-written `wei σ.field`/`bool σ.field`/... type-tagged prefix notation
family (`TxM.lean`) as the recommended read syntax; those stay available underneath (this
generates plain `def`s of the same shape their combinators already build, nothing removed). -/
def mkSigmaFieldCmds (structName : Name) (fields : Array (Name × FieldKind)) :
    TermElabM (Array Command) := do
  let ns := structName.getPrefix
  -- A `wadMap` field has no plain `σ.field` form at all — only `σ.field[key]`
  -- (`Lang/Syntax.lean`'s dedicated grammar), so it's excluded here.
  let fields := fields.filter (·.2 != .wadMap)
  fields.mapM fun (fname, k) => do
    let sigmaFieldName := mkIdent (ns ++ `σ ++ fname)
    let tyStx ← k.exprTypeStx
    let valStx ← k.storageGetStx fname.toString
    `(command| @[simp] def $sigmaFieldName : $tyStx := $valStx)

/-- `instance : Inhabited $structName where default := {}` — every field kind
`ContractStorage` supports (`Wei`/`Wad`/`Bool`/`Address`/`UInt256`) has a Lean
default value, and storage structures are expected to give each field a
default, so `{}` always resolves. Saves contract authors from hand-writing
this instance (needed by `ContractM`'s default-storage handling) themselves. -/
def mkInhabitedCmd (structName : Name) : TermElabM Command :=
  `(command| instance : Inhabited $(mkIdent structName) where default := {})

def mkContractStorageHandler : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  let structName := declNames[0]!
  let env ← getEnv
  unless isStructure env structName do return false
  let fieldKinds ← liftTermElabM do
    let indVal ← getConstInfoInduct structName
    if indVal.numParams != 0 then
      throwError "deriving ContractStorage: parametric structures are not supported (`{structName}`)"
    getStructureFieldKinds structName
  let getCmd ← liftTermElabM <| mkGetFieldCmd structName fieldKinds
  let setCmd ← liftTermElabM <| mkSetFieldCmd structName fieldKinds
  let getMapCmd ← liftTermElabM <| mkGetMapFieldCmd structName fieldKinds
  let setMapCmd ← liftTermElabM <| mkSetMapFieldCmd structName fieldKinds
  let sigmaCmds ← liftTermElabM <| mkSigmaFieldCmds structName fieldKinds
  let inhabitedCmd ← liftTermElabM <| mkInhabitedCmd structName
  atRootNamespace do
    elabCommand getCmd
    elabCommand setCmd
    elabCommand getMapCmd
    elabCommand setMapCmd
    for c in sigmaCmds do elabCommand c
    elabCommand inhabitedCmd
  return true

initialize registerDerivingHandler ``ContractStorage mkContractStorageHandler

/-! ## `deriving ContractEvent`

Naming convention: for an event inductive `E`, this emits a top-level
`E.buildEvent`. Per `ContractGen.lean`/`Counter.lean`, event constructors
support 0 or 1 parameter today — multi-param events aren't supported by
the rest of the pipeline yet, so a constructor with more than one
parameter is a clear `deriving`-time error rather than a silent
mis-generation. -/

/-- For a 0- or 1-arg constructor, return `none` (no payload) or
`some (paramName, kind)`. Throws for >1 params (unsupported, see above)
or for a payload type outside the four supported tags. -/
def getCtorFieldKind (ctorName : Name) : TermElabM (Option FieldKind) := do
  let ci ← getConstInfoCtor ctorName
  forallTelescopeReducing ci.type fun xs _ => do
    if xs.size == 0 then return none
    if xs.size > 1 then
      throwError "deriving ContractEvent: constructor `{ctorName}` has {xs.size} parameters; \
        only 0- or 1-parameter events are currently supported"
    let ty ← inferType xs[0]!
    match ← fieldKindOfExprM ty with
    | some k => return some k
    | none =>
      throwError "deriving ContractEvent: constructor `{ctorName}`'s parameter has unsupported type `{ty}` \
        — event payloads must be `Wei`/`Wad`/`Bool`/`Address`/`UInt256` (or a `Wad`-shaped alias)"

/-- Like `getCtorFieldKind`, but also returns the payload's declared parameter
name (needed to reconstruct `ContractDef.events`'s `(paramName, ty)` shape in
`derive_contract_def`). -/
def getCtorFieldNameKind (ctorName : Name) : TermElabM (Option (Name × FieldKind)) := do
  let ci ← getConstInfoCtor ctorName
  forallTelescopeReducing ci.type fun xs _ => do
    if xs.size == 0 then return none
    if xs.size > 1 then
      throwError "derive_contract_def: constructor `{ctorName}` has {xs.size} parameters; \
        only 0- or 1-parameter events are currently supported"
    let ty ← inferType xs[0]!
    let paramName ← xs[0]!.fvarId!.getUserName
    match ← fieldKindOfExprM ty with
    | some k => return some (paramName, k)
    | none =>
      throwError "derive_contract_def: constructor `{ctorName}`'s parameter has unsupported type `{ty}` \
        — event payloads must be `Wei`/`Wad`/`Bool`/`Address`/`UInt256` (or a `Wad`-shaped alias)"

def mkBuildEventCmd (indName : Name) (ctors : Array Name) : TermElabM Command := do
  let evtId := mkIdent indName
  let buildEventName := mkIdent (indName ++ `buildEvent)
  let nameId := mkIdent `name
  let valsId := mkIdent `vals
  let arms ← ctors.mapM fun ctorName => do
    let cStr := ctorName.getString!
    let nameStr := quote cStr
    match ← getCtorFieldKind ctorName with
    | none =>
      let ctorShortId := mkIdent (Name.mkSimple cStr)
      let emptyList ← `(([] : List (Sigma Lsc.Val)))
      let body ← `(some (.$ctorShortId : $evtId))
      let pats : Array Term := #[nameStr, emptyList]
      `(matchAltExpr| | $[$pats],* => $body)
    | some k =>
      let tyConst ← k.tyConst
      let valCtor ← k.valCtor
      let varId ← `(x)
      let valPat ← `($valCtor $varId)
      let listPat ← `([⟨$tyConst, $valPat⟩])
      let fullCtorId := mkIdent ctorName
      let bridged ← k.bridgeGeneric varId
      let body ← `(some ($fullCtorId $bridged))
      let pats : Array Term := #[nameStr, listPat]
      `(matchAltExpr| | $[$pats],* => $body)
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => none)
  let alts := arms.push defaultArm
  let discrs ← #[nameId, valsId].mapM mkDiscr
  `(command| def $buildEventName ($nameId : String) ($valsId : List (Sigma Lsc.Val)) : Option $evtId :=
      match $[$discrs],* with
      $alts:matchAlt*)

def mkContractEventHandler : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  let indName := declNames[0]!
  let indValOpt ← liftTermElabM <| try some <$> getConstInfoInduct indName catch _ => pure none
  let some indVal := indValOpt | return false
  if isStructure (← getEnv) indName then return false
  if indVal.numParams != 0 then
    throwError "deriving ContractEvent: parametric inductives are not supported (`{indName}`)"
  if indVal.isRec then
    throwError "deriving ContractEvent: recursive inductives are not supported (`{indName}`)"
  let cmd ← liftTermElabM <| mkBuildEventCmd indName indVal.ctors.toArray
  atRootNamespace <| elabCommand cmd
  return true

initialize registerDerivingHandler ``ContractEvent mkContractEventHandler

/-! ## `deriving ContractError`

Naming convention: for an error inductive `Err`, this emits:
* `Err.resolveError` — purely structural, one arm per constructor.
* `instance : Inhabited Err` (defaulting to the first declared
  constructor) — needed by `ContractErrors.unreachableArith`'s
  `[Inhabited Err]` requirement.
* `instance : Lsc.ContractErrors Err` — `arith`/`fromFramework` arms are
  filled in by *name-matching* against `ArithError`
  (`Overflow`/`Underflow`/`DivisionByZero`) and `FrameworkError`
  (`Reentrant`/`Unauthorized`/`InvalidSelector`/`ExternalCallFailed`)
  constructors: a
  same-named constructor in `Err` maps directly; an unmatched case falls
  back to `ContractErrors.unreachableArith` (for `arith`) or the first
  declared `Err` constructor (for `fromFramework`) — **per `FrameworkError`
  constructor**, independently: e.g. an `Err` with both `Reentrant` and
  `ExternalCallFailed` constructors gets each mapped to itself, while an
  `Err` with only `Reentrant` gets `Unauthorized`/`InvalidSelector`/
  `ExternalCallFailed` all falling back to the first declared `Err`
  constructor (typically `Reentrant` itself, if declared first) — this
  generalizes `Counter.lean`'s original hand-written instance (which only
  ever had one fixed fallback constructor for *every* `FrameworkError`
  case, unable to give `ExternalCallFailed` its own distinct mapping the
  way `Escrow`'s hand-written instance needs, see `docs/reference/
  ESCROW.md`).

  IMPORTANT (intentional, see the plan's "Resolved: `ContractError`
  derivation example" section): this handler only does what's decidable
  from the *inductive's constructor names alone*, at the point
  `deriving ContractError` runs — i.e. *before* any function bodies
  exist. It does **not** attempt to verify that every `ArithError`/
  `FrameworkError` case actually reachable from the contract's function
  bodies has a real (non-fallback) mapping; turning an actually-reachable
  but unmapped case into a loud compile error is the job of the
  *separate*, later `Lang/Checks.lean` arith-error-coverage pass (step 3
  of the migration plan), which runs after all function bodies are known. -/

def arithErrorCtorNames : Array String := #["Overflow", "Underflow", "DivisionByZero"]

/-- Must list *every* `Lsc.FrameworkError` constructor (`Lsc/Core/ContractM.lean`), in
declaration order — `mkContractErrorsInstanceCmd`'s `fromFramework` match is built directly from
this list and relies on it being exhaustive over the real inductive's shape (no trailing
wildcard arm is emitted); adding a new `FrameworkError` constructor without adding it here would
make the generated `fromFramework` non-exhaustive, a compile error at every contract's own
`deriving ContractError` site rather than a silent gap. -/
def frameworkErrorCtorNames : Array String :=
  #["Reentrant", "Unauthorized", "InvalidSelector", "ExternalCallFailed"]

def mkResolveErrorCmd (indName : Name) (ctorStrs : Array String) : TermElabM Command := do
  let errId := mkIdent indName
  let resolveErrName := mkIdent (indName ++ `resolveError)
  let nameId := mkIdent `name
  let arms ← ctorStrs.mapM fun cstr => do
    let nameStr := quote cstr
    let ctorId := mkIdent (Name.mkSimple cstr)
    let body ← `(some (.$ctorId : $errId))
    `(matchAltExpr| | $nameStr => $body)
  let wc ← `(_)
  let defaultArm ← `(matchAltExpr| | $wc => none)
  let alts := arms.push defaultArm
  let discrs ← #[nameId].mapM mkDiscr
  `(command| def $resolveErrName ($nameId : String) : Option $errId :=
      match $[$discrs],* with
      $alts:matchAlt*)

def mkContractErrorsInstanceCmd (indName : Name) (ctorStrs : Array String) : TermElabM Command := do
  let errId := mkIdent indName
  -- `arith`: same-named `ArithError` constructors map directly; anything
  -- else falls back to `ContractErrors.unreachableArith` (requires
  -- `Inhabited Err`, emitted separately just before this instance).
  let arithArms ← arithErrorCtorNames.filterMapM fun an => do
    if ctorStrs.contains an then
      -- Built as one fully-qualified identifier (not `Lsc.ArithError.$aeId`
      -- dot-syntax) since splicing an antiquotation after a literal dotted
      -- prefix parses as *field-projection* notation, which isn't valid in
      -- pattern position ("Invalid pattern").
      let fullPat := mkIdent (`Lsc.ArithError ++ Name.mkSimple an)
      let aeId := mkIdent (Name.mkSimple an)
      let body ← `(.$aeId)
      some <$> `(matchAltExpr| | $fullPat:term => $body)
    else
      pure none
  let aeWc := mkIdent `ae
  let fallbackBody ← `(Lsc.ContractErrors.unreachableArith $aeWc)
  let arithDefault ← `(matchAltExpr| | $aeWc => $fallbackBody)
  -- If every `ArithError` constructor already has a same-named `Err` arm above (e.g. a
  -- contract using both `Wei` and `Wad` arithmetic, whose error type names all three of
  -- `Overflow`/`Underflow`/`DivisionByZero`), a trailing wildcard default arm is dead code —
  -- Lean's match compiler rejects it outright ("Redundant alternative") rather than silently
  -- ignoring it, so it must be omitted in that case rather than always appended.
  let arithAlts :=
    if arithErrorCtorNames.all ctorStrs.contains then arithArms else arithArms.push arithDefault
  let arithDiscrs ← #[(aeWc : Term)].mapM mkDiscr
  let arithMatch ← `(fun $aeWc => match $[$arithDiscrs],* with $arithAlts:matchAlt*)
  -- `fromFramework`: real per-constructor matching — each of `FrameworkError`'s constructors
  -- independently prefers a same-named `Err` constructor if one is declared, else falls back to
  -- the first declared `Err` constructor. This is exhaustive over `FrameworkError`'s fixed shape
  -- (`frameworkErrorCtorNames`, kept in lockstep with the real inductive by hand — see that
  -- `def`'s docstring), so no trailing wildcard arm is needed.
  let firstCtorStr := ctorStrs[0]!
  let feId := mkIdent `fe
  let fwArms ← frameworkErrorCtorNames.mapM fun fen => do
    let fwPat := mkIdent (`Lsc.FrameworkError ++ Name.mkSimple fen)
    let targetCtorStr := if ctorStrs.contains fen then fen else firstCtorStr
    let targetCtorId := mkIdent (Name.mkSimple targetCtorStr)
    let body ← `(.$targetCtorId)
    `(matchAltExpr| | $fwPat:term => $body)
  let fwDiscrs ← #[(feId : Term)].mapM mkDiscr
  let fwMatch ← `(fun $feId => match $[$fwDiscrs],* with $fwArms:matchAlt*)
  `(command|
    instance : Lsc.ContractErrors $errId where
      arith := $arithMatch
      fromFramework := $fwMatch)

def mkContractErrorHandler : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  let indName := declNames[0]!
  let indValOpt ← liftTermElabM <| try some <$> getConstInfoInduct indName catch _ => pure none
  let some indVal := indValOpt | return false
  if isStructure (← getEnv) indName then return false
  if indVal.numParams != 0 then
    throwError "deriving ContractError: parametric inductives are not supported (`{indName}`)"
  if indVal.ctors.isEmpty then
    throwError "deriving ContractError: `{indName}` has no constructors"
  liftTermElabM do
    for c in indVal.ctors do
      let ci ← getConstInfoCtor c
      forallTelescopeReducing ci.type fun xs _ =>
        if xs.size != 0 then
          throwError "deriving ContractError: constructor `{c}` has parameters; \
            error constructors must be nullary"
        else
          pure ()
  let ctorStrs := indVal.ctors.toArray.map (·.getString!)
  let firstCtorId := mkIdent (Name.mkSimple ctorStrs[0]!)
  let resolveCmd ← liftTermElabM <| mkResolveErrorCmd indName ctorStrs
  let errorsCmd ← liftTermElabM <| mkContractErrorsInstanceCmd indName ctorStrs
  atRootNamespace do
    elabCommand (← `(command| instance : Inhabited $(mkIdent indName) where default := .$firstCtorId))
    elabCommand resolveCmd
    elabCommand errorsCmd
  return true

initialize registerDerivingHandler ``ContractError mkContractErrorHandler

/-! ## Internal DSL assembly (`elabDeriveContractDsl`)

Wires the three `deriving`-generated pieces (found purely by the naming convention
documented above — `S.getField`/`S.setField`/`Err.resolveError`/
`E.buildEvent`, all reachable from `S`/`Err`/`E` via plain Lean
dot-notation since they're declared as `S.getField` etc.) plus the
`ContractErrors Err` instance (found by ordinary typeclass resolution —
no naming convention needed since it's anonymous) into the final
`ContractDSL` instance. Invoked internally by `derive_contract` in
`Lang/Syntax.lean`, not exposed as a separate author command. -/
/-! ### Auto-generated `@[simp]` DSL-projection lemmas

`Stmt.evalWith`'s simp set (`Lang/Eval.lean`) only unfolds as far as
`dsl.getField`/`dsl.setField`/`dsl.resolveErr`/`dsl.buildEvent` (the
`ContractDSL` *projections*); without lemmas relating those projections
back to the concrete derived defs, `simp` cannot see through the
(reducible but not `@[simp]`) `ContractDSL` instance `elabDeriveContractDsl`
assembles to actually evaluate a `getField`/`setField`/... call. Marking
the generated defs themselves `@[simp]` (so their own `match` equations
fire) plus relating the class projections to them via the four `rfl`
lemmas below is what previously had to be hand-written per-contract (see
e.g. `examples/counter/src/Counter.lean`'s history) — `elabDeriveContractDsl`
now emits all of this itself. -/

/-- `@ContractDSL.getField S E Err _ _ t f s = S.getField t f s`, as a `rfl` lemma. -/
def mkDslGetFieldLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let getFieldRef := mkIdent (storageName ++ `getField)
  let tId := mkIdent `t
  let fId := mkIdent `f
  let sVarId := mkIdent `s
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident ($tId : Lsc.Ty) ($fId : Lsc.Ident) ($sVarId : $sId) :
        @Lsc.ContractDSL.getField $sId $eId $errIdT _ _ $tId $fId $sVarId =
          $getFieldRef $tId $fId $sVarId := rfl)

def mkDslSetFieldLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let setFieldRef := mkIdent (storageName ++ `setField)
  let tId := mkIdent `t
  let fId := mkIdent `f
  let vId := mkIdent `v
  let sVarId := mkIdent `s
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident
        ($tId : Lsc.Ty) ($fId : Lsc.Ident) ($vId : Lsc.Val $tId) ($sVarId : $sId) :
        @Lsc.ContractDSL.setField $sId $eId $errIdT _ _ $tId $fId $vId $sVarId =
          $setFieldRef $tId $fId $vId $sVarId := rfl)

/-- `getMapField`/`setMapField`'s own `ContractDSL`-projection bridging lemma, exactly mirroring
`mkDslGetFieldLemma`/`mkDslSetFieldLemma` above (see those docstrings) — without this, `simp`
has no way to unfold `@ContractDSL.getMapField/setMapField S E Err _ _ ...` (a structure
projection applied to the `@[reducible] instance` `derive_contract_dsl` builds below) back down
to the concrete, `match`-based `$storageId.getMapField`/`setMapField` those instance fields are
literally assigned to — needed for any symbolic (non-`native_decide`) proof about a `tx` that
reads/writes a `Lsc.Wad.WadMap` storage field (e.g. `examples/escrow`'s `Token.transfer`). -/
def mkDslGetMapFieldLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let getMapFieldRef := mkIdent (storageName ++ `getMapField)
  let fId := mkIdent `f
  let aId := mkIdent `a
  let sVarId := mkIdent `s
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident ($fId : Lsc.Ident) ($aId : Lsc.Address) ($sVarId : $sId) :
        @Lsc.ContractDSL.getMapField $sId $eId $errIdT _ _ $fId $aId $sVarId =
          $getMapFieldRef $fId $aId $sVarId := rfl)

def mkDslSetMapFieldLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let setMapFieldRef := mkIdent (storageName ++ `setMapField)
  let fId := mkIdent `f
  let aId := mkIdent `a
  let vId := mkIdent `v
  let sVarId := mkIdent `s
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident
        ($fId : Lsc.Ident) ($aId : Lsc.Address) ($vId : Lsc.Wad.Wad) ($sVarId : $sId) :
        @Lsc.ContractDSL.setMapField $sId $eId $errIdT _ _ $fId $aId $vId $sVarId =
          $setMapFieldRef $fId $aId $vId $sVarId := rfl)

def mkDslResolveErrLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let resolveErrRef := mkIdent (errName ++ `resolveError)
  let nameId := mkIdent `name
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident ($nameId : Lsc.Ident) :
        @Lsc.ContractDSL.resolveErr $sId $eId $errIdT _ _ $nameId =
          $resolveErrRef $nameId := rfl)

def mkDslBuildEventLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let buildEventRef := mkIdent (eventName ++ `buildEvent)
  let nameId := mkIdent `name
  let valsId := mkIdent `vals
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident ($nameId : Lsc.Ident) ($valsId : List (Sigma Lsc.Val)) :
        @Lsc.ContractDSL.buildEvent $sId $eId $errIdT _ _ $nameId $valsId =
          $buildEventRef $nameId $valsId := rfl)

/-- One `@[simp]` `rfl` lemma per matched `ArithError` constructor, e.g.
`@ContractErrors.arith Err _ ArithError.Overflow = Err.Overflow`, generalizing
what used to be one hand-written `counterError_arith_overflow`-style lemma
per contract to every arith case the error type actually maps (found via the
same name-matching `deriving ContractError` already performs). -/
def mkErrorArithLemma (lemmaName errName : Name) (ctorStr : String) : TermElabM Command := do
  let errId := mkIdent errName
  let aeCtorId := mkIdent (`Lsc.ArithError ++ Name.mkSimple ctorStr)
  let errCtorId := mkIdent (errName ++ Name.mkSimple ctorStr)
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident :
        @Lsc.ContractErrors.arith $errId _ $aeCtorId = $errCtorId := rfl)

/-- Internal assembly step invoked by `derive_contract` (`Lang/Syntax.lean`): wires
`deriving`-generated `getField`/`setField`/`resolveError`/`buildEvent` into a
`ContractDSL` instance and populates the namespace registries `currContractTypes`/
`currContractStorageName` consult when elaborating buffered `tx`/`view` bodies. Not a
public author-facing command. -/
def elabDeriveContractDsl (storageId errId eventId : Lean.Ident) : CommandElabM Unit := do
  -- Resolve each identifier to its fully-qualified `Name` first, then build
  -- the `S.getField`/etc. references as single fully-qualified idents —
  -- splicing `$storageId.getField` directly would parse as one antiquoted
  -- dotted name (wrong), and `($storageId).getField` as a value-level field
  -- projection on the *type* `$storageId` denotes (also wrong, since
  -- `TStorage` is a `Type`, not a structure instance); neither is what we
  -- want, which is plain namespaced-constant reference to `TStorage.getField`.
  let storageName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo storageId
  let errName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo errId
  let eventName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo eventId
  let getFieldRef := mkIdent (storageName ++ `getField)
  let setFieldRef := mkIdent (storageName ++ `setField)
  let getMapFieldRef := mkIdent (storageName ++ `getMapField)
  let setMapFieldRef := mkIdent (storageName ++ `setMapField)
  let resolveErrRef := mkIdent (errName ++ `resolveError)
  let buildEventRef := mkIdent (eventName ++ `buildEvent)
  -- Record this contract's `(errName, eventName)` under the current namespace, so the
  -- `revert`/`require ... else revert`/`emitEvent` real-constructor sugar (below) can find
  -- them later when this contract's function bodies are elaborated.
  let currNs ← getCurrNamespace
  modifyEnv fun env => contractTypesExt.modifyState env (·.insert currNs (errName, eventName))
  modifyEnv fun env => contractStorageExt.modifyState env (·.insert currNs storageName)
  Lean.Elab.Command.elabCommand (← `(command|
    @[reducible] instance : Lsc.ContractDSL $storageId $eventId $errId where
      getField   := $getFieldRef
      setField   := $setFieldRef
      getMapField := $getMapFieldRef
      setMapField := $setMapFieldRef
      resolveErr := $resolveErrRef
      buildEvent := $buildEventRef))
  -- Mark the three generated defs `@[simp]` (their own `match` equations
  -- then fire under plain `simp`), and emit the four DSL-projection `rfl`
  -- lemmas relating the `ContractDSL` class projections back to them.
  Lean.Elab.Command.elabCommand (← `(command|
    attribute [simp] $getFieldRef:ident $setFieldRef:ident $resolveErrRef:ident $buildEventRef:ident))
  let baseStr := storageId.getId.toString
  let getFieldLemma ← liftTermElabM <|
    mkDslGetFieldLemma (Name.mkSimple (baseStr ++ "Dsl_getField")) storageName errName eventName
  let setFieldLemma ← liftTermElabM <|
    mkDslSetFieldLemma (Name.mkSimple (baseStr ++ "Dsl_setField")) storageName errName eventName
  let getMapFieldLemma ← liftTermElabM <|
    mkDslGetMapFieldLemma (Name.mkSimple (baseStr ++ "Dsl_getMapField")) storageName errName eventName
  let setMapFieldLemma ← liftTermElabM <|
    mkDslSetMapFieldLemma (Name.mkSimple (baseStr ++ "Dsl_setMapField")) storageName errName eventName
  let resolveErrLemma ← liftTermElabM <|
    mkDslResolveErrLemma (Name.mkSimple (baseStr ++ "Dsl_resolveErr")) storageName errName eventName
  let buildEventLemma ← liftTermElabM <|
    mkDslBuildEventLemma (Name.mkSimple (baseStr ++ "Dsl_buildEvent")) storageName errName eventName
  atRootNamespace do
    elabCommand getFieldLemma
    elabCommand setFieldLemma
    elabCommand getMapFieldLemma
    elabCommand setMapFieldLemma
    elabCommand resolveErrLemma
    elabCommand buildEventLemma
  -- Emit one `@[simp]` arith-mapping lemma per `ArithError` constructor name
  -- that `errId`'s constructors actually shadow (mirrors the name-matching
  -- `deriving ContractError`'s handler already performs for the
  -- `ContractErrors.arith` field).
  let errIndVal ← liftTermElabM <| getConstInfoInduct errName
  let errCtorStrs := errIndVal.ctors.toArray.map (·.getString!)
  for an in arithErrorCtorNames do
    if errCtorStrs.contains an then
      let lemmaName := Name.mkSimple (baseStr ++ "Error_arith_" ++ an)
      let cmd ← liftTermElabM <| mkErrorArithLemma lemmaName errName an
      atRootNamespace <| elabCommand cmd

/-! ## `ContractDef` + compile outputs from introspection

`derive_contract`'s `elabContractDefBody` step (in `Lang/Syntax.lean`) re-derives the pieces of
`ContractDef` that are already fully determined by

`Storage`/`Err`/`Event`'s declared fields/constructors (`storage`/`errors`/
`events`) via the same introspection `deriving ContractStorage`/
`ContractError`/`ContractEvent` already perform, wraps each function in
`functions` (a plain `List (String × Stmt)` — every contract function, now a
bare `def foo : TxM Unit := ...`, coerces to `Stmt` automatically, see
`Lang/TxM.lean`) into a `FunctionDef`, and emits, at the call site's ambient
namespace: `contractDef`, `config`, `bytecodeHex`, `deployHex` — replacing
the hand-written `counterFn`/`counterDef`/`compileConfig`/
`counterBytecodeHex`/`counterDeployHex` block a contract used to need.

All three trailing groups are **optional**, consumed left-to-right
(`functions`, then `topic0`, then `ctor` — see the elaborator below for why
this is unambiguous), each falling back to an auto-derived default when
omitted so the common case needs none of them:
* `functions` defaults to every `tx name { .. }` self-registered under this
  namespace so far (`Lsc.Deriving.contractFnsExt`), in declaration order —
  every `tx` is already an external function today, so this is never lossy.
* `topic0` defaults to a real Keccak256 computation
  (`Lsc.computeEventTopic0`) over each event's ABI signature, derived from
  the same `eventEntries` used for `ContractDef.events` — no more
  hand-maintained topic tables (and no more non-cryptographic
  `name.hash.toNat` stand-ins for events without a hand-pinned topic).
* `ctor` defaults to `none`, *unless* `Storage` declares an `owner : Address`
  field, in which case it defaults to the standard "set `owner` to the
  deployer (`msg.sender`) at construction time" `Stmt` — the exact one-liner
  `Counter`'s hand-written `owner := msg.sender` constructor used to spell
  out by hand.

Any of the three can still be given explicitly to override the default
(e.g. a contract with an unrelated `owner`-named field that isn't meant to
be deploy-initialized, or an event needing a hand-pinned topic).

Storage field *default values* (the third component of each
`ContractDef.storage` entry) are always emitted as `none`: they are only
consulted by `Lang/Checks.lean`'s arith-error-coverage check today, never
actually written to storage at deploy time (only `constructor` is), so
there is no real "default init value" for this command to recover from a
structure's Lean-level field defaults (which serve a different purpose —
e.g. `Inhabited`/`{}`-literal ergonomics — and aren't reliably safe to
reinterpret as on-chain initial storage values). A contract that does need
a non-`owner` field pre-set at deploy time should pass an explicit
`ctor` override.

This command's actual `elab` lives in `Lang/Syntax.lean`, not here: it needs to flush any
buffered `tx { .. }` bodies (`Lsc.Deriving.contractTxSyntaxExt`) into real `def`s before it can
read `contractFnsExt`'s now-complete function list, and flushing requires `elabStmtList`, which
lives in `Syntax.lean` (this file is imported *by* `Syntax.lean`, not the reverse, so it can't
call back into it). -/

/-! ## `currContractTypes`/`currContractStorageName`/`elabErrorCtorName`

These helpers used to back a bare-do-notation `revert`/`require ... else revert`/`emit`
term-level sugar declared at the very bottom of this file; that sugar was removed once
`Lang/Syntax.lean`'s `tx { ... }` grammar took over as the contract-author-facing surface (it
calls these same helpers itself for its `revert Ctor();`/`require(cond) else revert Ctor();`/
`emit Ctor(arg);` statement forms). The helpers/registries stay, only the old sugar `elab`s are
gone. -/

/-- Look up the current namespace's `(errName, eventName)`, registered by `derive_contract`. -/
def currContractTypes : TermElabM (Name × Name) := do
  let ns ← getCurrNamespace
  let some tys := (contractTypesExt.getState (← getEnv)).find? ns
    | throwError "no `derive_contract` found for namespace `{ns}` — declare the contract's \
      storage/error/event types and call `derive_contract` before using `revert`/`require \
      ... else revert`/`emit`"
  return tys

/-- Look up the current namespace's storage `structure` name, registered by
`derive_contract`. Used by `Lang/Syntax.lean`'s `σ.field` resolution. -/
def currContractStorageName : TermElabM Name := do
  let ns ← getCurrNamespace
  let some storageName := (contractStorageExt.getState (← getEnv)).find? ns
    | throwError "no `derive_contract` found for namespace `{ns}` — declare the contract's \
      storage/error/event types and call `derive_contract` before using `tx`"
  return storageName

/-- Elaborate `e` against `errName`, returning the short name of the constructor it resolves
to (or a clear error if `e` isn't a constructor application of `errName` at all). -/
def elabErrorCtorName (e : Term) (errName : Name) : TermElabM String := do
  let errTy ← mkConstWithFreshMVarLevels errName
  let errVal ← elabTermEnsuringType e (some errTy)
  let errValR ← whnf errVal
  let some ctorName := errValR.getAppFn.constName?
    | throwError "expected a constructor of `{errName}`, got `{errValR}`"
  let ctorInfo ← getConstInfoCtor ctorName
  unless ctorInfo.induct == errName do
    throwError "`{ctorName}` is not a constructor of `{errName}`"
  return ctorName.componentsRev.head!.toString

end Lsc.Deriving

-- The old bare-do-notation `revert $e`/`require $c else revert $e`/`emit $c $args,*` term-level
-- sugar elaborators that used to live here (building on `currContractTypes`/
-- `elabErrorCtorName`/`getCtorFieldKind` above) were removed: `Lang/Syntax.lean`'s `tx { ... }`
-- grammar now provides the real-constructor `revert Ctor();`/`require(cond) else revert Ctor();`/
-- `emit Ctor();`/`emit Ctor(arg);` statement forms directly, calling `currContractTypes`/
-- `elabErrorCtorName`/`getCtorFieldKind` itself. Those functions/registries (and the three
-- `deriving` handlers/`elabDeriveContractDsl`/`derive_contract` above) all stay.
