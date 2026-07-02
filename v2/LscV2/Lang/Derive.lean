import LscV2.Core.ContractM
import LscV2.Lang.AST
import LscV2.Lang.TxM
import LscV2.Compile.Bytecode.Contract
import Lean

/-!
# Custom `deriving` handlers for the storage/error/event glue

This is step 2 of the Lean-first DSL redesign (see the migration plan and
the "Resolved: `ContractError` derivation example" section of the plan
doc). It replaces `LscV2.Lang.ContractGen`'s storage/error/event/dispatch
codegen (which synthesized everything from a bespoke custom-syntax parse
tree, see `ContractGen.lean`'s header comment) with three real `deriving`
handlers attached directly to plain `structure`/`inductive` declarations,
plus one small `derive_contract_dsl` assembly command.

This file does **not** touch `ContractGen.lean`/`Contract.lean`/
`Syntax.lean` — those are deleted in a later migration step.

## True `deriving X` handlers (no command fallback needed)

Unlike the old `contract … where` macro (which had to hand-build raw
`Syntax.node` trees to dodge a tokeniser conflict with `Syntax.lean`'s
`lsc_*` categories), this file imports neither `Syntax.lean` nor
`Contract.lean`, so plain Lean quasiquotes (`` `(term| …) ``) work
perfectly normally here. Lean's `Lean.Elab.registerDerivingHandler` API
(see `Lean.Elab.Deriving.Basic`/`Lean.Elab.Deriving.BEq` for the upstream
pattern this file follows) only needs to be told the *names* of the
declarations `deriving Foo` was attached to — by the time the handler
runs, the `structure`/`inductive` is already fully elaborated and sitting
in the environment, so ordinary introspection (`getStructureFields`,
`getConstInfoInduct`, `getConstInfoCtor`) gives everything needed. So this
step uses **true `deriving ContractStorage` / `deriving ContractEvent` /
`deriving ContractError` syntax**, not a command-based fallback.

## The `Address`/`UInt256` ambiguity — resolved, not just worked around

`Address` and `UInt256` are both literally `abbrev`s for `Word := BitVec
256` (`Types.lean`), so a fully-`whnf`'d field type cannot distinguish
them. However, empirically (verified against this project's Lean 4.31
toolchain), a structure's field-projection *type*, as stored in the
`ConstantInfo` Lean adds to the environment when elaborating `structure …
where field : Address`, is **not** auto-unfolded through reducible
`abbrev`s — it remains the literal constant application `LscV2.Address`
(resp. `LscV2.UInt256`), distinct from `LscV2.Wei`/`Bool`/each other,
until something explicitly calls `whnf`/unfolds it. `fieldKindOfExpr`
below relies on exactly this and never calls `whnf`, so it can tell
`Address` and `UInt256` apart from the *unreduced* stored type alone.

The one real limitation this leaves: a field declared with some *other*
alias of `Word`/`BitVec 256` (not literally `LscV2.Address`/
`LscV2.UInt256`/`LscV2.Wei`/`Bool`), e.g. spelling the type out as
`BitVec 256` directly, is rejected with a clear "unsupported field type"
error at `deriving` time rather than silently miscategorized — this is
intentional and documented, not a silent foot-gun.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace LscV2.Deriving

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
grammar's `σ.field` resolution (`Lang/Syntax2.lean`) can find *which* structure to run
`getStructureFieldKinds` against without the contract author repeating it — the same
`derive_contract_dsl`-populated-registry pattern as `contractTypesExt` above, kept as a
separate extension (rather than widening `contractTypesExt`'s tuple) so existing
`currContractTypes` callers are unaffected. -/
initialize contractStorageExt : EnvExtension (NameMap Name) ←
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

/-- Storage-field type tag. See the module docstring for why/how
`Address` and `UInt256` are distinguishable here despite both being
`abbrev`s for the same underlying `Word`/`BitVec 256` type. -/
inductive FieldKind
  | wei | bool | address | uint256
  deriving Repr, DecidableEq

/-- Classify a (necessarily un-`whnf`'d) field-type `Expr` by its literal
head constant. Returns `none` for any type other than the four supported
ones (see module docstring). -/
def fieldKindOfExpr (e : Lean.Expr) : Option FieldKind :=
  if e.isConstOf ``LscV2.Wei then some .wei
  else if e.isConstOf ``Bool then some .bool
  else if e.isConstOf ``LscV2.Address then some .address
  else if e.isConstOf ``LscV2.UInt256 then some .uint256
  else none

def FieldKind.tyConst : FieldKind → TermElabM Term
  | .wei => `(LscV2.Ty.wei)
  | .bool => `(LscV2.Ty.bool)
  | .address => `(LscV2.Ty.address)
  | .uint256 => `(LscV2.Ty.uint256)

/-- Wrap a plain term as a `matchDiscr` for splicing into `match $[$discrs],* with …`. -/
def mkDiscr (t : Term) : TermElabM (TSyntax ``Lean.Parser.Term.matchDiscr) :=
  `(Lean.Parser.Term.matchDiscr| $t:term)

def FieldKind.valCtor : FieldKind → TermElabM Term
  | .wei => `(LscV2.Val.wei)
  | .bool => `(LscV2.Val.bool)
  | .address => `(LscV2.Val.addr)
  | .uint256 => `(LscV2.Val.u256)

/-- The *expression* (not value) Lean type carrying a field of this kind while a
`Stmt`/`Expr` AST fragment is being built — `Wei.Expr` for `.wei`, `CoreExpr <tyConst>`
otherwise. Used by the `σ.field`-generation below, so `σ.number : Wei.Expr` and
`σ.paused : CoreExpr Ty.bool` come out with exactly the same Lean types the hand-written
`wei σ.field`/`bool σ.field` notation family (`TxM.lean`) already produces. -/
def FieldKind.exprTypeStx : FieldKind → TermElabM Term
  | .wei => `(LscV2.Wei.Expr)
  | .bool => `(LscV2.CoreExpr LscV2.Ty.bool)
  | .address => `(LscV2.CoreExpr LscV2.Ty.address)
  | .uint256 => `(LscV2.CoreExpr LscV2.Ty.uint256)

/-- The default (i.e. only, since these are never written by contract authors — they're
generated) value of a `σ.field` constant: a fresh `storageGet` expression fragment
referencing `fieldStr`, identical in shape to what `wei σ.field`/`bool σ.field`/... build
today (`TxM.lean`'s `weiField`/`boolField`/`addrField`/`u256Field`). -/
def FieldKind.storageGetStx (k : FieldKind) (fieldStr : String) : TermElabM Term := do
  let fieldLit := quote fieldStr
  match k with
  | .wei => `(LscV2.Wei.Expr.storageGet $fieldLit)
  | .bool => `(LscV2.CoreExpr.storageGet LscV2.Ty.bool $fieldLit)
  | .address => `(LscV2.CoreExpr.storageGet LscV2.Ty.address $fieldLit)
  | .uint256 => `(LscV2.CoreExpr.storageGet LscV2.Ty.uint256 $fieldLit)

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
    match fieldKindOfExpr fieldTy with
    | some k => return (fname, k)
    | none =>
      throwError "deriving ContractStorage: field `{fname}` of `{structName}` has unsupported type `{fieldTy}` \
        — storage fields must be declared with exactly one of `Wei`/`Bool`/`Address`/`UInt256` written literally \
        (see `LscV2.Deriving`'s module docstring for why this can't be fully generic)"

def mkGetFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let getFieldName := mkIdent (structName ++ `getField)
  let tId := mkIdent `t
  let fieldId := mkIdent `field
  let sId := mkIdent `s
  let arms ← fields.mapM fun (fname, k) => do
    let tyConst ← k.tyConst
    let valCtor ← k.valCtor
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    let pats : Array Term := #[tyConst, fieldStr]
    `(matchAltExpr| | $[$pats],* => some ($valCtor $sId.$fId))
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => none)
  let alts := arms.push defaultArm
  let discrs ← #[tId, fieldId].mapM mkDiscr
  `(command| def $getFieldName ($tId : LscV2.Ty) ($fieldId : String) ($sId : $structId) : Option (LscV2.Val $tId) :=
      match $[$discrs],* with
      $alts:matchAlt*)

def mkSetFieldCmd (structName : Name) (fields : Array (Name × FieldKind)) : TermElabM Command := do
  let structId := mkIdent structName
  let setFieldName := mkIdent (structName ++ `setField)
  let tId := mkIdent `t
  let fieldId := mkIdent `field
  let vId := mkIdent `v
  let sId := mkIdent `s
  let arms ← fields.mapM fun (fname, k) => do
    let valCtor ← k.valCtor
    let tyConst ← k.tyConst
    let fId := mkIdent fname
    let fieldStr := quote fname.toString
    let varId ← `(x)
    let valPat ← `($valCtor $varId)
    let body ← `({ $sId with $fId:ident := $varId })
    let pats : Array Term := #[tyConst, fieldStr, valPat]
    `(matchAltExpr| | $[$pats],* => $body)
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => $sId)
  let alts := arms.push defaultArm
  let discrs ← #[tId, fieldId, vId].mapM mkDiscr
  `(command| def $setFieldName ($tId : LscV2.Ty) ($fieldId : String) ($vId : LscV2.Val $tId) ($sId : $structId) : $structId :=
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
  fields.mapM fun (fname, k) => do
    let sigmaFieldName := mkIdent (ns ++ `σ ++ fname)
    let tyStx ← k.exprTypeStx
    let valStx ← k.storageGetStx fname.toString
    `(command| @[simp] def $sigmaFieldName : $tyStx := $valStx)

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
  let sigmaCmds ← liftTermElabM <| mkSigmaFieldCmds structName fieldKinds
  atRootNamespace do
    elabCommand getCmd
    elabCommand setCmd
    for c in sigmaCmds do elabCommand c
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
    match fieldKindOfExpr ty with
    | some k => return some k
    | none =>
      throwError "deriving ContractEvent: constructor `{ctorName}`'s parameter has unsupported type `{ty}` \
        — event payloads must be `Wei`/`Bool`/`Address`/`UInt256`"

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
    match fieldKindOfExpr ty with
    | some k => return some (paramName, k)
    | none =>
      throwError "derive_contract_def: constructor `{ctorName}`'s parameter has unsupported type `{ty}` \
        — event payloads must be `Wei`/`Bool`/`Address`/`UInt256`"

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
      let emptyList ← `(([] : List (Sigma LscV2.Val)))
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
      let body ← `(some ($fullCtorId $varId))
      let pats : Array Term := #[nameStr, listPat]
      `(matchAltExpr| | $[$pats],* => $body)
  let wc ← `(_)
  let wcPats : Array Term := #[wc, wc]
  let defaultArm ← `(matchAltExpr| | $[$wcPats],* => none)
  let alts := arms.push defaultArm
  let discrs ← #[nameId, valsId].mapM mkDiscr
  `(command| def $buildEventName ($nameId : String) ($valsId : List (Sigma LscV2.Val)) : Option $evtId :=
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
* `instance : LscV2.ContractErrors Err` — `arith`/`fromFramework` arms are
  filled in by *name-matching* against `ArithError`
  (`Overflow`/`Underflow`/`DivisionByZero`) and `FrameworkError`
  (`Reentrant`/`Unauthorized`/`InvalidSelector`) constructors: a
  same-named constructor in `Err` maps directly; an unmatched case falls
  back to `ContractErrors.unreachableArith` (for `arith`) or the first
  matching-by-name framework constructor found, else the first declared
  `Err` constructor (for `fromFramework`) — mirroring exactly what
  `Counter.lean`'s hand-written instance already does today (it maps
  every `FrameworkError` case to one fixed fallback constructor).

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
def frameworkErrorCtorNames : Array String := #["Reentrant", "Unauthorized", "InvalidSelector"]

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
      -- Built as one fully-qualified identifier (not `LscV2.ArithError.$aeId`
      -- dot-syntax) since splicing an antiquotation after a literal dotted
      -- prefix parses as *field-projection* notation, which isn't valid in
      -- pattern position ("Invalid pattern").
      let fullPat := mkIdent (`LscV2.ArithError ++ Name.mkSimple an)
      let aeId := mkIdent (Name.mkSimple an)
      let body ← `(.$aeId)
      some <$> `(matchAltExpr| | $fullPat:term => $body)
    else
      pure none
  let aeWc := mkIdent `ae
  let fallbackBody ← `(LscV2.ContractErrors.unreachableArith $aeWc)
  let arithDefault ← `(matchAltExpr| | $aeWc => $fallbackBody)
  let arithAlts := arithArms.push arithDefault
  let arithDiscrs ← #[(aeWc : Term)].mapM mkDiscr
  let arithMatch ← `(fun $aeWc => match $[$arithDiscrs],* with $arithAlts:matchAlt*)
  -- `fromFramework`: every case maps to one fixed fallback constructor,
  -- same pattern as `Counter.lean`'s hand-written instance — preferring a
  -- same-named `Err` constructor for any `FrameworkError` case if one
  -- exists, else the first declared `Err` constructor.
  let matchedFramework := frameworkErrorCtorNames.filter ctorStrs.contains
  let fallbackCtorStr := matchedFramework[0]?.getD ctorStrs[0]!
  let fallbackCtorId := mkIdent (Name.mkSimple fallbackCtorStr)
  let feWc ← `(_fe)
  let fwBody ← `(.$fallbackCtorId)
  let fwMatch ← `(fun $feWc => $fwBody)
  `(command|
    instance : LscV2.ContractErrors $errId where
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

/-! ## `derive_contract_dsl` — final assembly command

One explicit line, `derive_contract_dsl FooStorage FooError FooEvent`,
wires the three derived pieces (found purely by the naming convention
documented above — `S.getField`/`S.setField`/`Err.resolveError`/
`E.buildEvent`, all reachable from `S`/`Err`/`E` via plain Lean
dot-notation since they're declared as `S.getField` etc.) plus the
`ContractErrors Err` instance (found by ordinary typeclass resolution —
no naming convention needed since it's anonymous) into the final
`ContractDSL` instance, matching `ContractGen.lean` step 8 /
`Counter.lean`'s hand-written instance. -/
/-! ### Auto-generated `@[simp]` DSL-projection lemmas

`Stmt.evalWith`'s simp set (`Lang/Eval.lean`) only unfolds as far as
`dsl.getField`/`dsl.setField`/`dsl.resolveErr`/`dsl.buildEvent` (the
`ContractDSL` *projections*); without lemmas relating those projections
back to the concrete derived defs, `simp` cannot see through the
(reducible but not `@[simp]`) `ContractDSL` instance `derive_contract_dsl`
assembles to actually evaluate a `getField`/`setField`/... call. Marking
the generated defs themselves `@[simp]` (so their own `match` equations
fire) plus relating the class projections to them via the four `rfl`
lemmas below is what previously had to be hand-written per-contract (see
e.g. `examples/counter/src/Counter.lean`'s history) — `derive_contract_dsl`
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
    @[simp] theorem $lemIdent:ident ($tId : LscV2.Ty) ($fId : LscV2.Ident) ($sVarId : $sId) :
        @LscV2.ContractDSL.getField $sId $eId $errIdT _ _ $tId $fId $sVarId =
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
        ($tId : LscV2.Ty) ($fId : LscV2.Ident) ($vId : LscV2.Val $tId) ($sVarId : $sId) :
        @LscV2.ContractDSL.setField $sId $eId $errIdT _ _ $tId $fId $vId $sVarId =
          $setFieldRef $tId $fId $vId $sVarId := rfl)

def mkDslResolveErrLemma (lemmaName storageName errName eventName : Name) : TermElabM Command := do
  let sId := mkIdent storageName
  let eId := mkIdent eventName
  let errIdT := mkIdent errName
  let resolveErrRef := mkIdent (errName ++ `resolveError)
  let nameId := mkIdent `name
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident ($nameId : LscV2.Ident) :
        @LscV2.ContractDSL.resolveErr $sId $eId $errIdT _ _ $nameId =
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
    @[simp] theorem $lemIdent:ident ($nameId : LscV2.Ident) ($valsId : List (Sigma LscV2.Val)) :
        @LscV2.ContractDSL.buildEvent $sId $eId $errIdT _ _ $nameId $valsId =
          $buildEventRef $nameId $valsId := rfl)

/-- One `@[simp]` `rfl` lemma per matched `ArithError` constructor, e.g.
`@ContractErrors.arith Err _ ArithError.Overflow = Err.Overflow`, generalizing
what used to be one hand-written `counterError_arith_overflow`-style lemma
per contract to every arith case the error type actually maps (found via the
same name-matching `deriving ContractError` already performs). -/
def mkErrorArithLemma (lemmaName errName : Name) (ctorStr : String) : TermElabM Command := do
  let errId := mkIdent errName
  let aeCtorId := mkIdent (`LscV2.ArithError ++ Name.mkSimple ctorStr)
  let errCtorId := mkIdent (errName ++ Name.mkSimple ctorStr)
  let lemIdent := mkIdent lemmaName
  `(command|
    @[simp] theorem $lemIdent:ident :
        @LscV2.ContractErrors.arith $errId _ $aeCtorId = $errCtorId := rfl)

end LscV2.Deriving

elab "derive_contract_dsl " storageId:ident errId:ident eventId:ident : command => do
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
  let resolveErrRef := mkIdent (errName ++ `resolveError)
  let buildEventRef := mkIdent (eventName ++ `buildEvent)
  -- Record this contract's `(errName, eventName)` under the current namespace, so the
  -- `revert`/`require ... else revert`/`emitEvent` real-constructor sugar (below) can find
  -- them later when this contract's function bodies are elaborated.
  let currNs ← getCurrNamespace
  modifyEnv fun env => LscV2.Deriving.contractTypesExt.modifyState env (·.insert currNs (errName, eventName))
  modifyEnv fun env => LscV2.Deriving.contractStorageExt.modifyState env (·.insert currNs storageName)
  Lean.Elab.Command.elabCommand (← `(command|
    @[reducible] instance : LscV2.ContractDSL $storageId $eventId $errId where
      getField   := $getFieldRef
      setField   := $setFieldRef
      resolveErr := $resolveErrRef
      buildEvent := $buildEventRef))
  -- Mark the three generated defs `@[simp]` (their own `match` equations
  -- then fire under plain `simp`), and emit the four DSL-projection `rfl`
  -- lemmas relating the `ContractDSL` class projections back to them.
  Lean.Elab.Command.elabCommand (← `(command|
    attribute [simp] $getFieldRef:ident $setFieldRef:ident $resolveErrRef:ident $buildEventRef:ident))
  let baseStr := storageId.getId.toString
  let getFieldLemma ← liftTermElabM <|
    LscV2.Deriving.mkDslGetFieldLemma (Name.mkSimple (baseStr ++ "Dsl_getField")) storageName errName eventName
  let setFieldLemma ← liftTermElabM <|
    LscV2.Deriving.mkDslSetFieldLemma (Name.mkSimple (baseStr ++ "Dsl_setField")) storageName errName eventName
  let resolveErrLemma ← liftTermElabM <|
    LscV2.Deriving.mkDslResolveErrLemma (Name.mkSimple (baseStr ++ "Dsl_resolveErr")) storageName errName eventName
  let buildEventLemma ← liftTermElabM <|
    LscV2.Deriving.mkDslBuildEventLemma (Name.mkSimple (baseStr ++ "Dsl_buildEvent")) storageName errName eventName
  LscV2.Deriving.atRootNamespace do
    elabCommand getFieldLemma
    elabCommand setFieldLemma
    elabCommand resolveErrLemma
    elabCommand buildEventLemma
  -- Emit one `@[simp]` arith-mapping lemma per `ArithError` constructor name
  -- that `errId`'s constructors actually shadow (mirrors the name-matching
  -- `deriving ContractError`'s handler already performs for the
  -- `ContractErrors.arith` field).
  let errIndVal ← liftTermElabM <| getConstInfoInduct errName
  let errCtorStrs := errIndVal.ctors.toArray.map (·.getString!)
  for an in LscV2.Deriving.arithErrorCtorNames do
    if errCtorStrs.contains an then
      let lemmaName := Name.mkSimple (baseStr ++ "Error_arith_" ++ an)
      let cmd ← liftTermElabM <| LscV2.Deriving.mkErrorArithLemma lemmaName errName an
      LscV2.Deriving.atRootNamespace <| elabCommand cmd

/-! ## `derive_contract_def` — `ContractDef` + compile outputs from introspection

`derive_contract_def "Name" Storage Err Event functions topic0 (some ctor)?`
re-derives the pieces of `ContractDef` that are already fully determined by
`Storage`/`Err`/`Event`'s declared fields/constructors (`storage`/`errors`/
`events`) via the same introspection `deriving ContractStorage`/
`ContractError`/`ContractEvent` already perform, wraps each function in
`functions` (a plain `List (String × Stmt)` — every contract function, now a
bare `def foo : TxM Unit := ...`, coerces to `Stmt` automatically, see
`Lang/TxM.lean`) into a `FunctionDef`, and emits, at the call site's ambient
namespace: `contractDef`, `config`, `bytecodeHex`, `deployHex` — replacing
the hand-written `counterFn`/`counterDef`/`compileConfig`/
`counterBytecodeHex`/`counterDeployHex` block a contract used to need.

Storage field *default values* (the third component of each
`ContractDef.storage` entry) are always emitted as `none`: they are only
consulted by `Lang/Checks.lean`'s arith-error-coverage check today, never
actually written to storage at deploy time (only `constructor` is), so
there is no real "default init value" for this command to recover from a
structure's Lean-level field defaults (which serve a different purpose —
e.g. `Inhabited`/`{}`-literal ergonomics — and aren't reliably safe to
reinterpret as on-chain initial storage values). A contract that does need
a non-zero field pre-set at deploy time should do it via `constructor`,
exactly like `Counter`'s `owner := msg.sender` already does. -/
elab "derive_contract_def " nameStrStx:str storageId:ident errId:ident eventId:ident
    "(" functions:term ")" "(" topic0:term ")" "(" ctor:term ")" : command => do
  let nameStr : Term := quote (nameStrStx.raw.isStrLit?.getD "")
  let storageName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo storageId
  let errName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo errId
  let eventName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo eventId
  -- `storage : List (Ident × Ty × Option ExprAny)`, derived from `storageId`'s fields.
  let storageFields ← liftTermElabM <| LscV2.Deriving.getStructureFieldKinds storageName
  let storageEntries ← storageFields.mapM fun (fname, k) => liftTermElabM do
    let tyConst ← k.tyConst
    let fnameStr := quote fname.toString
    `(($fnameStr, $tyConst, (none : Option LscV2.ExprAny)))
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
    match ← LscV2.Deriving.getCtorFieldNameKind ctorName with
    | none => `(($cStrLit, ([] : List (LscV2.Ident × LscV2.Ty))))
    | some (paramName, k) =>
      let tyConst ← k.tyConst
      let paramStrLit := quote paramName.toString
      `(($cStrLit, [($paramStrLit, $tyConst)]))
  let eventsTerm ← `([$eventEntries,*])
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
  Lean.Elab.Command.elabCommand (← `(command|
    def $contractDefId : LscV2.ContractDef where
      name := $nameStr
      storage := $storageTerm
      errors := $errorsTerm
      events := $eventsTerm
      functions :=
        ($functions : List (String × LscV2.Stmt)).map fun ($nId, $bodyId) =>
          { name := $nId, kind := LscV2.FunctionKind.external, params := [],
            retTy := LscV2.Ty.unit, body := $bodyId }
      interfaces := []
      constructor := $ctor))
  Lean.Elab.Command.elabCommand (← `(command|
    def $configId : LscV2.Compile.Config := LscV2.Compile.configFromContract $contractDefId $topic0))
  Lean.Elab.Command.elabCommand (← `(command|
    def $bytecodeHexId : String :=
      match LscV2.Compile.contractToBytecodeHex $contractDefId $topic0 with
      | .ok hex => hex
      | .error _ => ""))
  Lean.Elab.Command.elabCommand (← `(command|
    def $deployHexId : String :=
      match LscV2.Compile.deployToBytecodeHex $contractDefId $topic0 with
      | .ok hex => hex
      | .error _ => ""))

/-! ## `currContractTypes`/`currContractStorageName`/`elabErrorCtorName`

These helpers used to back a bare-do-notation `revert`/`require ... else revert`/`emit`
term-level sugar declared at the very bottom of this file; that sugar was removed once
`Lang/Syntax2.lean`'s `tx { ... }` grammar took over as the contract-author-facing surface (it
calls these same helpers itself for its `revert(Ctor);`/`require(cond, Ctor);`/`emit
Ctor(arg);` statement forms). The helpers/registries stay, only the old sugar `elab`s are
gone. -/

namespace LscV2.Deriving

/-- Look up the current namespace's `(errName, eventName)`, registered by `derive_contract_dsl`. -/
def currContractTypes : TermElabM (Name × Name) := do
  let ns ← getCurrNamespace
  let some tys := (contractTypesExt.getState (← getEnv)).find? ns
    | throwError "no `derive_contract_dsl` found for namespace `{ns}` — declare the contract's \
      storage/error/event types and call `derive_contract_dsl` before using `revert`/`require \
      ... else revert`/`emit`"
  return tys

/-- Look up the current namespace's storage `structure` name, registered by
`derive_contract_dsl`. Used by `Lang/Syntax2.lean`'s `σ.field` resolution. -/
def currContractStorageName : TermElabM Name := do
  let ns ← getCurrNamespace
  let some storageName := (contractStorageExt.getState (← getEnv)).find? ns
    | throwError "no `derive_contract_dsl` found for namespace `{ns}` — declare the contract's \
      storage/error/event types and call `derive_contract_dsl` before using `tx`"
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

end LscV2.Deriving

-- The old bare-do-notation `revert $e`/`require $c else revert $e`/`emit $c $args,*` term-level
-- sugar elaborators that used to live here (building on `currContractTypes`/
-- `elabErrorCtorName`/`getCtorFieldKind` above) were removed: `Lang/Syntax2.lean`'s `tx { ... }`
-- grammar now provides the real-constructor `revert(Ctor);`/`require(cond, Ctor);`/
-- `emit Ctor;`/`emit Ctor(arg);` statement forms directly, calling `currContractTypes`/
-- `elabErrorCtorName`/`getCtorFieldKind` itself. Those functions/registries (and the three
-- `deriving` handlers/`derive_contract_dsl`/`derive_contract_def` commands above) all stay.
