import LscV2.Core.ContractM
import LscV2.Lang.Eval
import LscV2.Lang.ContractTypes
import Lean

/-!
  Code-generation half of the `contract … where` elaborator.

  IMPORTANT: Do NOT import `LscV2.Lang.Syntax` here.  That file registers
  lsc tokens (`$.`, `Bool`, `false`, `errors`, `events`, `storage`, …) into
  Lean's global tokeniser, breaking the quasiquotes in this file.

  Lean 4.30 quirks worked around here:
  * `structSimpleBinder` — not quotable; built via `Syntax.node`.
  * `matchAlt`/`matchAlts` — not quotable; built via `Syntax.node`.
  * `match disc with $alts` — splicing matchAlts into a quasiquote does not
    work; instead we build the whole match as a `Syntax.node` and splice it
    as a term (`$matchExpr`).
  * `Lean.Parser.Command.ctor| | $id:ident` — works only in `MacroM`;
    use `liftMacroM`.
-/

open Lean Elab Command
open LscV2.DSL
open LscV2.ContractElab

namespace LscV2.ContractElab

-- ── Per-kind Lean syntax helpers ──────────────────────────────────────────

private def genLeanType (k : FieldKind) : MacroM (TSyntax `term) :=
  match k with
  | .wei     => `(LscV2.Wei)
  | .bool    => return mkIdent `Bool
  | .address => `(LscV2.Address)
  | .uint256 => `(LscV2.UInt256)

private def genDefault (k : FieldKind) : MacroM (TSyntax `term) :=
  match k with
  | .wei     => `(LscV2.Wei.mkNat 0)
  | .bool    => return mkIdent `Bool.false
  | .address => `(0)
  | .uint256 => `(0)

private def genTyConst (k : FieldKind) : MacroM (TSyntax `term) :=
  match k with
  | .wei     => `(LscV2.Ty.wei)
  | .bool    => `(LscV2.Ty.bool)
  | .address => `(LscV2.Ty.address)
  | .uint256 => `(LscV2.Ty.uint256)

-- ── Raw struct-field builder ──────────────────────────────────────────────

private def emptyDeclMods : Syntax :=
  Lean.Syntax.node .none `Lean.Parser.Command.declModifiers
    (Array.replicate 7 (Lean.Syntax.node .none `null #[]))

/-- Build a `structSimpleBinder` Syntax node: `name : ty := defVal`. -/
private def mkStructSimpleBinder
    (nameId : TSyntax `ident)
    (ty     : TSyntax `term)
    (defVal : Option (TSyntax `term))
    : Syntax :=
  let typeSpec :=
    Lean.Syntax.node .none `Term.typeSpec
      #[Lean.Syntax.atom .none ":", ty]
  let optSig :=
    Lean.Syntax.node .none `Lean.Parser.Command.optDeclSig
      #[Lean.Syntax.node .none `null #[],
        Lean.Syntax.node .none `null #[typeSpec]]
  let optDef := match defVal with
    | none   => Lean.Syntax.node .none `null #[]
    | some d =>
      Lean.Syntax.node .none `null
        #[Lean.Syntax.node .none `Term.binderDefault
            #[Lean.Syntax.atom .none ":=", d]]
  Lean.Syntax.node .none `Lean.Parser.Command.structSimpleBinder
    #[emptyDeclMods, nameId, optSig, optDef]

-- ── Raw match-expression builder ──────────────────────────────────────────

/-- Build one match arm: `| pats => body`. -/
private def mkMatchArm (pats : Array Syntax) (body : Syntax) : Syntax :=
  let patsWithCommas := pats.foldl (fun (acc : Array Syntax) p =>
    if acc.isEmpty then acc.push p
    else acc.push (Lean.Syntax.atom .none ",") |>.push p) #[]
  Lean.Syntax.node .none `Lean.Parser.Term.matchAlt
    #[Lean.Syntax.atom .none "|",
      Lean.Syntax.node .none `null
        #[Lean.Syntax.node .none `null patsWithCommas],
      Lean.Syntax.atom .none "=>",
      body]

/-- Build `match discr1, discr2, … with arm1 arm2 …` as a `term` Syntax. -/
private def mkMatchExpr (discrs : Array Syntax) (arms : Array Syntax) : TSyntax `term :=
  let discrsWithComma := discrs.foldl (fun (acc : Array Syntax) d =>
    if acc.isEmpty then
      acc.push (Lean.Syntax.node .none `Lean.Parser.Term.matchDiscr
        #[Lean.Syntax.node .none `null #[], d])
    else
      (acc.push (Lean.Syntax.atom .none ","))
      |>.push (Lean.Syntax.node .none `Lean.Parser.Term.matchDiscr
        #[Lean.Syntax.node .none `null #[], d])) #[]
  let alts := Lean.Syntax.node .none `Lean.Parser.Term.matchAlts
    #[Lean.Syntax.node .none `null arms]
  ⟨Lean.Syntax.node .none `Lean.Parser.Term.match
    #[Lean.Syntax.atom .none "match",
      Lean.Syntax.node .none `null #[],
      Lean.Syntax.node .none `null #[],
      Lean.Syntax.node .none `null discrsWithComma,
      Lean.Syntax.atom .none "with",
      alts]⟩

-- ── Code generator ────────────────────────────────────────────────────────

/-- Emit all Lean declarations for a parsed contract. -/
def generate (nameId : TSyntax `ident) (d : ContractData) : CommandElabM Unit := do
  let storageName := mkIdent d.storageName
  let errorName   := mkIdent d.errorName
  let eventName   := mkIdent d.eventName
  let mName       := mkIdent d.mName

  elabCommand (← `(command| namespace $nameId))

  -- ── 1. Storage structure ──────────────────────────────────────────────
  let structFields ← d.fields.mapM fun fi => do
    let fnameId := mkIdent (Name.mkSimple fi.name)
    let ty      ← liftMacroM (genLeanType fi.kind)
    let defVal  ← match fi.default with
      | some dv => pure (some dv)
      | none    => liftMacroM (some <$> genDefault fi.kind)
    return mkStructSimpleBinder fnameId ty defVal
  let structFieldsNode :=
    Lean.Syntax.node .none `Lean.Parser.Command.structFields
      #[Lean.Syntax.node .none `null structFields]
  let structCmd :=
    Lean.Syntax.node .none `Lean.Parser.Command.declaration
      #[emptyDeclMods,
        Lean.Syntax.node .none `Lean.Parser.Command.structure
          #[Lean.Syntax.node .none `Lean.Parser.Command.structureTk
              #[Lean.Syntax.atom .none "structure"],
            Lean.Syntax.node .none `Lean.Parser.Command.declId
              #[storageName, Lean.Syntax.node .none `null #[]],
            Lean.Syntax.node .none `Lean.Parser.Command.optDeclSig
              #[Lean.Syntax.node .none `null #[],
                Lean.Syntax.node .none `null #[]],
            Lean.Syntax.node .none `null #[],
            Lean.Syntax.node .none `null
              #[Lean.Syntax.atom .none "where",
                Lean.Syntax.node .none `null #[],
                structFieldsNode],
            Lean.Syntax.node .none `Lean.Parser.Command.optDeriving
              #[Lean.Syntax.atom .none "deriving",
                Lean.Syntax.node .none `null
                  #[Lean.Syntax.node .none `Lean.Parser.Command.derivingClass
                      #[Lean.Syntax.node .none `null #[], mkIdent `Repr]]]]]
  elabCommand (⟨structCmd⟩ : TSyntax `command)
  elabCommand (← `(command|
    instance : Inhabited $storageName where
      default := {}))

  -- ── 2. Error inductive ────────────────────────────────────────────────
  let errCtors ← d.errorNames.mapM fun ename => do
    let eId := mkIdent (Name.mkSimple ename)
    liftMacroM `(Lean.Parser.Command.ctor| | $eId:ident)
  elabCommand (← `(command|
    inductive $errorName where
      $[$errCtors]*
    deriving Repr, DecidableEq))
  let firstErrId := mkIdent (Name.mkSimple d.errorNames[0]!)
  elabCommand (← `(command|
    instance : Inhabited $errorName where
      default := .$firstErrId))
  let overflowId  := mkIdent (Name.mkSimple (if d.errorNames.contains "Overflow" then "Overflow" else d.errorNames[0]!))
  let frameworkId := mkIdent (Name.mkSimple d.errorNames[0]!)
  elabCommand (← `(command|
    instance : LscV2.ContractErrors $errorName where
      arith         := fun _ => .$overflowId
      fromFramework := fun _ => .$frameworkId))

  -- ── 3. Event inductive ────────────────────────────────────────────────
  let evCtors ← d.evts.mapM fun ev => do
    let eId := mkIdent (Name.mkSimple ev.name)
    if ev.params.isEmpty then
      liftMacroM `(Lean.Parser.Command.ctor| | $eId:ident)
    else
      let (pname, pkind) := ev.params[0]!
      let pId := mkIdent (Name.mkSimple pname)
      let pty ← liftMacroM (genLeanType pkind)
      liftMacroM `(Lean.Parser.Command.ctor| | $eId:ident ($pId:ident : $pty))
  elabCommand (← `(command|
    inductive $eventName where
      $[$evCtors]*
    deriving Repr, DecidableEq))
  -- Pick first no-param event for Inhabited; fall back to first event with a default arg
  let firstEvDefault ← do
    match d.evts.find? (·.params.isEmpty) with
    | some ev => liftMacroM do
        let eId := mkIdent (Name.mkSimple ev.name)
        `(.$eId)
    | none =>
        -- All events have params; use first with a type-specific default
        let ev := d.evts[0]!
        let (_, pkind) := ev.params[0]!
        let eId := mkIdent (Name.mkSimple ev.name)
        let defArg ← liftMacroM (genDefault pkind)
        liftMacroM `(.$eId $defArg)
  elabCommand (← `(command|
    instance : Inhabited $eventName where
      default := $firstEvDefault))

  -- ── 4. getField ──────────────────────────────────────────────────────
  -- All construction inside a SINGLE liftMacroM so binders (`t`, `field`, `s`)
  -- and match-discriminant references share the same hygienic scope.
  -- Wrap in try-catch to expose any silent elaboration errors.
  -- ── 4. getField ──────────────────────────────────────────────────────
  -- KEY: use mkIdent (raw, no scope) for the DEF NAME so the function is stored
  -- under `Counter.getField` (not a hygienic variant). The BODY idents (`t`,
  -- `field`, `s`) are created via `\`` INSIDE the same liftMacroM so binders
  -- and references share the same hygienic scope.
  let getFieldName := mkIdent `getField
  let getFieldCmd ← liftMacroM do
    let tId    ← `(t)
    let fieldId ← `(field)
    let sId    ← `(s)
    let gfArms ← d.fields.mapM fun fi => do
      let tyConst ← genTyConst fi.kind
      let fnameStr : Syntax := Lean.Syntax.mkStrLit fi.name
      let fId := mkIdent (Name.mkSimple fi.name)
      let sField ← `($sId.$fId)
      let body ← match fi.kind with
        | .wei     => `(some (LscV2.Val.wei  $sField))
        | .bool    => `(some (LscV2.Val.bool $sField))
        | .address => `(some (LscV2.Val.addr $sField))
        | .uint256 => `(some (LscV2.Val.u256 $sField))
      return mkMatchArm #[tyConst, fnameStr] body
    let wc : Syntax ← `(_)
    let gfDefault := mkMatchArm #[wc, wc] (mkIdent `none)
    let gfExpr := mkMatchExpr #[tId, fieldId] (gfArms.push gfDefault)
    `(command| def $getFieldName (t : LscV2.Ty) (field : String) (s : $storageName) : Option (LscV2.Val t) :=
        $gfExpr)
  elabCommand getFieldCmd

  -- ── 5. setField ──────────────────────────────────────────────────────
  let setFieldName := mkIdent `setField
  let setFieldCmd ← liftMacroM do
    let tId    ← `(t)
    let fieldId ← `(field)
    let vId    ← `(v)
    let sId    ← `(s)
    let sfArms ← d.fields.mapM fun fi => do
      let tyConst ← genTyConst fi.kind
      let fnameStr : Syntax := Lean.Syntax.mkStrLit fi.name
      let varName : Name := match fi.kind with
        | .wei => `w__ | .bool => `b__ | .address => `a__ | .uint256 => `n__
      let varId := mkIdent varName
      let valPat ← match fi.kind with
        | .wei     => `(LscV2.Val.wei  $varId)
        | .bool    => `(LscV2.Val.bool $varId)
        | .address => `(LscV2.Val.addr $varId)
        | .uint256 => `(LscV2.Val.u256 $varId)
      let fId := mkIdent (Name.mkSimple fi.name)
      let body ← `({ $sId with $fId:ident := $varId })
      return mkMatchArm #[tyConst, fnameStr, valPat] body
    let wc : Syntax ← `(_)
    let sfDefault := mkMatchArm #[wc, wc, wc] sId
    let sfExpr := mkMatchExpr #[tId, fieldId, vId] (sfArms.push sfDefault)
    `(command| def $setFieldName (t : LscV2.Ty) (field : String) (v : LscV2.Val t) (s : $storageName) : $storageName :=
        $sfExpr)
  elabCommand setFieldCmd

  -- ── 6. resolveError ──────────────────────────────────────────────────
  let resolveErrName := mkIdent `resolveError
  let resolveErrCmd ← liftMacroM do
    let nameId ← `(name)
    let reArms ← d.errorNames.mapM fun ename => do
      let eStr : Syntax := Lean.Syntax.mkStrLit ename
      let eId  := mkIdent (Name.mkSimple ename)
      let body ← `(some (.$eId : $errorName))
      return mkMatchArm #[eStr] body
    let wc : Syntax ← `(_)
    let reDefault := mkMatchArm #[wc] (mkIdent `none)
    let reExpr := mkMatchExpr #[nameId] (reArms.push reDefault)
    `(command| def $resolveErrName (name : String) : Option $errorName :=
        $reExpr)
  elabCommand resolveErrCmd

  -- ── 7. buildEvent ────────────────────────────────────────────────────
  let buildEventName := mkIdent `buildEvent
  let buildEventCmd ← liftMacroM do
    let nameId ← `(name)
    let valsId ← `(vals)
    let beArms ← d.evts.mapM fun ev => do
      let eStr : Syntax := Lean.Syntax.mkStrLit ev.name
      let eId   := mkIdent (Name.mkSimple ev.name)
      if ev.params.isEmpty then
        let emptyList ← `(([] : List (Sigma LscV2.Val)))
        let body      ← `(some (.$eId : $eventName))
        return mkMatchArm #[eStr, emptyList] body
      else
        let (pname, pkind) := ev.params[0]!
        let pId     := mkIdent (Name.mkSimple pname)
        let tyConst ← genTyConst pkind
        let valPat  ← match pkind with
          | .wei     => `(LscV2.Val.wei  $pId)
          | .bool    => `(LscV2.Val.bool $pId)
          | .address => `(LscV2.Val.addr $pId)
          | .uint256 => `(LscV2.Val.u256 $pId)
        let fullCtorId := mkIdent (Name.str d.eventName ev.name)
        let listPat ← `([⟨$tyConst, $valPat⟩])
        let body    ← `(some ($fullCtorId $pId))
        return mkMatchArm #[eStr, listPat] body
    let wc : Syntax ← `(_)
    let beDefault := mkMatchArm #[wc, wc] (mkIdent `none)
    let beExpr := mkMatchExpr #[nameId, valsId] (beArms.push beDefault)
    `(command| def $buildEventName (name : String) (vals : List (Sigma LscV2.Val)) : Option $eventName :=
        $beExpr)
  elabCommand buildEventCmd

  -- ── 8. ContractDSL instance ──────────────────────────────────────────
  -- Use raw mkIdent for the function references so they resolve to the plain-named
  -- definitions (not the hygienic `✝` variants).
  let gfRef  := mkIdent `getField
  let sfRef  := mkIdent `setField
  let reRef  := mkIdent `resolveError
  let beRef  := mkIdent `buildEvent
  elabCommand (← `(command|
    @[reducible] instance : LscV2.ContractDSL $storageName $eventName $errorName where
      getField   := $gfRef
      setField   := $sfRef
      resolveErr := $reRef
      buildEvent := $beRef))

  -- ── 9. ContractM abbreviation ─────────────────────────────────────────
  elabCommand (← `(command|
    abbrev $mName := LscV2.ContractM $storageName $eventName $errorName))

  -- ── 10. Function ASTs and ContractM defs ─────────────────────────────
  for fi in d.funcs do
    let fnameId := mkIdent (Name.mkSimple fi.name)
    let astId   := mkIdent (Name.mkSimple (fi.name ++ "Ast"))
    elabCommand (← `(command| def $astId : LscV2.Stmt := $(fi.body)))
    elabCommand (← `(command| def $fnameId : $mName Unit := LscV2.Stmt.eval $astId))

  elabCommand (← `(command| end $nameId))

end LscV2.ContractElab
