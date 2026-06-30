import LscV2.Lang.Syntax
import LscV2.Lang.ContractGen

/-!
  `contract … where` elaborator — parsing half.

  This file imports `LscV2.Lang.Syntax` (which registers the `$.field` lsc
  token), so quasiquote templates with `$var` are broken here.  We therefore
  do only *parsing* via raw Syntax navigation, then hand everything off to
  `LscV2.Lang.ContractGen.generate`, which lives in a file that does NOT
  import Syntax and therefore has working `$var` antiquotations.
-/

open Lean Elab Command LscV2.DSL LscV2.ContractElab

namespace LscV2.ContractElab

-- ── Raw helpers ───────────────────────────────────────────────────────────

private partial def unwrapSyntax (stx : Syntax) : Syntax :=
  if stx.getNumArgs == 1 then unwrapSyntax stx[0]! else stx

-- Convert a raw lsc_expr Syntax node to a Lean term Syntax node.
-- Produces a `Lean.mkIdent` or `mkNumLit`; no quasiquotes used.
private def lscExprRawToSyntax (raw : Syntax) : MacroM Syntax := do
  let leaf    := unwrapSyntax raw
  let atomStr := match leaf with | .atom _ s => s | _ => ""
  match atomStr with
  | "false" => return Lean.mkIdent `Bool.false
  | "true"  => return Lean.mkIdent `Bool.true
  | s =>
    match s.toNat? with
    | some _ => return Lean.Syntax.mkNumLit s
    | none   =>
      let kind := leaf.getKind.toString
      if kind.endsWith "lsc_false" then return Lean.mkIdent `Bool.false
      if kind.endsWith "lsc_true"  then return Lean.mkIdent `Bool.true
      Macro.throwError s!"unsupported lsc default: {raw}"

-- Parse one lsc_field_decl.
-- Layout: [0] ident  [1] ":"  [2] lsc_ty  [3] optGroup
-- optGroup when present: [0] ":="  [1] lsc_expr
private def parseField
    (fd : TSyntax `lsc_field_decl)
    : CommandElabM FieldInfo := do
  let raw   := fd.raw
  let fname := raw[0]!.getId.toString
  let k     ← liftMacroM (lscTyToFieldKind ⟨raw[2]!⟩)
  let opt   := raw[3]!
  if opt.getNumArgs > 0 then
    let defSyn ← liftMacroM (lscExprRawToSyntax opt[1]!)
    return { name := fname, kind := k, default := some (⟨defSyn⟩ : TSyntax `term) }
  else
    return { name := fname, kind := k, default := none }

-- ── Elaborator ────────────────────────────────────────────────────────────

elab "contract" name:ident "where" body:lsc_contract_body : command =>
  match body with
  | `(lsc_contract_body|
        storage: $fieldDecls:lsc_field_decl*
        errors:  $errorDecls:lsc_error_decl*
        events:  $eventDecls:lsc_event_decl*
        $funcDecls:lsc_func_decl*) => do

    let base := name.getId

    -- ── Parse storage fields ─────────────────────────────────────────────
    let mut fieldMap : FieldMap := #[]
    let mut fields   : Array FieldInfo := #[]
    for fd in fieldDecls do
      let fi ← parseField fd
      fieldMap := fieldMap.push (fi.name, fi.kind)
      fields   := fields.push fi

    -- ── Parse errors ─────────────────────────────────────────────────────
    -- (renamed errList to avoid the `errors` lsc keyword conflict)
    let mut errList : Array String := #[]
    for ed in errorDecls do
      match ed with
      | `(lsc_error_decl| | $e:ident) => errList := errList.push e.getId.toString
      | _ => throwError "invalid error declaration"

    -- ── Parse events ─────────────────────────────────────────────────────
    -- (renamed evList to avoid the `events` lsc keyword conflict)
    let mut evList : Array EventInfo := #[]
    for evd in eventDecls do
      match evd with
      | `(lsc_event_decl| | $e:ident) =>
        evList := evList.push { name := e.getId.toString, params := #[] }
      | `(lsc_event_decl| | $e:ident ($p:ident : $ty:lsc_ty)) => do
        let k ← liftMacroM (lscTyToFieldKind ty)
        evList := evList.push { name := e.getId.toString, params := #[(p.getId.toString, k)] }
      | _ => throwError "invalid event declaration"

    -- ── Parse functions ───────────────────────────────────────────────────
    let mut funcList : Array FuncInfo := #[]
    for fd in funcDecls do
      match fd with
      | `(lsc_func_decl| def $fname:ident : Tx := do $body:lsc_stmt) => do
        let bodyTerm ← liftMacroM (LscV2.expandLscStmtWith fieldMap body)
        funcList := funcList.push { name := fname.getId.toString, body := bodyTerm }
      | _ => throwError "invalid function declaration"

    -- ── Hand off to the code generator ───────────────────────────────────
    -- Names must be SIMPLE (e.g. `CounterStorage`), not qualified (`Counter.CounterStorage`),
    -- because they are emitted INSIDE `namespace $name`.
    let baseName := base.toString
    let d : ContractData := {
      storageName := Name.mkSimple (baseName ++ "Storage")
      errorName   := Name.mkSimple (baseName ++ "Error")
      eventName   := Name.mkSimple (baseName ++ "Event")
      mName       := Name.mkSimple (baseName ++ "M")
      fields
      errorNames  := errList
      evts        := evList
      funcs       := funcList
    }
    generate name d

  | _ => throwError "invalid contract body"

end LscV2.ContractElab
