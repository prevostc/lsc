import Lean
import Lsc.Attribute
import Lsc.ContractState
import Lsc.ContractM

open Lean Elab Command Parser

declare_syntax_cat stateField

syntax ident " : " ident (ppSpace atomic("@public"))? : stateField

/-- `state! Mod where field : Type [@public] ...`
    Generates:
    - `Mod.State` structure with one field per declaration
    - `fields.x : Field Mod.State T` for each field
    - `ContractState Mod.State` instance (self / view / embed)
    - `@[lsc.external]` getter for each `@public` field (polymorphic in E) -/
syntax "state!" ident " where" ppLine many1(stateField) : command

/-- `contract! Mod E` — emits `abbrev Mod (α) := ContractM E Mod.State α`
    and a `@[simp] def Mod.view` alias for `ContractState.view`. -/
syntax "contract!" ident ident : command

private structure StField where
  name     : Name
  ty       : Name
  isPublic : Bool
  offset   : Nat
  deriving Inhabited

private def parseField (i : Nat) (stx : Syntax) : CommandElabM StField := do
  match stx with
  | `(stateField| $n:ident : $ty:ident @public) =>
    return { name := n.getId, ty := ty.getId, isPublic := true, offset := i }
  | `(stateField| $n:ident : $ty:ident) =>
    return { name := n.getId, ty := ty.getId, isPublic := false, offset := i }
  | _ => throwErrorAt stx "invalid state! field"

elab_rules : command
  | `(state! $mod:ident where $fieldSyns:stateField*) => do
    let stIdent := mkIdentFrom mod (mod.getId ++ `State)
    let flds ← fieldSyns.mapIdxM fun i stx => parseField i stx

    -- 1. State structure — use structExplicitBinder (parenthesised form) which is
    --    a valid quotation category in Lean 4.30
    let structFieldDecls ← flds.mapM fun (f : StField) => do
      let n := mkIdent f.name
      let t := mkIdent f.ty
      `(Lean.Parser.Command.structExplicitBinder| ($n:ident : $t:ident))
    elabCommand (← `(structure $stIdent:ident where $[$structFieldDecls]*))

    -- 2. Field witnesses — use Lean.mkIdent (non-hygienic) for the namespace and def
    --    names so that user code can reference `fields.number` etc. without hygiene issues.
    let fieldsNS : Ident := Lean.mkIdent `fields
    elabCommand (← `(namespace $fieldsNS))
    for f in flds do
      let n   : Ident := Lean.mkIdent f.name
      let t   : Ident := Lean.mkIdent f.ty
      let off := Syntax.mkNumLit (toString f.offset)
      elabCommand (← `(@[simp] def $n : Lsc.Field $stIdent $t := ⟨$off⟩))
    elabCommand (← `(end $fieldsNS))

    -- 3. Build view body (used in instance + @[simp] unfolding theorem)
    let viewArgs ← flds.mapM fun (f : StField) => do
      let off := Syntax.mkNumLit (toString f.offset)
      `(Lsc.FromWord.fromWord (Lsc.World.getStorage w Lsc.defaultSelf $off:num))
    let mkName := mkIdentFrom stIdent (stIdent.getId ++ `mk)
    let viewBody ← viewArgs.foldlM (init := ← `($mkName)) fun acc arg => `($acc $arg)

    -- 4. Build embed body (used in instance + @[simp] unfolding theorem)
    --    Use named accessor `Mod.State.field s` to avoid dot-projection antiquotation issues.
    let embedExpr ← flds.foldlM (init := ← `(w)) fun acc (f : StField) => do
      let off      := Syntax.mkNumLit (toString f.offset)
      let accessor := mkIdentFrom stIdent (stIdent.getId ++ f.name)
      `(Lsc.World.setStorage $acc Lsc.defaultSelf $off:num
          (Lsc.ToWord.toWord ($accessor s)))

    -- 5. ContractState instance (bodies inlined — no private intermediary defs)
    elabCommand (← `(instance : Lsc.ContractState $stIdent:ident where
      self  := Lsc.defaultSelf
      view  := fun w => $viewBody
      embed := fun s w => $embedExpr))

    -- 5b. @[simp] simp lemma for ContractState.self (needed by ContractM.get/set).
    let selfThmId : Ident := Lean.mkIdent (stIdent.getId ++ `self_eq)
    elabCommand (← `(@[simp] theorem $selfThmId :
        Lsc.ContractState.self (S := $stIdent:ident) = Lsc.defaultSelf := rfl))

    -- 5c. @[simp] unfolding theorems: bridge class projections → concrete bodies.
    --     Without these, `simp` can't reduce `ContractState.view` / `ContractState.embed`.
    let viewThmId  : Ident := Lean.mkIdent (stIdent.getId ++ `view_unfold)
    let embedThmId : Ident := Lean.mkIdent (stIdent.getId ++ `embed_unfold)
    elabCommand (← `(@[simp] theorem $viewThmId (w : Lsc.World) :
        Lsc.ContractState.view (S := $stIdent:ident) w = $viewBody := rfl))
    elabCommand (← `(@[simp] theorem $embedThmId (s : $stIdent:ident) (w : Lsc.World) :
        Lsc.ContractState.embed s w = $embedExpr := rfl))

    -- 6. @public — tag the Field constant with @[lsc.public] so the codegen
    --    walker can discover ABI entrypoints without generating extra functions.
    for f in flds do
      if f.isPublic then
        let fieldRef : Ident := Lean.mkIdent (`fields ++ f.name)
        elabCommand (← `(attribute [lsc.public] $fieldRef))

elab_rules : command
  | `(contract! $mod:ident $err:ident) => do
    let stIdent  := mkIdentFrom mod (mod.getId ++ `State)
    let modNS    : Ident := Lean.mkIdent mod.getId   -- non-hygienic: avoids view✝
    let viewId   : Ident := Lean.mkIdent `view
    elabCommand (← `(abbrev $mod:ident (α : Type) :=
      Lsc.ContractM $err:ident $stIdent:ident α))
    elabCommand (← `(namespace $modNS))
    elabCommand (← `(@[simp] def $viewId : Lsc.World → $stIdent:ident :=
      Lsc.ContractState.view))
    elabCommand (← `(end $modNS))
