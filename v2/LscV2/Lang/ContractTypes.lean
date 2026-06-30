import Lean

/-!
  Shared types for the `contract … where` elaborator.

  This file MUST NOT import `LscV2.Lang.Syntax` (which registers lsc tokens
  like `$.`, and keywords `Bool`, `false`, `errors`, `events`, `storage`).
  Keeping it clean allows `ContractGen.lean` to import it and still use
  standard Lean quasiquotes without conflicts.
-/

open Lean

namespace LscV2.DSL

/-- Mirrors the storage field types of the lsc DSL. -/
inductive FieldKind
  | wei
  | bool
  | address
  | uint256

instance : Inhabited FieldKind := ⟨.wei⟩

abbrev FieldMap := Array (String × FieldKind)

end LscV2.DSL

namespace LscV2.ContractElab

open LscV2.DSL

structure FieldInfo where
  name    : String
  kind    : FieldKind
  /-- Explicit Lean default term, if the user wrote `:= expr`. -/
  default : Option (TSyntax `term)

instance : Inhabited FieldInfo where
  default := { name := "", kind := .wei, default := none }

structure EventInfo where
  name   : String
  params : Array (String × FieldKind)

instance : Inhabited EventInfo where
  default := { name := "", params := #[] }

structure FuncInfo where
  name : String
  body : TSyntax `term   -- expanded Stmt term

instance : Inhabited FuncInfo where
  default := { name := "", body := ⟨.missing⟩ }

structure ContractData where
  storageName : Name          -- e.g. `CounterStorage
  errorName   : Name
  eventName   : Name
  mName       : Name
  fields      : Array FieldInfo
  errorNames  : Array String  -- named "errorNames" to avoid lsc keyword conflict
  evts        : Array EventInfo  -- named "evts" to avoid lsc `events` keyword conflict
  funcs       : Array FuncInfo

end LscV2.ContractElab
