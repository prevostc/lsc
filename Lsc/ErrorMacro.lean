import Lean
import Lsc.Attribute
import Lsc.Error

open Lean Elab Command

declare_syntax_cat errorCtor

syntax "|" ident : errorCtor
syntax "|" ident " : " term : errorCtor

/-- `error! E where | Ctor1 | Ctor2 : T → E ...`
    Generates:
    - `inductive E` with the given constructors + `deriving DecidableEq, Repr`
    - `instance : LscError E where arith := .arith`
    - `attribute [lsc.error] E`
    The `| arith : ArithError → E` constructor **must** be present; the macro
    errors at elaboration time if it is missing. -/
syntax "error!" ident " where" ppLine many1(errorCtor) : command

elab_rules : command
  | `(error! $errName:ident where $ctorSyns:errorCtor*) => do
    -- Check that an arith constructor is declared.
    let hasArith := ctorSyns.any fun stx =>
      match stx with
      | `(errorCtor| | arith : $_) => true
      | _ => false
    unless hasArith do
      throwError "error!: '{errName.getId}' must include '| arith : ArithError → {errName.getId}'"

    -- Build constructor decls.
    let ctorDecls ← ctorSyns.mapM fun stx =>
      match stx with
      | `(errorCtor| | $n:ident : $ty:term) =>
          `(Lean.Parser.Command.ctor| | $n:ident : $ty:term)
      | `(errorCtor| | $n:ident) =>
          `(Lean.Parser.Command.ctor| | $n:ident)
      | _ => throwError "invalid error! constructor"

    -- Emit the inductive.
    elabCommand (← `(inductive $errName:ident where
        $[$ctorDecls]*
      deriving DecidableEq, Repr))

    -- Emit the LscError instance.
    elabCommand (← `(instance : Lsc.LscError $errName:ident where arith := .arith))

    -- Tag with [lsc.error].
    elabCommand (← `(attribute [lsc.error] $errName:ident))
