import Lean

/-!
# `@[internal]`

Tag a non-entrypoint function of the contract (Solidity `internal`). Reify
delta-unfolds it (β with arguments, fuel-bounded) and continues on the body.
Recursive definitions are rejected at attribute application. Certificates are
kernel-checked `Core.denote (reify f) = f` (`rfl`, or `Tx` monad laws when a
helper sits mid-`do`).

`@[internal]` and `@[internal inline]` have the same codegen today (substitution
at call sites). A later slice compiles plain `@[internal]` as a real Yul
function call and keeps `inline` substituted. Do not use Lean's builtin
`@[inline]`.
-/

open Lean

namespace Lsc

/-- Parameter of `@[internal]`: today both kinds are inlined; `inline` will
stay substituted after plain `internal` becomes a real call. -/
inductive InternalKind where
  /-- Default: will become a real Yul function call. -/
  | call
  /-- Keep substituting at call sites. -/
  | inline
  deriving Inhabited, BEq, Repr

/-- `@[internal]` / `@[internal inline]`. Not Lean's builtin `@[inline]`. -/
syntax (name := internal) "internal" (ppSpace &"inline")? : attr

/-- Validate that `n` is a non-recursive definition. -/
def validateInternal (n : Name) : AttrM Unit := do
  let info ← getConstInfo n
  unless info.isDefinition do
    throwError "@[internal] can only be applied to definitions"
  let some v := info.value? |
    throwError "@[internal] can only be applied to definitions"
  if v.find? (·.isConstOf n) |>.isSome then
    throwError "@[internal] does not support recursive definitions"

initialize internalAttr : ParametricAttribute InternalKind ←
  registerParametricAttribute {
    name := `internal
    descr := "Mark a non-entrypoint function (Solidity `internal`)."
    getParam := fun n stx => do
      let kind ←
        match stx with
        | `(attr| internal) => pure InternalKind.call
        | `(attr| internal inline) => pure InternalKind.inline
        | _ =>
          match (← Attribute.Builtin.getIdent? stx) with
          | none => pure InternalKind.call
          | some id =>
            unless id.getId == `inline do
              throwError "@[internal] optional flag must be `inline`"
            pure InternalKind.inline
      validateInternal n
      return kind
  }

/-- True when `n` carries `@[internal]` (with or without `inline`). -/
def isInternal (env : Environment) (n : Name) : Bool :=
  (internalAttr.getParam? env n).isSome

end Lsc
