import Lean

/-!
# `@[reentrant]`

Opt a contract function out of acquiring/releasing the transient
reentrancy lock (`locks f` is then false). The runtime prologue still
checks the slot. `@[reentrant (unsafe := true)]` additionally skips the
compile-time store-after-call rejection.
-/

open Lean

namespace Lsc

/-- `true` when the attribute was `@[reentrant (unsafe := true)]`. -/
abbrev ReentrantUnsafe := Bool

syntax (name := reentrant) "reentrant" (ppSpace "(" &"unsafe" " := " term ")")? : attr

def parseReentrantUnsafe (stx : Syntax) : AttrM ReentrantUnsafe := do
  match stx with
  | `(attr| reentrant) => return false
  | `(attr| reentrant (unsafe := true)) => return true
  | `(attr| reentrant (unsafe := false)) => return false
  | _ => throwError "unexpected @[reentrant] syntax; use `@[reentrant]` or \
      `@[reentrant (unsafe := true)]`"

initialize reentrantAttr : ParametricAttribute ReentrantUnsafe ←
  registerParametricAttribute {
    name := `reentrant
    descr := "Opt this function out of the transient reentrancy lock. \
      `@[reentrant (unsafe := true)]` also allows storage writes after an \
      external call."
    getParam := fun n stx => do
      let info ← getConstInfo n
      unless info.isDefinition do
        throwError "@[reentrant] can only be applied to definitions"
      parseReentrantUnsafe stx
  }

/-- `(reentrant, reentrantUnsafe)` from the env attribute, else both false. -/
def reentrantFlags (env : Environment) (fn : Name) : Bool × Bool :=
  match reentrantAttr.getParam? env fn with
  | none => (false, false)
  | some u => (true, u)

end Lsc
