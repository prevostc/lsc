import Lean

/-!
# `@[lsc_inline]`

Tag a library `Tx` helper so Reify delta-unfolds it (β with arguments, fuel-bounded)
and continues on the body. Recursive definitions are rejected at attribute
application. Certificates are kernel-checked `Core.denote (reify f) = f` (`rfl`,
or `Tx` monad laws when a helper sits mid-`do`).
-/

open Lean

namespace Lsc

initialize lscInlineAttr : TagAttribute ←
  registerTagAttribute `lsc_inline
    "Delta-unfold this `Tx` helper during reification."
    fun n => do
      let info ← getConstInfo n
      unless info.isDefinition do
        throwError "@[lsc_inline] can only be applied to definitions"
      let some v := info.value? |
        throwError "@[lsc_inline] can only be applied to definitions"
      if v.find? (·.isConstOf n) |>.isSome then
        throwError "@[lsc_inline] does not support recursive definitions"

end Lsc
