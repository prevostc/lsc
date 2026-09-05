import Lsc.Lang.Tx

/-!
A contract as a finite family of `Tx` entrypoints, each with its own argument and
return types. `lsc_contract` generates `C.Fn` / `C.entry` / `C.spec` from this.
-/

namespace Lsc

/-- One ABI entrypoint, with its own argument and return types. -/
structure Entry (S E ε : Type) where
  Args : Type
  Ret : Type
  run : Args → Tx S E ε Ret

/-- A contract as a family of entrypoints. `Fn` is typically a finite inductive. -/
structure Spec (S E ε : Type) where
  Fn : Type
  entry : Fn → Entry S E ε

namespace Spec
variable (C : Spec S E ε)
abbrev Args (fn : C.Fn) : Type := (C.entry fn).Args
abbrev Ret (fn : C.Fn) : Type := (C.entry fn).Ret
/-- Run the body of `fn` on `args`. -/
@[reducible] def exec (fn : C.Fn) (args : C.Args fn) : Tx S E ε (C.Ret fn) :=
  (C.entry fn).run args
end Spec

end Lsc
