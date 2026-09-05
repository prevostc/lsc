import Lsc.Lang.Tx

/-!
A contract as a finite family of `Tx` entrypoints, each with its own argument and
return types. `lsc_contract` generates `C.Fn` / `C.entry` / `C.spec` from this.
-/

namespace Lsc

/-- One ABI entrypoint, with its own argument and return types. -/
structure Entry (S X E ε : Type) where
  Args : Type
  Ret : Type
  run : Args → Tx S X E ε Ret

/-- A contract as a family of entrypoints. `Fn` is typically a finite inductive. -/
structure Spec (S X E ε : Type) where
  Fn : Type
  entry : Fn → Entry S X E ε

namespace Spec
variable (C : Spec S X E ε)
abbrev Args (fn : C.Fn) : Type := (C.entry fn).Args
abbrev Ret (fn : C.Fn) : Type := (C.entry fn).Ret
/-- Run the body of `fn` on `args`. -/
@[reducible] def exec (fn : C.Fn) (args : C.Args fn) : Tx S X E ε (C.Ret fn) :=
  (C.entry fn).run args
end Spec

end Lsc
