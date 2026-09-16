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

/-- `[Payable]` table. Default: nothing is payable. `lsc_contract` generates
a specialized instance when some entry has `[Payable]`. Kept off `Spec`
so `exec` / `Args` stay instance-free (Vault `lsc_contract`). -/
class HasPayable (C : Spec S X E ε) where
  payable : C.Fn → Bool

instance (priority := low) {S X E ε : Type} {C : Spec S X E ε} : HasPayable C where
  payable := fun _ => false

namespace Spec
variable (C : Spec S X E ε)
abbrev Args (fn : C.Fn) : Type := (C.entry fn).Args
abbrev Ret (fn : C.Fn) : Type := (C.entry fn).Ret
/-- Run the body of `fn` on `args`. -/
@[reducible] def exec (fn : C.Fn) (args : C.Args fn) : Tx S X E ε (C.Ret fn) :=
  (C.entry fn).run args
/-- `[Payable]` table: `HasPayable` instance, default `false`. -/
@[reducible] def payable [HasPayable C] (fn : C.Fn) : Bool :=
  HasPayable.payable (C := C) fn
/-- Same shape as compiler `valueOk`: payable, or zero value. -/
def valueOk [HasPayable C] (fn : C.Fn) (v : Nat) : Bool :=
  C.payable fn || decide (v = 0)
theorem valueOk_zero [HasPayable C] (fn : C.Fn) : C.valueOk fn 0 = true := by
  simp [valueOk]
theorem valueOk_of_payable [HasPayable C] {fn : C.Fn} {v : Nat}
    (h : C.payable fn = true) : C.valueOk fn v = true := by
  simp [valueOk, h]
theorem valueOk_false [HasPayable C] {fn : C.Fn} {v : Nat}
    (hp : C.payable fn = false) (hv : v ≠ 0) : C.valueOk fn v = false := by
  simp [valueOk, hp, hv]
theorem value_eq_zero_of_valueOk [HasPayable C] {fn : C.Fn} {v : Nat}
    (hp : C.payable fn = false) (hvo : C.valueOk fn v = true) : v = 0 := by
  simp [valueOk, hp] at hvo
  exact hvo
end Spec

end Lsc
