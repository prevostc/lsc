import Lsc.Error
import Lsc.ContractState
import Lsc.Word

namespace Lsc

/- `S` is an intentional phantom type parameter that keeps `Counter` and `Vault` distinct. -/
set_option linter.unusedVariables false in
/-- Contract effect monad: `World → Except (ContractError E) (α × World)`.
    `S` is phantom — it pins the `ContractState` instance per contract. -/
abbrev ContractM (E : Type) (S : Type) (α : Type) :=
  StateT World (Except (ContractError E)) α

namespace ContractM

@[simp] def get {E S σ : Type} [cs : ContractState S] [FromWord σ] (field : Field S σ) :
    ContractM E S σ :=
  fun w => .ok (FromWord.fromWord (World.getStorage w cs.self field.offset), w)

@[simp] def set {E S σ : Type} [cs : ContractState S] [ToWord σ] (field : Field S σ) (val : σ) :
    ContractM E S Unit :=
  fun w => .ok ((), World.setStorage w cs.self field.offset (ToWord.toWord val))

def arithFail {E S α : Type} (e : ArithError) : ContractM E S α :=
  fun _ => .error (.arith e)

def revertFail {E S α : Type} (e : E) : ContractM E S α :=
  fun _ => .error (.contract e)

@[simp] def revert {E S α : Type} (e : E) : ContractM E S α :=
  revertFail e

macro "get" "." field:ident : term => do
  let fieldRef : Lean.Ident := Lean.mkIdent (`fields ++ field.getId)
  `(ContractM.get $fieldRef)

macro "set" "." field:ident val:term : doElem => do
  let fieldRef : Lean.Ident := Lean.mkIdent (`fields ++ field.getId)
  `(doElem| ContractM.set $fieldRef $val)

end ContractM

end Lsc
