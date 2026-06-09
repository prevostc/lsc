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

-- `require cond err` — revert with `err` when `cond` is false.
macro "require" cond:term err:term : doElem =>
  `(doElem| unless $cond do ContractM.revert $err)

macro "get" "." field:ident : term => do
  let fieldRef : Lean.Ident := Lean.mkIdent (`fields ++ field.getId)
  `(ContractM.get $fieldRef)

macro "set" "." field:ident val:term : doElem => do
  let fieldRef : Lean.Ident := Lean.mkIdent (`fields ++ field.getId)
  `(doElem| ContractM.set $fieldRef $val)

end ContractM

-- `failWhen b err` — revert with `err` when `b` is true.
-- Lives in the `Lsc` namespace so `open Lsc` exposes it directly.
-- Usage in a `do` block:  `failWhen (← get .paused) .IsPausedError`
-- Lean 4 do-notation desugars `(← e)` in term position, so the visible ←
-- is genuine syntax, not hidden by any macro.
def failWhen {E S : Type} (b : Bool) (err : E) : ContractM E S Unit :=
  if b then ContractM.revert err else pure ()

end Lsc

namespace Bool

/-- `¬b` (Bool coerced to `Prop`) rewrites to `b = false` under `simp`. -/
@[simp] theorem not_iff_eq_false {b : Bool} : (¬b) ↔ (b = false) := by
  cases b <;> simp

end Bool
