import Lsc.Lib.Wei.Syntax
import Lsc.Lib.Fixed.Arith
import Lsc.Core.ContractM
import Lsc.Lang.AST

namespace Lsc.Wei

def addChecked (a b : Wei) : Except ArithError Wei := Fixed.addChecked a b
def subChecked (a b : Wei) : Except ArithError Wei := Fixed.subChecked a b
def addCheckedNat (a : Wei) (n : Nat) : Except ArithError Wei := Fixed.addCheckedNat a n

abbrev Wei.canAddNat (w : Wei) (n : Nat) : Prop := w.raw.toNat + n < 2 ^ 256

@[simp] theorem addCheckedNat_ok (a : Wei) (n : Nat) (h : Wei.canAddNat a n) :
    addCheckedNat a n = .ok ⟨BitVec.ofNat 256 (a.raw.toNat + n)⟩ := by
  unfold Wei.canAddNat at h
  simp [addCheckedNat, Fixed.addCheckedNat, Fixed.mkNat, UInt256.addCheckedNat_ok a.raw n h, Except.map]

@[simp] theorem addCheckedNat_error (a : Wei) (n : Nat) (h : ¬ Wei.canAddNat a n) :
    addCheckedNat a n = .error .Overflow := by
  unfold Wei.canAddNat at h
  simp [addCheckedNat, Fixed.addCheckedNat, UInt256.addCheckedNat_error a.raw n h, Except.map]

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

def eval (e : Expr) (env : LocalEnv) : ContractM S E Err Wei :=
  match e with
  | .lit n => pure (Wei.mkNat n)
  | .var name =>
    match env.lookup name with
    | some ⟨Ty.wei, v⟩ => pure (Val.weiOf v)
    | _ => ContractM.revert .Unauthorized
  | .storageGet field => do
    let st ← ContractM.get
    match dsl.getField Ty.wei field st.storage with
    | some (.wei w) => pure w
    | _ => ContractM.revert .Unauthorized
  | .addChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wei.addChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .addCheckedNat a n => do
    let va ← eval a env
    match Wei.addCheckedNat va n with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .subChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wei.subChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .sqrtDownChecked scale a => do
    let va ← eval a env
    match Fixed.sqrtDown scale va with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .min a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (Fixed.min va vb)
  | .mulHalfUpChecked _ _ _ | .divDownChecked _ _ _ | .mapGet _ _ | .mapGet2 _ _ _ =>
    ContractM.revert .Unauthorized

attribute [simp] eval

end Lsc.Wei
