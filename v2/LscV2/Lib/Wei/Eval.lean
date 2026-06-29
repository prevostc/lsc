import LscV2.Lib.Wei.Syntax
import LscV2.Core.ContractM
import LscV2.Lang.AST

namespace LscV2.Wei

def addChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.addChecked a.raw b.raw).map Wei.mk

def subChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.subChecked a.raw b.raw).map Wei.mk

def mulChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.mulChecked a.raw b.raw).map Wei.mk

def divFloor (a b : Wei) : Except ArithError Wei :=
  (UInt256.divChecked a.raw b.raw).map Wei.mk

def addCheckedNat (a : Wei) (n : Nat) : Except ArithError Wei :=
  (UInt256.addCheckedNat a.raw n).map Wei.mk

/-- `w.canAddNat n` holds iff adding `n` to `w` will not overflow 256 bits. -/
abbrev Wei.canAddNat (w : Wei) (n : Nat) : Prop := w.raw.toNat + n < 2 ^ 256

@[simp]
theorem addCheckedNat_ok (a : Wei) (n : Nat) (h : a.canAddNat n) :
    addCheckedNat a n = .ok ⟨BitVec.ofNat 256 (a.raw.toNat + n)⟩ := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

@[simp]
theorem addCheckedNat_error (a : Wei) (n : Nat) (h : ¬ a.canAddNat n) :
    addCheckedNat a n = .error .Overflow := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

def eval
    (e : Expr) (env : LocalEnv) : ContractM S E Err Wei :=
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

attribute [simp] eval

end LscV2.Wei
