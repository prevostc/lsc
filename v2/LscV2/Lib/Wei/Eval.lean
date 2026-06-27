import LscV2.Core.ContractM
import LscV2.Lib.Wei.Expr
import LscV2.Lib.Wei.Arith

namespace LscV2.Wei

variable {S E Err : Type} [ContractErrors Err]

def eval
    (getField : (t : Ty) → Ident → S → Option (Val t))
    (e : Wei.Expr) (env : LocalEnv) : ContractM S E Err Wei :=
  match e with
  | .lit n => pure (Wei.mkNat n)
  | .var name =>
    match env.lookup name with
    | some ⟨Ty.wei, v⟩ => pure (Val.weiOf v)
    | _ => ContractM.revert .Unauthorized
  | .storageGet field => do
    let st ← ContractM.get
    match getField Ty.wei field st.storage with
    | some (.wei w) => pure w
    | _ => ContractM.revert .Unauthorized
  | .addChecked a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    match Wei.addChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .addCheckedNat a n => do
    let va ← eval getField a env
    match Wei.addCheckedNat va n with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .subChecked a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    match Wei.subChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r

attribute [simp] eval

end LscV2.Wei
