import LscV2.Lib.Wei.Expr

namespace LscV2.Wei

def arithErrors : Expr → List ArithError
  | .addChecked _ _ => [.Overflow]
  | .addCheckedNat _ _ => [.Overflow]
  | .subChecked _ _ => [.Underflow]
  | _ => []

end LscV2.Wei
