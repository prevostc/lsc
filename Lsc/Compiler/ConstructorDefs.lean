import Lsc.Lang.Core

/-!
`NoIte`: constructor cores without `ite` (Token). Needed by `constructor_correct`.
-/

namespace Lsc.Compiler

open Lsc

/-- Cores without `ite` / `seqIf` (Token constructor). Avoids a `.normal` switch lemma. -/
def NoIte : {t : RetTy} → Core t → Prop
  | _, .ite .. => False
  | _, .seqIf .. => False
  | _, .letOp _ k => NoIte k
  | _, .seq _ k => NoIte k
  | _, .letPure _ _ k => NoIte k
  | _, _ => True

end Lsc.Compiler
