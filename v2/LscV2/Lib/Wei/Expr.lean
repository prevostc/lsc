import LscV2.Lib.Wei.Type

namespace LscV2.Wei

/-- Wei-domain expression fragment (`Expr .wei`). -/
inductive Expr where
  | lit : Nat → Expr
  | var : Ident → Expr
  | storageGet : Ident → Expr
  | addChecked : Expr → Expr → Expr
  | addCheckedNat : Expr → Nat → Expr
  | subChecked : Expr → Expr → Expr
  deriving Repr

end LscV2.Wei
