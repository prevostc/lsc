import Lsc.Types

namespace Lsc

/-- The key a `σ.field[key]` mapping read/write is keyed by — deliberately a small,
self-contained sum type (rather than reusing `Lsc.CoreExpr Ty.address`) since `Wad.Expr` sits
*below* `Lang/AST.lean`'s `CoreExpr`/`Ty` machinery in the import graph. Restricts a mapping key
to exactly the two forms real contracts need (`msg.sender`, or a bare local name). -/
inductive MapKey where
  | caller
  | var : Ident → MapKey
  deriving Repr

end Lsc
