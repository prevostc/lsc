import Lsc.Types
import Lsc.Arithmetic
import Lsc.Lib.Wei.Syntax

namespace Lsc

/-- Core type tags. Extension types (wad, ray, linear) live in optional libs. -/
inductive Ty
  | uint256
  | bool
  | address
  | wei
  | unit
  deriving Repr, DecidableEq

/-- Literal payload for core primitive types (not lib-owned types). -/
inductive Lit : Ty → Type
  | u256 : UInt256 → Lit Ty.uint256
  | bool : Bool → Lit Ty.bool
  | addr : Address → Lit Ty.address

inductive TxField
  | caller
  | callvalue
  | timestamp
  deriving Repr, DecidableEq

def txFieldTy : TxField → Ty
  | .caller => .address
  | .callvalue => .uint256
  | .timestamp => .uint256

/-- Core expression AST for primitive types (bool, address, uint256, unit). -/
inductive CoreExpr : Ty → Type
  | lit : (t : Ty) → Lit t → CoreExpr t
  | var (t : Ty) : Ident → CoreExpr t
  | storageGet (t : Ty) : Ident → CoreExpr t
  | txField (f : TxField) : CoreExpr (txFieldTy f)
  | eq (t : Ty) : CoreExpr t → CoreExpr t → CoreExpr Ty.bool
  | lt : CoreExpr Ty.uint256 → CoreExpr Ty.uint256 → CoreExpr Ty.bool
  | le : CoreExpr Ty.uint256 → CoreExpr Ty.uint256 → CoreExpr Ty.bool
  | not : CoreExpr Ty.bool → CoreExpr Ty.bool
  | and : CoreExpr Ty.bool → CoreExpr Ty.bool → CoreExpr Ty.bool
  | or : CoreExpr Ty.bool → CoreExpr Ty.bool → CoreExpr Ty.bool
  | unit : CoreExpr Ty.unit

/-- Typed expressions: Wei lives in `Lib.Wei`; primitives in `CoreExpr`. -/
def Expr : Ty → Type :=
  fun t => match t with
  | .wei => Wei.Expr
  | .uint256 | .bool | .address | .unit => CoreExpr t

abbrev ExprAny := Sigma Expr

inductive Stmt
  | skip
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → (t : Ty) × Expr t → Stmt
  | storageSet : Ident → (t : Ty) × Expr t → Stmt
  | require : Expr Ty.bool → Ident → Stmt
  | ifThenElse : Expr Ty.bool → Stmt → Stmt → Stmt
  | emit : Ident → List ExprAny → Stmt
  | revert : Ident → Stmt

inductive FunctionKind
  | external
  | internal
  | view
  | constructor
  deriving Repr, DecidableEq

structure FunctionDef where
  name : Ident
  kind : FunctionKind
  params : List (Ident × Ty)
  retTy : Ty
  body : Stmt

structure ContractDef where
  name : Ident
  storage : List (Ident × Ty × Option ExprAny)
  errors : List Ident
  events : List (Ident × List (Ident × Ty))
  functions : List FunctionDef
  interfaces : List (Ident × Ident)
  /-- Optional constructor body. When present, `deployToBytecode` wraps runtime
      bytecode with an EVM deploy transaction (CODECOPY + RETURN pattern). -/
  constructor : Option Stmt := none

end Lsc
