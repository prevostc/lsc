import LscV2.Types
import LscV2.Arithmetic
import LscV2.Mapping
import LscV2.LinearTypes

namespace LscV2

inductive Ty
  | uint256
  | bool
  | address
  | wei
  | wad
  | ray
  | tokenAmount
  | allowance
  | flashReceipt
  | lock
  | capability
  | positionTicket
  | mapping (k v : Ty)
  | unit
  deriving Repr, DecidableEq

inductive Expr : Ty → Type
    | litU256 : UInt256 → Expr .uint256
    | litWei : Nat → Expr .wei
    | litBool : Bool → Expr .bool
    | litAddr : Address → Expr .address
    | var : Ident → Expr t
    | storageGet : Ident → Expr t
    | weiAddChecked : Expr .wei → Expr .wei → Expr .wei
    | weiSubChecked : Expr .wei → Expr .wei → Expr .wei
    | weiMulChecked : Expr .wei → Expr .wei → Expr .wei
    | weiDivFloor : Expr .wei → Expr .wei → Expr .wei
    | weiAddCheckedNat : Expr .wei → Nat → Expr .wei
    | wadAddChecked : Expr .wad → Expr .wad → Expr .wad
    | wadSubChecked : Expr .wad → Expr .wad → Expr .wad
    | wadMulDown : Expr .wad → Expr .wad → Expr .wad
    | wadMulUp : Expr .wad → Expr .wad → Expr .wad
    | wadMulHalfUp : Expr .wad → Expr .wad → Expr .wad
    | wadDivDown : Expr .wad → Expr .wad → Expr .wad
    | wadDivUp : Expr .wad → Expr .wad → Expr .wad
    | wadDivHalfUp : Expr .wad → Expr .wad → Expr .wad
    | rayAddChecked : Expr .ray → Expr .ray → Expr .ray
    | raySubChecked : Expr .ray → Expr .ray → Expr .ray
    | eq : Expr t → Expr t → Expr .bool
    | lt : Expr .uint256 → Expr .uint256 → Expr .bool
    | le : Expr .uint256 → Expr .uint256 → Expr .bool
    | not : Expr .bool → Expr .bool
    | and : Expr .bool → Expr .bool → Expr .bool
    | or : Expr .bool → Expr .bool → Expr .bool
    | caller : Expr .address
    | callvalue : Expr .uint256
    | timestamp : Expr .uint256
    | mappingGet : Expr (.mapping k v) → Expr k → Expr v
    | tokenMint : Expr .wei → Expr .tokenAmount
    | tokenBurn : Expr .tokenAmount → Expr .wei
    | tokenSplit : Expr .tokenAmount → Expr .wei
    | tokenMerge : Expr .tokenAmount → Expr .tokenAmount → Expr .tokenAmount

/-- Argument bundle for call/emit nodes. -/
abbrev ExprAny := Sigma Expr

inductive Stmt
  | skip
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → (t : Ty) × Expr t → Stmt
  | letBind2 : Ident → Ident → (t : Ty) × Expr t → Stmt
  | storageSet : Ident → (t : Ty) × Expr t → Stmt
  | storageMapSet : Ident → (k : Ty) × Expr k → (v : Ty) × Expr v → Stmt
  | require : Expr .bool → Ident → Stmt
  | ifThenElse : Expr .bool → Stmt → Stmt → Stmt
  | call : Ident → List ExprAny → Stmt
  | externalCall : Ident → Ident → List ExprAny → Stmt
  | emit : Ident → List ExprAny → Stmt
  | revert : Ident → Stmt
  | lockAcquire : Ident → Stmt
  | lockRelease : Expr .lock → Stmt

inductive FunctionKind
  | external
  | internal
  | view
  | constructor
  deriving Repr, DecidableEq

inductive LinearPermission
  | canMint (tokenType : Ident)
  | canBurn (tokenType : Ident)
  | canFlashBorrow
  deriving Repr, DecidableEq

structure FunctionDef where
  name : Ident
  kind : FunctionKind
  params : List (Ident × Ty)
  retTy : Ty
  body : Stmt
  permits : List LinearPermission

structure ContractDef where
  name : Ident
  storage : List (Ident × Ty × Option ExprAny)
  errors : List Ident
  events : List (Ident × List (Ident × Ty))
  functions : List FunctionDef
  interfaces : List (Ident × Ident)

end LscV2
