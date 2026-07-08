import Lsc.Types
import Lsc.Arithmetic
import Lsc.Lib.Wei.Syntax
import Lsc.Lib.Wad.Syntax

namespace Lsc

/-- Core type tags. `wei`/`wad` are lib-owned numeric types wired in exactly
alike (see `Expr` below); further extension types (ray, linear) live in
optional libs. -/
inductive Ty
  | uint256
  | bool
  | address
  | wei
  | wad
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

/-- Typed expressions: Wei/Wad live in `Lib.Wei`/`Lib.Wad`; primitives in `CoreExpr`. -/
def Expr : Ty → Type :=
  fun t => match t with
  | .wei => Wei.Expr
  | .wad => Wad.Expr
  | .uint256 | .bool | .address | .unit => CoreExpr t

abbrev ExprAny := Sigma Expr

inductive Stmt
  | skip
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → (t : Ty) × Expr t → Stmt
  | storageSet : Ident → (t : Ty) × Expr t → Stmt
  /-- `σ.field[key] = e;` — write one entry of an address-keyed `Lsc.Wad.WadMap` storage field
      (see that type's docstring, `Lib/Wad/Syntax.lean`). Kept as its own `Stmt` node (rather
      than folded into `storageSet`, which is `Ty`-indexed and `WadMap` is not a `Ty` at all —
      it is a storage-only `FieldKind`, see `Lang/Derive.lean`) since a mapping write needs both
      a key (`Wad.MapKey`) and a `Wad`-kinded value, not just a bare `Ty`-tagged value. -/
  | mapSet : Ident → Wad.MapKey → Wad.Expr → Stmt
  | require : Expr Ty.bool → Ident → Stmt
  | ifThenElse : Expr Ty.bool → Stmt → Stmt → Stmt
  | emit : Ident → List ExprAny → Stmt
  | revert : Ident → Stmt
  /-- `return e;` — only ever produced by `view` function bodies (`Lang/Syntax.lean`'s
      `lscReturn`), never by `tx` bodies (checked by `Checks.checkViewReturns`/purity at
      elaboration time). `Eval.lean`'s `Stmt.evalWith` threads the returned value out alongside
      `LocalEnv`, short-circuiting any following `.seq` sibling exactly like a real early
      `return`. -/
  | ret : (t : Ty) × Expr t → Stmt
  /-- `exec Target.fn(args);` — mutating cross-contract call. `targetField` holds the callee
      contract address (`Token` module → `token` storage field); `selector` is the 4-byte ABI
      selector; `args` are the already-elaborated argument expressions. -/
  | externalExec (targetField : Ident) (selector : Nat) (checkBoolReturn : Bool)
      (args : List ExprAny) : Stmt
  /-- `read Target.fn(args);` — read-only cross-contract call (`STATICCALL`). Same addressing
      convention as `externalExec`; no reentrancy guard required. -/
  | externalRead (targetField : Ident) (selector : Nat) (retWords : Nat)
      (args : List ExprAny) : Stmt
  /-- `@nonreentrant` desugaring — wraps a `tx` body; lowers to transient-storage lock
      prologue/epilogue (`TLOAD`/`TSTORE`). Visible to `Checks` and proofs. -/
  | reentrancyGuard (body : Stmt) : Stmt

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
  /-- Whether this `tx` was declared `@nonreentrant`. Required for any `tx` whose body contains
      `Stmt.externalExec` — checked by `Checks.checkNonReentrant` and at `tx`-elaboration time.
      The decorator desugars to `Stmt.reentrancyGuard` on the body. Optional/no-op otherwise. -/
  nonReentrant : Bool := false

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
