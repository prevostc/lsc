import Lsc.Lang.AST
import Lsc.Lib.Wei.Optimize
import Lsc.Lib.Wad.Optimize

namespace Lsc.Compile

/-! Cross-contract `exec`/`read` lower to `IR.externalCall`/`IR.staticCall` with ABI-packed
calldata. `Stmt.reentrancyGuard` lowers to transient-storage lock IR. -/

structure StorageLayout where
  slots : List (Ident × Nat)
  mapSlots : List (Ident × Nat) := []
  deriving Repr

namespace StorageLayout

def fieldSlot (layout : StorageLayout) (field : Ident) : Option Nat :=
  (layout.slots.find? (·.1 == field)).map (·.2)

def mapFieldSlot (layout : StorageLayout) (field : Ident) : Option Nat :=
  (layout.mapSlots.find? (·.1 == field)).map (·.2)

def fromList (slots : List (Ident × Nat)) : StorageLayout := ⟨slots, []⟩

end StorageLayout

structure EventLayout where
  topic0 : Ident → Option Nat

structure Config where
  storage : StorageLayout
  events : EventLayout := { topic0 := fun _ => none }

open Lsc.Compile.IR (Expr Stmt)

namespace Lower

private def resolveSlot (cfg : Config) (field : Ident) : Except String Nat :=
  match cfg.storage.fieldSlot field with
  | some s => .ok s
  | none => .error s!"unknown storage field {field}"

private def resolveMapSlot (cfg : Config) (field : Ident) : Except String Nat :=
  match cfg.storage.mapFieldSlot field with
  | some s => .ok s
  | none => .error s!"unknown mapping field {field}"

private def lowerMapKey (_cfg : Config) (key : Wad.MapKey) : Except String IR.Expr :=
  match key with
  | .caller => .ok (.local "caller")
  | .var name => .ok (.local name)

private partial def lowerCoreExpr (cfg : Config) {t : Ty} (e : CoreExpr t) : Except String IR.Expr :=
  match e with
  | .lit _ l =>
    match l with
    | .u256 n => .ok (.lit n.toNat)
    | .bool b => .ok (.lit (if b then 1 else 0))
    | .addr _ => .error "address literal lowering not supported"
  | .var _ name => .ok (.local name)
  | .storageGet _ field => do
    let s ← resolveSlot cfg field
    .ok (.sload s)
  | .txField f =>
    match f with
    | .caller => .ok (.local "caller")
    | .callvalue | .timestamp => .ok (.lit 0)
  | .not a => do
    let a' ← lowerCoreExpr cfg a
    .ok (.isZero a')
  | .eq _ a b => do
    let a' ← lowerCoreExpr cfg a
    let b' ← lowerCoreExpr cfg b
    .ok (.eq a' b')
  | _ => .error "unsupported expression in lowering"

private partial def lowerExpr (cfg : Config) {t : Ty} (e : Expr t) : Except String IR.Expr :=
  match t, e with
  | .wei, e => Wei.lowerExpr cfg.storage.fieldSlot e
  | .wad, e => Wad.lowerExpr cfg.storage.fieldSlot cfg.storage.mapFieldSlot e
  | .uint256, e => lowerCoreExpr cfg e
  | .bool, e => lowerCoreExpr cfg e
  | .address, e => lowerCoreExpr cfg e
  | .unit, e => lowerCoreExpr cfg e

private def lowerExprAny (cfg : Config) (e : ExprAny) : Except String IR.Expr :=
  lowerExpr cfg e.2

/-- Calldata size in bytes: 4-byte selector + 32 bytes per argument. -/
private def calldataSize (args : List IR.Expr) : Nat :=
  4 + 32 * args.length

/-- Lower argument expressions for an external call (already in IR.Expr form). -/
private def lowerExternalArgs (cfg : Config) (args : List ExprAny) : Except String (List IR.Expr) :=
  args.mapM (lowerExprAny cfg)

/-- Address of the callee: `sload` of a storage field, or a bound local/param. -/
private def lowerCalleeAddr (cfg : Config) (callee : CalleeRef) : Except String IR.Expr :=
  match callee with
  | .storageField targetField => do
    let slot ← resolveSlot cfg targetField
    .ok (.sload slot)
  | .local name => .ok (.local name)

private partial def lowerStmt (cfg : Config) (s : Lsc.Stmt) : Except String IR.Stmt :=
  match s with
  | .skip => .ok .skip
  | .seq s1 s2 => do
    let ir1 ← lowerStmt cfg s1
    let ir2 ← lowerStmt cfg s2
    .ok (.seq ir1 ir2)
  | .letBind name ⟨Ty.wei, e⟩ =>
    Wei.lowerLetBind cfg.storage.fieldSlot name e
  | .letBind name ⟨t, e⟩ => do
    let ir ← lowerExpr cfg (t := t) e
    .ok (.letBind name ir)
  | .storageSet field ⟨t, e⟩ => do
    let s ← resolveSlot cfg field
    let ir ← lowerExpr cfg (t := t) e
    .ok (.sstore s ir)
  | .require e _ => do
    let cond ← lowerExpr cfg (t := Ty.bool) e
    .ok (.ifRevert (.isZero cond))
  | .emit eventName args =>
    match cfg.events.topic0 eventName with
    | some topic =>
      match args with
      | [⟨Ty.wei, dataExpr⟩] => do
        let data ← Wei.lowerExpr cfg.storage.fieldSlot dataExpr
        .ok (.log1 topic data)
      | [⟨Ty.wad, dataExpr⟩] => do
        let data ← Wad.lowerExpr cfg.storage.fieldSlot cfg.storage.mapFieldSlot dataExpr
        .ok (.log1 topic data)
      | [] =>
        .ok (.log0 topic)
      | _ => .error s!"unsupported emit arity for {eventName}"
    | none => .error s!"unknown event {eventName}"
  | .revert _ => .ok .revert0
  | .ret ⟨t, e⟩ => do
    let ir ← lowerExpr cfg (t := t) e
    .ok (.ret ir)
  | .reentrancyGuard body => do
    let irBody ← lowerStmt cfg body
    .ok (.seq (.seq (.seq .checkReentrancyLock (.setReentrancyLock true)) irBody)
      (.setReentrancyLock false))
  | .externalExec callee selector args => do
    let addr ← lowerCalleeAddr cfg callee
    let argExprs ← lowerExternalArgs cfg args
    .ok (.externalCall addr selector argExprs false)
  | .letExecBind name _ callee selector args => do
    let addr ← lowerCalleeAddr cfg callee
    let argExprs ← lowerExternalArgs cfg args
    .ok (.externalCallBind addr selector argExprs name)
  | .externalRead callee selector retWords args => do
    let addr ← lowerCalleeAddr cfg callee
    let argExprs ← lowerExternalArgs cfg args
    .ok (.staticCall addr selector argExprs retWords)
  | .letReadBind name _ callee selector _ args => do
    let addr ← lowerCalleeAddr cfg callee
    let argExprs ← lowerExternalArgs cfg args
    .ok (.staticCallBind addr selector argExprs name)
  | .mapSet field key expr => do
    let base ← resolveMapSlot cfg field
    let keyIr ← lowerMapKey cfg key
    let valIr ← Wad.lowerExpr cfg.storage.fieldSlot cfg.storage.mapFieldSlot expr
    .ok (.sstoreDyn (.mapSlot base keyIr) valIr)
  | _ => .error "unsupported statement in lowering"

def stmt (cfg : Config) (s : Lsc.Stmt) : Except String IR.Stmt :=
  lowerStmt cfg s

/-- Prepend ABI calldata `letBind`s for each function parameter (declaration order). -/
private partial def paramPrologueFrom (params : List (Ident × Ty)) (i : Nat) (baseOffset : Nat)
    (body : IR.Stmt) : IR.Stmt :=
  match params.drop i with
  | [] => body
  | (name, _) :: _ =>
    .seq (.letBind name (.calldataWord (baseOffset + 32 * i)))
      (paramPrologueFrom params (i + 1) baseOffset body)

private def paramPrologue (params : List (Ident × Ty)) (baseOffset : Nat) (body : IR.Stmt) : IR.Stmt :=
  paramPrologueFrom params 0 baseOffset body

/-- Lower a `FunctionDef` body with ABI parameter bindings in IR.
    `baseOffset` is 4 for external functions (after selector) and 0 for constructors. -/
def function (cfg : Config) (fn : FunctionDef) (baseOffset : Nat := 4) : Except String IR.Stmt := do
  let body ← stmt cfg fn.body
  .ok (paramPrologue fn.params baseOffset body)

end Lower
end Lsc.Compile
