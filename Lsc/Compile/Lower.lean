import Lsc.Lang.AST
import Lsc.Lib.Wei.Optimize
import Lsc.Lib.Wad.Optimize

namespace Lsc.Compile

/-! Cross-contract `exec`/`read` lower to `IR.externalCall`/`IR.staticCall` with ABI-packed
calldata. `Stmt.reentrancyGuard` lowers to transient-storage lock IR. -/

structure StorageLayout where
  slots : List (Ident × Nat)
  deriving Repr

namespace StorageLayout

def fieldSlot (layout : StorageLayout) (field : Ident) : Option Nat :=
  (layout.slots.find? (·.1 == field)).map (·.2)

def fromList (slots : List (Ident × Nat)) : StorageLayout := ⟨slots⟩

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
  | .wad, e => Wad.lowerExpr cfg.storage.fieldSlot e
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

/-- Address of the callee: `sload` of the `targetField` storage slot. -/
private def lowerCalleeAddr (cfg : Config) (targetField : Ident) : Except String IR.Expr := do
  let slot ← resolveSlot cfg targetField
  .ok (.sload slot)

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
        let data ← Wad.lowerExpr cfg.storage.fieldSlot dataExpr
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
  | .externalExec targetField selector checkBoolReturn args => do
    let addr ← lowerCalleeAddr cfg targetField
    let argExprs ← lowerExternalArgs cfg args
    .ok (.externalCall addr selector argExprs checkBoolReturn)
  | .externalRead targetField selector retWords args => do
    let addr ← lowerCalleeAddr cfg targetField
    let argExprs ← lowerExternalArgs cfg args
    .ok (.staticCall addr selector argExprs retWords)
  | _ => .error "unsupported statement in lowering"

def stmt (cfg : Config) (s : Lsc.Stmt) : Except String IR.Stmt :=
  lowerStmt cfg s

end Lower
end Lsc.Compile
