import LscV2.AST
import LscV2.Compile.IR

namespace LscV2.Compile

/-- Storage field → sequential EVM slot (Solidity layout, v1). -/
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

namespace Lower

private def resolveSlot (cfg : Config) (field : Ident) : Except String Nat :=
  match cfg.storage.fieldSlot field with
  | some s => .ok s
  | none => .error s!"unknown storage field {field}"

private partial def lowerExpr (cfg : Config) (e : Sigma LscV2.Expr) : Except String IR.Expr :=
  match e with
  | ⟨Ty.wei, LscV2.Expr.litWei n⟩ => .ok (.lit n)
  | ⟨Ty.uint256, LscV2.Expr.litU256 n⟩ => .ok (.lit n.toNat)
  | ⟨Ty.bool, LscV2.Expr.litBool b⟩ => .ok (.lit (if b then 1 else 0))
  | ⟨_, LscV2.Expr.var name⟩ => .ok (.local name)
  | ⟨_, LscV2.Expr.storageGet field⟩ => do
    let s ← resolveSlot cfg field
    .ok (.sload s)
  | ⟨Ty.address, LscV2.Expr.caller⟩ => .ok (.local "caller")
  | ⟨Ty.bool, LscV2.Expr.not a⟩ => do
    let a' ← lowerExpr cfg ⟨Ty.bool, a⟩
    .ok (.isZero a')
  | ⟨Ty.bool, @LscV2.Expr.eq t a b⟩ => do
    let a' ← lowerExpr cfg ⟨t, a⟩
    let b' ← lowerExpr cfg ⟨t, b⟩
    .ok (.eq a' b')
  | _ => .error "unsupported expression in lowering"

private def checkedAddNat (cfg : Config) (field : Ident) (n : Nat) (bind : Ident) (rest : IR.Stmt) :
    Except String IR.Stmt := do
  let s ← resolveSlot cfg field
  let old := s!"lsc_{field}_old"
  .ok <| .seq
    (.letBind old (.sload s))
    (.seq
      (.letBind bind (.add (.local old) (.lit n)))
      (.seq
        (.ifRevert (.lt (.local bind) (.local old)))
        rest))

private partial def lowerStmt (cfg : Config) (s : LscV2.Stmt) : Except String IR.Stmt :=
  match s with
  | .skip => .ok .skip
  | .seq s1 s2 => do
    let ir1 ← lowerStmt cfg s1
    let ir2 ← lowerStmt cfg s2
    .ok (.seq ir1 ir2)
  | .letBind name ⟨Ty.wei, LscV2.Expr.weiAddCheckedNat (LscV2.Expr.storageGet field) n⟩ =>
    checkedAddNat cfg field n name .skip
  | .letBind name tyExpr => do
    let e ← lowerExpr cfg tyExpr
    .ok (.letBind name e)
  | .storageSet field tyExpr => do
    let s ← resolveSlot cfg field
    let e ← lowerExpr cfg tyExpr
    .ok (.sstore s e)
  | .require e _ => do
    let cond ← lowerExpr cfg ⟨Ty.bool, e⟩
    .ok (.ifRevert (.isZero cond))
  | .emit eventName args =>
    match cfg.events.topic0 eventName with
    | some topic =>
      match args with
      | [⟨Ty.wei, dataExpr⟩] => do
        let data ← lowerExpr cfg ⟨Ty.wei, dataExpr⟩
        .ok (.log1 topic data)
      | [] =>
        .ok (.log1 topic (.lit 0))
      | _ => .error s!"unsupported emit arity for {eventName}"
    | none => .error s!"unknown event {eventName}"
  | .revert _ => .ok .revert0
  | _ => .error "unsupported statement in lowering"

def stmt (cfg : Config) (s : LscV2.Stmt) : Except String IR.Stmt :=
  lowerStmt cfg s

end Lower
end LscV2.Compile
