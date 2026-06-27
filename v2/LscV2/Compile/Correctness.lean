import LscV2.Compile.Lower
import LscV2.Compile.IR
import LscV2.TestFixtures.Counter

namespace LscV2.Compile.Correctness

open LscV2.TestFixtures

abbrev IRExpr := LscV2.Compile.IR.Expr
abbrev IRStmt := LscV2.Compile.IR.Stmt

/-- Nat-valued IR state for the Counter increment slice. -/
structure IRState where
  locals : List (Ident × Nat) := []
  slots : List (Nat × Nat) := []
  logs : List (Nat × Nat) := []
  reverted : Bool := false
  deriving Repr

namespace IRState

def lookupLocal (st : IRState) (name : Ident) : Nat :=
  match st.locals.find? (·.1 == name) with
  | some (_, v) => v
  | none => 0

def lookupSlot (st : IRState) (slot : Nat) : Nat :=
  match st.slots.find? (·.1 == slot) with
  | some (_, v) => v
  | none => 0

def setLocal (st : IRState) (name : Ident) (v : Nat) : IRState :=
  { st with locals := (name, v) :: st.locals.filter (·.1 != name) }

def setSlot (st : IRState) (slot : Nat) (v : Nat) : IRState :=
  { st with slots := (slot, v) :: st.slots.filter (·.1 != slot) }

end IRState

partial def evalExpr (st : IRState) (e : IRExpr) : Nat :=
  match e with
  | .lit n => n
  | .local name => st.lookupLocal name
  | .sload slot => st.lookupSlot slot
  | .add a b => evalExpr st a + evalExpr st b
  | .lt a b => if evalExpr st a < evalExpr st b then 1 else 0
  | .eq a b => if evalExpr st a == evalExpr st b then 1 else 0
  | .isZero a => if evalExpr st a == 0 then 1 else 0

partial def evalStmt (st : IRState) (s : IRStmt) : IRState :=
  match s with
  | .skip => st
  | .seq s1 s2 => evalStmt (evalStmt st s1) s2
  | .letBind name e => st.setLocal name (evalExpr st e)
  | .sstore slot e => st.setSlot slot (evalExpr st e)
  | .ifRevert cond =>
    if evalExpr st cond = 1 then { st with reverted := true } else st
  | .log1 topic data => { st with logs := st.logs ++ [(topic, evalExpr st data)] }
  | .revert0 => { st with reverted := true }

def counterConfig : Config :=
  { storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  , events := { topic0 := fun _ => none } }

/-- Expected IR for `let n ← $.number +? 1` at slot 0. -/
def incrementLetIR : IRStmt :=
  let old := "lsc_n_old"
  .seq
    (.letBind old (.sload 0))
    (.seq
      (.letBind "n" (.add (.local old) (.lit 1)))
      (.seq
        (.ifRevert (.lt (.local "n") (.local old)))
        .skip))

theorem Wei_lower_addCheckedNatStorage_shape :
    Wei.Lower.lowerLetBind (fun f => counterConfig.storage.fieldSlot f) "n"
        (Wei.addCheckedNatStorage "number" 1) =
      .ok incrementLetIR := rfl

theorem incrementLet_lowers_ok :
    (Lower.stmt counterConfig incrementLet).isOk := by native_decide

theorem incrementLet_ir_binds_incremented_local :
    let st := evalStmt { slots := [(0, 5)] } incrementLetIR
    st.lookupLocal "n" = 6 ∧ st.lookupLocal "lsc_n_old" = 5 ∧ ¬ st.reverted := by native_decide

def incrementBody : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementEventConfig : Config :=
  { storage := counterConfig.storage
  , events := { topic0 := fun
      | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
      | _ => none } }

theorem increment_body_lowers_ok :
    Lower.stmt incrementEventConfig incrementBody |>.isOk := by native_decide

end LscV2.Compile.Correctness
