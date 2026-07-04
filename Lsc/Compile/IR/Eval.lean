import Lsc.Compile.IR

namespace Lsc.Compile.IR

open Lsc (Ident)

/-- Nat-valued IR state for reference evaluation. -/
structure IRState where
  locals : Ident → Option Nat := fun _ => none
  slots : List (Nat × Nat) := []
  logs : List (Nat × Nat) := []
  reverted : Bool := false

namespace IRState

def lookupLocal (st : IRState) (name : Ident) : Nat :=
  match st.locals name with
  | some v => v
  | none => 0

def lookupSlot (st : IRState) (slot : Nat) : Nat :=
  match st.slots.find? (·.1 == slot) with
  | some (_, v) => v
  | none => 0

def setLocal (st : IRState) (name : Ident) (v : Nat) : IRState :=
  { st with locals := fun x => if x == name then some v else st.locals x }

def setSlot (st : IRState) (slot : Nat) (v : Nat) : IRState :=
  { st with slots := (slot, v) :: st.slots.filter (·.1 != slot) }

@[simp] theorem lookupLocal_setLocal_same (st : IRState) (name : Ident) (v : Nat) :
    (st.setLocal name v).lookupLocal name = v := by
  simp [lookupLocal, setLocal]

@[simp] theorem lookupLocal_setLocal_ne (st : IRState) (name other : Ident) (v : Nat)
    (hne : name ≠ other) :
    (st.setLocal name v).lookupLocal other = st.lookupLocal other := by
  simp only [lookupLocal, setLocal]
  by_cases h : other == name
  · exact absurd (beq_iff_eq.mp h) hne.symm
  · simp [h]

end IRState

/-- Observable state equality (storage, logs, revert). Locals may differ. -/
def observablyEqual (a b : IRState) : Prop :=
  a.slots = b.slots ∧ a.logs = b.logs ∧ a.reverted = b.reverted

@[simp] theorem observablyEqual_refl (st : IRState) : observablyEqual st st :=
  ⟨rfl, rfl, rfl⟩

def evalExpr (st : IRState) (e : Expr) : Nat :=
  match e with
  | .lit n => n
  | .local name => st.lookupLocal name
  | .sload slot => st.lookupSlot slot
  | .add a b => evalExpr st a + evalExpr st b
  | .sub a b => evalExpr st a - evalExpr st b
  | .lt a b => if evalExpr st a < evalExpr st b then 1 else 0
  | .eq a b => if evalExpr st a == evalExpr st b then 1 else 0
  | .isZero a => if evalExpr st a == 0 then 1 else 0

@[simp] theorem evalExpr_lit (st : IRState) (n : Nat) : evalExpr st (.lit n) = n := rfl

@[simp] theorem evalExpr_local (st : IRState) (name : Ident) :
    evalExpr st (.local name) = st.lookupLocal name := rfl

@[simp] theorem evalExpr_sload (st : IRState) (slot : Nat) :
    evalExpr st (.sload slot) = st.lookupSlot slot := rfl

@[simp] theorem evalExpr_add (st : IRState) (a b : Expr) :
    evalExpr st (.add a b) = evalExpr st a + evalExpr st b := rfl

@[simp] theorem evalExpr_sub (st : IRState) (a b : Expr) :
    evalExpr st (.sub a b) = evalExpr st a - evalExpr st b := rfl

@[simp] theorem evalExpr_lt (st : IRState) (a b : Expr) :
    evalExpr st (.lt a b) = if evalExpr st a < evalExpr st b then 1 else 0 := rfl

@[simp] theorem evalExpr_eq (st : IRState) (a b : Expr) :
    evalExpr st (.eq a b) = if evalExpr st a == evalExpr st b then 1 else 0 := rfl

@[simp] theorem evalExpr_isZero (st : IRState) (a : Expr) :
    evalExpr st (.isZero a) = if evalExpr st a == 0 then 1 else 0 := rfl

def evalStmt (st : IRState) (s : Stmt) : IRState :=
  match s with
  | .skip => st
  | .seq s1 s2 => evalStmt (evalStmt st s1) s2
  | .letBind name e => st.setLocal name (evalExpr st e)
  | .sstore slot e => st.setSlot slot (evalExpr st e)
  | .ifRevert cond =>
    if evalExpr st cond = 1 then { st with reverted := true } else st
  | .log0 topic => { st with logs := st.logs ++ [(topic, 0)] }
  | .log1 topic data => { st with logs := st.logs ++ [(topic, evalExpr st data)] }
  | .revert0 => { st with reverted := true }

@[simp] theorem evalStmt_skip (st : IRState) : evalStmt st .skip = st := rfl

@[simp] theorem evalStmt_seq (st : IRState) (s1 s2 : Stmt) :
    evalStmt st (.seq s1 s2) = evalStmt (evalStmt st s1) s2 := rfl

@[simp] theorem evalStmt_letBind (st : IRState) (name : Ident) (e : Expr) :
    evalStmt st (.letBind name e) = st.setLocal name (evalExpr st e) := rfl

@[simp] theorem evalStmt_sstore (st : IRState) (slot : Nat) (e : Expr) :
    evalStmt st (.sstore slot e) = st.setSlot slot (evalExpr st e) := rfl

@[simp] theorem evalStmt_ifRevert (st : IRState) (cond : Expr) :
    evalStmt st (.ifRevert cond) =
      if evalExpr st cond = 1 then { st with reverted := true } else st := rfl

@[simp] theorem evalStmt_log0 (st : IRState) (topic : Nat) :
    evalStmt st (.log0 topic) = { st with logs := st.logs ++ [(topic, 0)] } := rfl

@[simp] theorem evalStmt_log1 (st : IRState) (topic : Nat) (data : Expr) :
    evalStmt st (.log1 topic data) =
      { st with logs := st.logs ++ [(topic, evalExpr st data)] } := rfl

@[simp] theorem evalStmt_revert0 (st : IRState) : evalStmt st .revert0 = { st with reverted := true } := rfl

end Lsc.Compile.IR
