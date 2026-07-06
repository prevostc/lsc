import Lsc.Compile.Lower
import Lsc.Compile.IR
import Lsc.TestFixtures.SyntaxSmoke
import Lsc.Lib.Wei.Optimize
import Lsc.Compile.IR.Eval

namespace Lsc.Compile.Correctness

open Lsc.TestFixtures
open Lsc.Compile.IR (IRState evalExpr evalStmt evalStmt_seq evalStmt_letBind evalStmt_ifRevert
  evalExpr_sload evalExpr_add evalExpr_local evalExpr_lit evalExpr_lt)

abbrev IRExpr := Lsc.Compile.IR.Expr
abbrev IRStmt := Lsc.Compile.IR.Stmt

/-! ## IR state correspondence

The IR reference semantics (`IR/Eval.lean`) models storage as a slot list and locals
as `Nat`s. `fromSlots` is the minimal bridge from a concrete slot-0 value (the counter's
`number` field) to an `IRState` ready for `evalStmt`. -/

/-- Minimal `IRState` from a slot list; no locals, logs, or revert. -/
def IRState.fromSlots (slots : List (Nat × Nat)) : IRState :=
  { slots := slots }

@[simp] theorem IRState.lookupSlot_fromSlots_zero (v : Nat) :
    (IRState.fromSlots [(0, v)]).lookupSlot 0 = v := by
  simp [IRState.fromSlots, IRState.lookupSlot]

def counterConfig : Config :=
  { storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  , events := { topic0 := fun _ => none } }

theorem Wei_lower_addCheckedNatStorage_shape :
    Wei.lowerLetBind counterConfig.storage.fieldSlot "n"
        (Wei.addCheckedNatStorage "number" 1) =
      .ok Wei.incrementLetIR := rfl

theorem incrementLet_lowers_ok :
    (Lower.stmt counterConfig incrementLet).isOk := by native_decide

theorem incrementLet_ir_binds_incremented_local :
    let st := evalStmt { slots := [(0, 5)] } Wei.incrementLetIR
    st.lookupLocal "n" = 6 ∧ st.lookupLocal "lsc_n_old" = 5 ∧ ¬ st.reverted := by native_decide

/-- Symbolic version of `incrementLet_ir_binds_incremented_local`: for any slot-0
    value `v`, running `Wei.incrementLetIR` binds `"n" = v + 1`. -/
theorem incrementLet_ir_binds_symbolic (v : Nat) :
    (evalStmt (IRState.fromSlots [(0, v)]) Wei.incrementLetIR).lookupLocal "n" = v + 1 := by
  let st0 := IRState.fromSlots [(0, v)]
  let st1 := st0.setLocal "lsc_n_old" v
  let st2 := st1.setLocal "n" (v + 1)
  have h0 : st0.lookupSlot 0 = v := IRState.lookupSlot_fromSlots_zero v
  have h1 : st1.lookupLocal "lsc_n_old" = v := by
    simp [st1, IRState.lookupLocal_setLocal_same]
  have h2 : st2.lookupLocal "n" = v + 1 := by
    simp [st2, IRState.lookupLocal_setLocal_same]
  have hne : "n" ≠ "lsc_n_old" := by decide
  have h3 : st2.lookupLocal "lsc_n_old" = v := by
    change (st1.setLocal "n" (v + 1)).lookupLocal "lsc_n_old" = v
    simp only [IRState.lookupLocal_setLocal_ne st1 "n" "lsc_n_old" (v + 1) hne, h1]
  have h4 : evalExpr st2 (.lt (.local "n") (.local "lsc_n_old")) = 0 := by
    simp [evalExpr_lt, h2, h3, Nat.not_lt.mpr (Nat.le_add_right v 1)]
  have hs1 : evalStmt st0 (.letBind "lsc_n_old" (.sload 0)) = st1 := by
    simp [evalStmt_letBind, evalExpr_sload, h0, st1]
  have hs2 : evalStmt st1 (.letBind "n" (.add (.local "lsc_n_old") (.lit 1))) = st2 := by
    simp [evalStmt_letBind, evalExpr, st1, st2, h1]
  have hs3 : evalStmt st2 (.ifRevert (.lt (.local "n") (.local "lsc_n_old"))) = st2 := by
    simp [evalStmt_ifRevert, h4]
  have h5 : evalStmt (IRState.fromSlots [(0, v)]) Wei.incrementLetIR = st2 := by
    change evalStmt st0 Wei.incrementLetIR = st2
    dsimp [Wei.incrementLetIR, st1, st2]
    simp [h0]
  simp [h5, h2]

/-- The IR produced by `Wei.lowerLetBind` for `incrementLet` (see
    `Wei_lower_addCheckedNatStorage_shape`) evaluates on slot 0 = `v` to bind local `"n"`
    to the incremented value. Connects the lowering shape lemma to `IR.evalStmt`. -/
theorem incrementLet_lower_preserves_n (v : Nat) :
    (evalStmt (IRState.fromSlots [(0, v)]) Wei.incrementLetIR).lookupLocal "n" = v + 1 :=
  incrementLet_ir_binds_symbolic v

def incrementBody : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementEventConfig : Config :=
  { storage := counterConfig.storage
  , events := { topic0 := fun
      | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
      | _ => none } }

theorem increment_body_lowers_ok :
    Lower.stmt incrementEventConfig incrementBody |>.isOk := by native_decide

end Lsc.Compile.Correctness
