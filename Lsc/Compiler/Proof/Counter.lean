import Lsc.Compiler.Proof.Core
import Lsc.Examples.Counter

/-!
`toYulFn_correct` instances for every Counter runtime entrypoint.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

def incrementFn : FnDef where
  name := "increment"
  decl := ``Counter.increment
  kind := .tx
  params := []
  ret := .unit
  core := Counter.increment.core

def incrementByFn : FnDef where
  name := "incrementBy"
  decl := ``Counter.incrementBy
  kind := .tx
  params := [{ name := "n", ty := .uint256 }]
  ret := .unit
  core := Counter.incrementBy.core

def decrementFn : FnDef where
  name := "decrement"
  decl := ``Counter.decrement
  kind := .tx
  params := []
  ret := .unit
  core := Counter.decrement.core

def getFn : FnDef where
  name := "get"
  decl := ``Counter.get
  kind := .view
  params := []
  ret := .word
  core := Counter.get.core

theorem increment_m1 : M1Frag incrementFn.core := by
  simp [incrementFn, M1Frag, M1Op, M1Stmt, Counter.increment.core]

theorem incrementBy_m1 : M1Frag incrementByFn.core := by
  simp [incrementByFn, M1Frag, M1Op, M1Stmt, M1Cond, Counter.incrementBy.core]

theorem decrement_m1 : M1Frag decrementFn.core := by
  simp [decrementFn, M1Frag, M1Op, M1Stmt, M1Cond, Counter.decrement.core]

theorem get_m1 : M1Frag getFn.core := by
  simp [getFn, M1Frag, M1Op, Counter.get.core]

theorem counter_fields_lt : Counter.contract.fields.length < wordBound := by
  have h : Counter.contract.fields.length = 1 := by
    simp [Counter.contract]
  rw [h]
  exact one_lt_wordBound

theorem params_bound_le_one {n : Nat} (h : n ≤ 1) :
    4 + 32 * n < wordBound :=
  lt_256_wordBound (by omega)

theorem increment_params_bound : 4 + 32 * incrementFn.params.length < wordBound :=
  params_bound_le_one (by simp [incrementFn])

theorem incrementBy_params_bound : 4 + 32 * incrementByFn.params.length < wordBound :=
  params_bound_le_one (by simp [incrementByFn])

theorem decrement_params_bound : 4 + 32 * decrementFn.params.length < wordBound :=
  params_bound_le_one (by simp [decrementFn])

theorem get_params_bound : 4 + 32 * getFn.params.length < wordBound :=
  params_bound_le_one (by simp [getFn])

theorem counter_increment_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementFn yul ctx w st0 :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    incrementFn (by simp [incrementFn]) increment_m1 counter_fields_lt
    increment_params_bound yul hyul ctx w st0 hctx hR

theorem counter_incrementBy_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementByFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementByFn yul ctx w st0 :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    incrementByFn (by simp [incrementByFn]) incrementBy_m1 counter_fields_lt
    incrementBy_params_bound yul hyul ctx w st0 hctx hR

theorem counter_decrement_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract decrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ decrementFn yul ctx w st0 :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    decrementFn (by simp [decrementFn]) decrement_m1 counter_fields_lt
    decrement_params_bound yul hyul ctx w st0 hctx hR

theorem counter_get_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract getFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ getFn yul ctx w st0 :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    getFn (by simp [getFn]) get_m1 counter_fields_lt
    get_params_bound yul hyul ctx w st0 hctx hR

theorem counter_functions :
    Counter.contract.functions = [incrementFn, incrementByFn, decrementFn, getFn] := by
  simp [Counter.contract, incrementFn, incrementByFn, decrementFn, getFn]

theorem counter_fn_m1 {f : FnDef} (hf : f ∈ Counter.contract.functions) :
    M1Frag f.core := by
  simp [counter_functions] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact increment_m1
  · exact incrementBy_m1
  · exact decrement_m1
  · exact get_m1

theorem counter_fn_params_bound {f : FnDef} (hf : f ∈ Counter.contract.functions) :
    4 + 32 * f.params.length < wordBound := by
  simp [counter_functions] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact increment_params_bound
  · exact incrementBy_params_bound
  · exact decrement_params_bound
  · exact get_params_bound

/-- `toYulFn_correct` for every runtime function of `Counter`. -/
theorem counter_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (f : FnDef) (hf : f ∈ Counter.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Counter.contract f = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ f yul ctx w st0 :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    f (by
      simp [counter_functions] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> simp [incrementFn, incrementByFn,
        decrementFn, getFn]) (counter_fn_m1 hf) counter_fields_lt
    (counter_fn_params_bound hf) yul hyul ctx w st0 hctx hR

end Lsc.Compiler
