import Lsc.Compiler.CoreExtSimTheorems
import Examples.Amm.Spec
import Examples.Amm.Contract
import Stdlib.ERC20

set_option linter.unusedSimpArgs false

/-!
Proofs of AMM S2 `toYulFn_correct_ext` instances. Statements live in `Theorems.lean`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc
open Lsc.Stdlib

theorem amm_getReserves_callFree : CallFree Amm.getReserves.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Amm.getReserves.core]

theorem amm_sharesOf_callFree : CallFree Amm.sharesOf.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Amm.sharesOf.core]

theorem amm_quote0for1_callFree : CallFree Amm.quote0for1.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Amm.quote0for1.core]

theorem amm_fields_lt : Amm.contract.fields.length < wordBound := by
  have h : Amm.contract.fields.length = 8 := by simp [Amm.contract]
  rw [h]
  exact lt_256_wordBound (by decide)

theorem amm_params_bound_le_two {n : Nat} (h : n ≤ 2) :
    4 + 32 * n < wordBound :=
  lt_256_wordBound (by omega)

theorem amm_fn_params_bound {f : FnDef} (hf : f ∈ Amm.contract.functions) :
    4 + 32 * f.params.length < wordBound := by
  have hlen : f.params.length ≤ 2 := by
    simp [Amm.contract] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact amm_params_bound_le_two hlen

theorem amm_fn_not_ctor {f : FnDef} (hf : f ∈ Amm.contract.functions) :
    f.kind ≠ .constructor := by
  simp [Amm.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem amm_fn_s2 {f : FnDef} (hf : f ∈ Amm.contract.functions) :
    S2Frag f.core := by
  simp [Amm.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Amm.addLiquidity.core]
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Amm.removeLiquidity.core]
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Amm.swap0for1.core]
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Amm.swap1for0.core]
  · exact s2frag_of_callFree amm_getReserves_callFree
  · exact s2frag_of_callFree amm_sharesOf_callFree
  · exact s2frag_of_callFree amm_quote0for1_callFree

theorem amm_scalar_token0 (σ : Amm.Storage) :
    Amm.schema.st.scalar 4 σ = Amm.token0B.addr σ := by
  simp [Amm.schema, Amm.token0B]
  rfl

theorem amm_scalar_token1 (σ : Amm.Storage) :
    Amm.schema.st.scalar 5 σ = Amm.token1B.addr σ := by
  simp [Amm.schema, Amm.token1B]
  rfl

theorem amm_field_token0 :
    (Amm.contract.fields[4]?).map (·.kind) = some FieldKind.scalar := by
  simp [Amm.contract]

theorem amm_field_token1 :
    (Amm.contract.fields[5]?).map (·.kind) = some FieldKind.scalar := by
  simp [Amm.contract]

theorem amm_fn_avoids0 {f : FnDef} (hf : f ∈ Amm.contract.functions) :
    coreAvoids 4 f.core := by
  simp [Amm.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [coreAvoids, stmtAvoids, Amm.addLiquidity.core]
  · simp [coreAvoids, stmtAvoids, Amm.removeLiquidity.core]
  · simp [coreAvoids, stmtAvoids, Amm.swap0for1.core]
  · simp [coreAvoids, stmtAvoids, Amm.swap1for0.core]
  · simp [coreAvoids, stmtAvoids, Amm.getReserves.core]
  · simp [coreAvoids, stmtAvoids, Amm.sharesOf.core]
  · simp [coreAvoids, stmtAvoids, Amm.quote0for1.core]

theorem amm_fn_avoids1 {f : FnDef} (hf : f ∈ Amm.contract.functions) :
    coreAvoids 5 f.core := by
  simp [Amm.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [coreAvoids, stmtAvoids, Amm.addLiquidity.core]
  · simp [coreAvoids, stmtAvoids, Amm.removeLiquidity.core]
  · simp [coreAvoids, stmtAvoids, Amm.swap0for1.core]
  · simp [coreAvoids, stmtAvoids, Amm.swap1for0.core]
  · simp [coreAvoids, stmtAvoids, Amm.getReserves.core]
  · simp [coreAvoids, stmtAvoids, Amm.sharesOf.core]
  · simp [coreAvoids, stmtAvoids, Amm.quote0for1.core]

theorem amm_hslot (α : Abs IERC20.Ghost) {f : FnDef}
    (hf : f ∈ Amm.contract.functions) :
    BindEnvs.avoids Amm.schema Amm.contract (ammBs α) f.core := by
  intro e he
  have : e = ⟨α, Amm.token0B⟩ ∨ e = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using he
  rcases this with rfl | rfl
  · exact ⟨4, amm_scalar_token0, amm_field_token0, amm_fn_avoids0 hf⟩
  · exact ⟨5, amm_scalar_token1, amm_field_token1, amm_fn_avoids1 hf⟩

private def ierc20Methods : List (String × AbiSpec) := [
  ("transfer", { selector := 0xa9059cbb, arity := 2, ret := .boolOpt }),
  ("transferFrom", { selector := 0x23b872dd, arity := 3, ret := .boolOpt }),
  ("balanceOf", { selector := 0x70a08231, arity := 1, ret := .word }),
  ("decimals", { selector := 0x313ce567, arity := 0, ret := .word })]

private def ammToken0Bd : BindingDef where
  name := "token0B"
  fieldSlot := 4
  ifaceName := "IERC20"
  methods := ierc20Methods

private def ammToken1Bd : BindingDef where
  name := "token1B"
  fieldSlot := 5
  ifaceName := "IERC20"
  methods := ierc20Methods

theorem amm_bindings_token0 : Amm.contract.bindings[0]? = some ammToken0Bd := by
  simp [Amm.contract, ammToken0Bd, ierc20Methods]

theorem amm_bindings_token1 : Amm.contract.bindings[1]? = some ammToken1Bd := by
  simp [Amm.contract, ammToken1Bd, ierc20Methods]

theorem amm_ext_t0_transfer (args : List Nat) :
    Amm.schema.ext.call 0 0 args = Tx.call Amm.token0B Method.transfer args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t0_transferFrom (args : List Nat) :
    Amm.schema.ext.call 0 1 args = Tx.call Amm.token0B Method.transferFrom args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t0_balanceOf (args : List Nat) :
    Amm.schema.ext.call 0 2 args = Tx.call Amm.token0B Method.balanceOf args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t0_decimals (args : List Nat) :
    Amm.schema.ext.call 0 3 args = Tx.call Amm.token0B Method.decimals args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t1_transfer (args : List Nat) :
    Amm.schema.ext.call 1 0 args = Tx.call Amm.token1B Method.transfer args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t1_transferFrom (args : List Nat) :
    Amm.schema.ext.call 1 1 args = Tx.call Amm.token1B Method.transferFrom args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t1_balanceOf (args : List Nat) :
    Amm.schema.ext.call 1 2 args = Tx.call Amm.token1B Method.balanceOf args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_ext_t1_decimals (args : List Nat) :
    Amm.schema.ext.call 1 3 args = Tx.call Amm.token1B Method.decimals args := by
  simp [Amm.schema, IERC20, Method.equivFin, Method.ofFin]

theorem amm_bindWF_t0_transfer :
    BindWF Amm.contract Amm.schema Amm.token0B 0 0 Method.transfer where
  lookup :=
    ⟨ammToken0Bd, amm_bindings_token0, by simp [ammToken0Bd, ierc20Methods]; rfl,
      amm_scalar_token0, amm_field_token0⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t0_transfer
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transfer
  harity := IERC20.abi_arity_le_3 Method.transfer

theorem amm_bindWF_t0_transferFrom :
    BindWF Amm.contract Amm.schema Amm.token0B 0 1 Method.transferFrom where
  lookup :=
    ⟨ammToken0Bd, amm_bindings_token0, by simp [ammToken0Bd, ierc20Methods]; rfl,
      amm_scalar_token0, amm_field_token0⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t0_transferFrom
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transferFrom
  harity := IERC20.abi_arity_le_3 Method.transferFrom

theorem amm_bindWF_t0_balanceOf :
    BindWF Amm.contract Amm.schema Amm.token0B 0 2 Method.balanceOf where
  lookup :=
    ⟨ammToken0Bd, amm_bindings_token0, by simp [ammToken0Bd, ierc20Methods]; rfl,
      amm_scalar_token0, amm_field_token0⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t0_balanceOf
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.balanceOf

theorem amm_bindWF_t0_decimals :
    BindWF Amm.contract Amm.schema Amm.token0B 0 3 Method.decimals where
  lookup :=
    ⟨ammToken0Bd, amm_bindings_token0, by simp [ammToken0Bd, ierc20Methods]; rfl,
      amm_scalar_token0, amm_field_token0⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t0_decimals
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.decimals

theorem amm_bindWF_t1_transfer :
    BindWF Amm.contract Amm.schema Amm.token1B 1 0 Method.transfer where
  lookup :=
    ⟨ammToken1Bd, amm_bindings_token1, by simp [ammToken1Bd, ierc20Methods]; rfl,
      amm_scalar_token1, amm_field_token1⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t1_transfer
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transfer
  harity := IERC20.abi_arity_le_3 Method.transfer

theorem amm_bindWF_t1_transferFrom :
    BindWF Amm.contract Amm.schema Amm.token1B 1 1 Method.transferFrom where
  lookup :=
    ⟨ammToken1Bd, amm_bindings_token1, by simp [ammToken1Bd, ierc20Methods]; rfl,
      amm_scalar_token1, amm_field_token1⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t1_transferFrom
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transferFrom
  harity := IERC20.abi_arity_le_3 Method.transferFrom

theorem amm_bindWF_t1_balanceOf :
    BindWF Amm.contract Amm.schema Amm.token1B 1 2 Method.balanceOf where
  lookup :=
    ⟨ammToken1Bd, amm_bindings_token1, by simp [ammToken1Bd, ierc20Methods]; rfl,
      amm_scalar_token1, amm_field_token1⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t1_balanceOf
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.balanceOf

theorem amm_bindWF_t1_decimals :
    BindWF Amm.contract Amm.schema Amm.token1B 1 3 Method.decimals where
  lookup :=
    ⟨ammToken1Bd, amm_bindings_token1, by simp [ammToken1Bd, ierc20Methods]; rfl,
      amm_scalar_token1, amm_field_token1⟩
  hgetset := fun _ _ => rfl
  hext := amm_ext_t1_decimals
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.decimals

theorem amm_lookupWF (α : Abs IERC20.Ghost) :
    BindEnvs.lookupWF Amm.contract Amm.schema (ammBs α) := by
  intro b m args hwf
  cases b with
  | succ b =>
    cases b with
    | zero =>
      cases m with
      | zero =>
        exact ⟨⟨α, Amm.token1B⟩, by simp [ammBs], Method.transfer, amm_bindWF_t1_transfer⟩
      | succ m =>
        cases m with
        | zero =>
          exact ⟨⟨α, Amm.token1B⟩, by simp [ammBs], Method.transferFrom,
            amm_bindWF_t1_transferFrom⟩
        | succ m =>
          cases m with
          | zero =>
            exact ⟨⟨α, Amm.token1B⟩, by simp [ammBs], Method.balanceOf,
              amm_bindWF_t1_balanceOf⟩
          | succ m =>
            cases m with
            | zero =>
              exact ⟨⟨α, Amm.token1B⟩, by simp [ammBs], Method.decimals,
                amm_bindWF_t1_decimals⟩
            | succ m => simp [callWF, Amm.contract] at hwf
    | succ _ => simp [callWF, Amm.contract] at hwf
  | zero =>
    cases m with
    | zero =>
      exact ⟨⟨α, Amm.token0B⟩, by simp [ammBs], Method.transfer, amm_bindWF_t0_transfer⟩
    | succ m =>
      cases m with
      | zero =>
        exact ⟨⟨α, Amm.token0B⟩, by simp [ammBs], Method.transferFrom,
          amm_bindWF_t0_transferFrom⟩
      | succ m =>
        cases m with
        | zero =>
          exact ⟨⟨α, Amm.token0B⟩, by simp [ammBs], Method.balanceOf,
            amm_bindWF_t0_balanceOf⟩
        | succ m =>
          cases m with
          | zero =>
            exact ⟨⟨α, Amm.token0B⟩, by simp [ammBs], Method.decimals,
              amm_bindWF_t0_decimals⟩
          | succ m => simp [callWF, Amm.contract] at hwf

theorem amm_sameAbs (α : Abs IERC20.Ghost) : BindEnvs.sameAbs (ammBs α) := by
  intro e1 h1 e2 h2
  have h1' : e1 = ⟨α, Amm.token0B⟩ ∨ e1 = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using h1
  have h2' : e2 = ⟨α, Amm.token0B⟩ ∨ e2 = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using h2
  rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl <;> rfl

theorem amm_orthogonal (α : Abs IERC20.Ghost) : BindEnvs.orthogonal (ammBs α) := by
  intro e1 h1 e2 h2 σ hne x g
  have h1' : e1 = ⟨α, Amm.token0B⟩ ∨ e1 = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using h1
  have h2' : e2 = ⟨α, Amm.token0B⟩ ∨ e2 = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using h2
  rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
  · exact (hne rfl).elim
  · rfl
  · rfl
  · exact (hne rfl).elim

theorem amm_ignoresLocal (α : Abs IERC20.Ghost) (h : α.ignoresLocal) :
    BindEnvs.ignoresLocal (ammBs α) := by
  intro e he
  have : e = ⟨α, Amm.token0B⟩ ∨ e = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using he
  rcases this with rfl | rfl <;> exact h

theorem amm_ofState_foreign (α : Abs IERC20.Ghost) (h : α.ofState_foreign) :
    BindEnvs.ofState_foreign (ammBs α) := by
  intro e he
  have : e = ⟨α, Amm.token0B⟩ ∨ e = ⟨α, Amm.token1B⟩ := by
    simpa [ammBs, List.mem_cons, List.mem_singleton] using he
  rcases this with rfl | rfl <;> exact h

namespace Proof

/-- `toYulFn_correct_ext` for every runtime function of `Amm`. -/
theorem amm_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Amm.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Amm.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Amm.contract f = some yul)
    (ctx : Ctx) (w : World Amm.Storage Amm.Ext Amm.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Amm.contract Amm.schema κ w st0)
    (hRX : RXs (ammBs α) w st0) (hign : α.ignoresLocal)
    (hBindNe : BindEnvs.neSelf (ammBs α) ctx.self w.self)
    (hconf : BindEnvs.conforms (ammBs α) ctx.self w.self calls)
    (hinj : BindEnvs.addrInj (ammBs α) w.self) :
    ToYulFnCorrectExts (ammBs α) Amm.contract Amm.schema κ calls f yul ctx w st0 :=
  toYulFn_correct_ext (I := IERC20) (S := Amm.Storage) (X := Amm.Ext)
    (E := Amm.Event) (ε := Amm.Error)
    (ammBs α) Amm.contract Amm.schema Amm.schema_lawful κ hκ
    calls f (amm_fn_not_ctor hf) (amm_fn_s2 hf) amm_fields_lt
    (amm_fn_params_bound hf) yul hyul ctx w st0 hctx hR hRX
    (amm_ignoresLocal α hign) hBindNe hconf (amm_sameAbs α) (amm_orthogonal α)
    hinj (amm_lookupWF α) (amm_hslot α hf)

end Proof

end Lsc.Compiler
