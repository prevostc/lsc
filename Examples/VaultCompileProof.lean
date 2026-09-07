import Lsc.Compiler.CoreExtSimTheorems
import Examples.Vault
import Lsc.Stdlib.ERC20

set_option linter.unusedSimpArgs false

/-!
Proofs of Vault S2 `toYulFn_correct_ext` instances. Statements live in
`VaultTheorems`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc
open Lsc.Stdlib
open Lsc.Compiler.Proof

theorem vault_previewDeposit_callFree : CallFree Vault.previewDeposit.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.previewDeposit.core]

theorem vault_previewRedeem_callFree : CallFree Vault.previewRedeem.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.previewRedeem.core]

theorem vault_pause_callFree : CallFree Vault.pause.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.pause.core]

theorem vault_unpause_callFree : CallFree Vault.unpause.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.unpause.core]

theorem vault_paused?_callFree : CallFree Vault.paused?.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.paused?.core]

theorem vault_decimals_callFree : CallFree Vault.decimals.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.decimals.core]

theorem vault_fields_lt : Vault.contract.fields.length < wordBound := by
  have h : Vault.contract.fields.length = 7 := by simp [Vault.contract]
  rw [h]
  exact lt_256_wordBound (by decide)

theorem vault_params_bound_le_three {n : Nat} (h : n ≤ 3) :
    4 + 32 * n < wordBound :=
  lt_256_wordBound (by omega)

theorem vault_fn_params_bound {f : FnDef} (hf : f ∈ Vault.contract.functions) :
    4 + 32 * f.params.length < wordBound := by
  have hlen : f.params.length ≤ 3 := by
    simp [Vault.contract] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact vault_params_bound_le_three hlen

theorem vault_fn_not_ctor {f : FnDef} (hf : f ∈ Vault.contract.functions) :
    f.kind ≠ .constructor := by
  simp [Vault.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem vault_fn_s2 {f : FnDef} (hf : f ∈ Vault.contract.functions) :
    S2Frag f.core := by
  simp [Vault.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Vault.deposit.core]
  · simp [S2Frag, S2Op, S2Stmt, M1Op, M1Stmt, M1Cond, Vault.withdraw.core]
  · exact s2frag_of_callFree vault_previewDeposit_callFree
  · exact s2frag_of_callFree vault_previewRedeem_callFree
  · exact s2frag_of_callFree vault_pause_callFree
  · exact s2frag_of_callFree vault_unpause_callFree
  · exact s2frag_of_callFree vault_paused?_callFree
  · exact s2frag_of_callFree vault_decimals_callFree

theorem vault_scalar_asset (σ : Vault.Storage) :
    Vault.schema.st.scalar 5 σ = Vault.assetB.addr σ := by
  simp [Vault.schema, Vault.assetB]
  rfl

theorem vault_field_asset :
    (Vault.contract.fields[5]?).map (·.kind) = some FieldKind.scalar := by
  simp [Vault.contract]

theorem vault_fn_avoids {f : FnDef} (hf : f ∈ Vault.contract.functions) :
    coreAvoids 5 f.core := by
  simp [Vault.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [coreAvoids, stmtAvoids, Vault.deposit.core]
  · simp [coreAvoids, stmtAvoids, Vault.withdraw.core]
  · simp [coreAvoids, stmtAvoids, Vault.previewDeposit.core]
  · simp [coreAvoids, stmtAvoids, Vault.previewRedeem.core]
  · simp [coreAvoids, stmtAvoids, Vault.pause.core]
  · simp [coreAvoids, stmtAvoids, Vault.unpause.core]
  · simp [coreAvoids, stmtAvoids, Vault.paused?.core]
  · simp [coreAvoids, stmtAvoids, Vault.decimals.core]

theorem vault_hslot {f : FnDef} (hf : f ∈ Vault.contract.functions) :
    ∃ slot : Nat,
      (∀ σ, Vault.schema.st.scalar slot σ = Vault.assetB.addr σ) ∧
      (Vault.contract.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
      coreAvoids slot f.core :=
  ⟨5, vault_scalar_asset, vault_field_asset, vault_fn_avoids hf⟩

private def vaultAssetBd : BindingDef where
  name := "assetB"
  fieldSlot := 5
  ifaceName := "IERC20"
  methods := [
    ("transfer", { selector := 0xa9059cbb, arity := 2, ret := .boolOpt }),
    ("transferFrom", { selector := 0x23b872dd, arity := 3, ret := .boolOpt }),
    ("balanceOf", { selector := 0x70a08231, arity := 1, ret := .word }),
    ("decimals", { selector := 0x313ce567, arity := 0, ret := .word })]

theorem vault_bindings_asset : Vault.contract.bindings[0]? = some vaultAssetBd := by
  simp [Vault.contract, vaultAssetBd]

theorem vault_ext_transfer (args : List Nat) :
    Vault.schema.ext.call 0 0 args = Tx.call Vault.assetB Method.transfer args := by
  simp [Vault.schema, IERC20, Method.equivFin, Method.ofFin]

theorem vault_ext_transferFrom (args : List Nat) :
    Vault.schema.ext.call 0 1 args = Tx.call Vault.assetB Method.transferFrom args := by
  simp [Vault.schema, IERC20, Method.equivFin, Method.ofFin]

theorem vault_ext_balanceOf (args : List Nat) :
    Vault.schema.ext.call 0 2 args = Tx.call Vault.assetB Method.balanceOf args := by
  simp [Vault.schema, IERC20, Method.equivFin, Method.ofFin]

theorem vault_ext_decimals (args : List Nat) :
    Vault.schema.ext.call 0 3 args = Tx.call Vault.assetB Method.decimals args := by
  simp [Vault.schema, IERC20, Method.equivFin, Method.ofFin]

theorem vault_bindWF_transfer :
    BindWF Vault.contract Vault.schema Vault.assetB 0 0 Method.transfer where
  lookup :=
    ⟨vaultAssetBd, vault_bindings_asset, by simp [vaultAssetBd]; rfl,
      vault_scalar_asset, vault_field_asset⟩
  hgetset := fun _ _ => rfl
  hext := vault_ext_transfer
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transfer
  harity := IERC20.abi_arity_le_3 Method.transfer

theorem vault_bindWF_transferFrom :
    BindWF Vault.contract Vault.schema Vault.assetB 0 1 Method.transferFrom where
  lookup :=
    ⟨vaultAssetBd, vault_bindings_asset, by simp [vaultAssetBd]; rfl,
      vault_scalar_asset, vault_field_asset⟩
  hgetset := fun _ _ => rfl
  hext := vault_ext_transferFrom
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inr IERC20.abi_ret_transferFrom
  harity := IERC20.abi_arity_le_3 Method.transferFrom

theorem vault_bindWF_balanceOf :
    BindWF Vault.contract Vault.schema Vault.assetB 0 2 Method.balanceOf where
  lookup :=
    ⟨vaultAssetBd, vault_bindings_asset, by simp [vaultAssetBd]; rfl,
      vault_scalar_asset, vault_field_asset⟩
  hgetset := fun _ _ => rfl
  hext := vault_ext_balanceOf
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.balanceOf

theorem vault_bindWF_decimals :
    BindWF Vault.contract Vault.schema Vault.assetB 0 3 Method.decimals where
  lookup :=
    ⟨vaultAssetBd, vault_bindings_asset, by simp [vaultAssetBd]; rfl,
      vault_scalar_asset, vault_field_asset⟩
  hgetset := fun _ _ => rfl
  hext := vault_ext_decimals
  hsel := IERC20.abi_sel_lt
  huniq := fun _ h => IERC20.abi_selector_inj h
  hret := Or.inl rfl
  harity := IERC20.abi_arity_le_3 Method.decimals

theorem vault_bindWF (b m : Nat) (args : List Atom)
    (hwf : callWF Vault.contract b m args = true) :
    ∃ meth, BindWF Vault.contract Vault.schema Vault.assetB b m meth := by
  cases b with
  | succ b =>
    simp [callWF, Vault.contract] at hwf
  | zero =>
    cases m with
    | zero => exact ⟨Method.transfer, vault_bindWF_transfer⟩
    | succ m =>
      cases m with
      | zero => exact ⟨Method.transferFrom, vault_bindWF_transferFrom⟩
      | succ m =>
        cases m with
        | zero => exact ⟨Method.balanceOf, vault_bindWF_balanceOf⟩
        | succ m =>
          cases m with
          | zero => exact ⟨Method.decimals, vault_bindWF_decimals⟩
          | succ m => simp [callWF, Vault.contract] at hwf

namespace Proof

/-- `toYulFn_correct_ext` for every runtime function of `Vault`. -/
theorem vault_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Vault.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Vault.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Vault.contract f = some yul)
    (ctx : Ctx) (w : World Vault.Storage Vault.Ext Vault.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Vault.contract Vault.schema κ w st0)
    (hRX : RX α Vault.assetB w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α) :
    ToYulFnCorrectExt α Vault.assetB Vault.contract Vault.schema κ calls f yul ctx w st0 :=
  Lsc.Compiler.toYulFn_correct_ext_one (I := IERC20) (S := Vault.Storage) (X := Vault.Ext)
    (E := Vault.Event) (ε := Vault.Error)
    α Vault.assetB Vault.contract Vault.schema Vault.schema_lawful κ hκ
    calls f (vault_fn_not_ctor hf) (vault_fn_s2 hf) vault_fields_lt
    (vault_fn_params_bound hf) yul hyul ctx w st0 hctx hR hRX hign hBindNe hconf
    vault_bindWF (vault_hslot hf)

end Proof

theorem vault_deposit_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Vault.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Vault.contract.functions)
    (_hname : f.name = "deposit")
    (yul : YBlock) (hyul : toYulFn Vault.contract f = some yul)
    (ctx : Ctx) (w : World Vault.Storage Vault.Ext Vault.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Vault.contract Vault.schema κ w st0)
    (hRX : RX α Vault.assetB w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α) :
    ToYulFnCorrectExt α Vault.assetB Vault.contract Vault.schema κ calls f yul ctx w st0 :=
  vault_correct_ext α κ hκ calls f hf (vault_fn_not_ctor hf) yul hyul
    ctx w st0 hctx hR hRX hign hBindNe hconf

theorem vault_withdraw_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Vault.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Vault.contract.functions)
    (_hname : f.name = "withdraw")
    (yul : YBlock) (hyul : toYulFn Vault.contract f = some yul)
    (ctx : Ctx) (w : World Vault.Storage Vault.Ext Vault.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Vault.contract Vault.schema κ w st0)
    (hRX : RX α Vault.assetB w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α) :
    ToYulFnCorrectExt α Vault.assetB Vault.contract Vault.schema κ calls f yul ctx w st0 :=
  vault_correct_ext α κ hκ calls f hf (vault_fn_not_ctor hf) yul hyul
    ctx w st0 hctx hR hRX hign hBindNe hconf

end Lsc.Compiler
