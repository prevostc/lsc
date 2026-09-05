import Lsc.Compiler.Proof.Core
import Lsc.Examples.Token

set_option linter.unusedSimpArgs false

/-!
`toYulFn_correct_callFree` for every Token runtime entrypoint.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem token_fields_lt : Token.contract.fields.length < wordBound := by
  have h : Token.contract.fields.length = 4 := by simp [Token.contract]
  rw [h]
  exact lt_256_wordBound (by decide)

theorem params_bound_le_three {n : Nat} (h : n ≤ 3) :
    4 + 32 * n < wordBound :=
  lt_256_wordBound (by omega)

theorem token_fn_params_bound {f : FnDef} (hf : f ∈ Token.contract.functions) :
    4 + 32 * f.params.length < wordBound := by
  have hlen : f.params.length ≤ 3 := by
    simp [Token.contract] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact params_bound_le_three hlen

theorem token_fn_not_ctor {f : FnDef} (hf : f ∈ Token.contract.functions) :
    f.kind ≠ .constructor := by
  simp [Token.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem token_fn_callFree {f : FnDef} (hf : f ∈ Token.contract.functions) :
    CallFree f.core := by
  simp [Token.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.transfer.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.approve.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.transferFrom.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.mint.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.burn.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.balanceOf.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.allowance.core]
  · simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Token.totalSupply.core]

/-- `toYulFn_correct` for every runtime function of `Token`. -/
theorem token_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (f : FnDef) (hf : f ∈ Token.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Token.contract f = some yul)
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    ToYulFnCorrect Token.contract Token.schema κ f yul ctx w st0 :=
  toYulFn_correct_callFree (S := Token.Storage) (X := Unit) (E := Token.Event)
    (ε := Token.Error)
    Token.contract Token.schema Token.schema_lawful κ hκ
    f (token_fn_not_ctor hf) (token_fn_callFree hf) token_fields_lt
    (token_fn_params_bound hf) yul hyul ctx w st0 hctx hR

end Lsc.Compiler
