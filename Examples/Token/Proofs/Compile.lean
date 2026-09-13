import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Lsc.Compiler.Bytecode
import Examples.Token.Contract

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-!
Proofs that every Token runtime entrypoint is call-free and compiles
correctly. The exported guarantee is `token_correct` in `Theorems.lean`.
Runtime bytecode exists via `compileRuntime` (erase, else powdr spill).
-/

open Lsc.Compiler

/-- Runtime bytecode exists (`compileRuntime`: erase, else powdr spill). -/
def token_runtime_some : Bool := (compileRuntime Token.contract).isSome

#guard token_runtime_some

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

private theorem m1Frag_withTrue (c : Core .unit) (h : M1Frag c) :
    M1Frag (Token.Core.withTrue c) := by
  match c with
  | .ret _ =>
    simp [Token.Core.withTrue, M1Frag]
  | .stmtTail s =>
    simpa [Token.Core.withTrue, M1Frag] using h
  | .revertTail _ args =>
    simpa [Token.Core.withTrue, M1Frag] using h
  | .letOp op k =>
    simp [Token.Core.withTrue, M1Frag] at h ⊢
    exact ⟨h.1, m1Frag_withTrue k h.2⟩
  | .seq s k =>
    simp [Token.Core.withTrue, M1Frag] at h ⊢
    exact ⟨h.1, m1Frag_withTrue k h.2⟩
  | .letPure p as k =>
    simp [Token.Core.withTrue, M1Frag] at h ⊢
    exact ⟨h.1, h.2.1, m1Frag_withTrue k h.2.2⟩
  | .ite c a b =>
    simp [Token.Core.withTrue, M1Frag] at h ⊢
    exact ⟨h.1, m1Frag_withTrue a h.2.1, m1Frag_withTrue b h.2.2⟩

theorem token_fn_callFree {f : FnDef} (hf : f ∈ Token.contract.functions) :
    CallFree f.core := by
  simp [Token.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1Frag_withTrue Token.transferU.core (by native_decide)
  · exact m1Frag_withTrue Token.transferFromU.core (by native_decide)
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Lsc.Compiler

namespace Lsc.Compiler.Proof

open YulSemantics
open YulSemantics.EVM
open Lsc
open Lsc.Compiler

theorem token_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (f : FnDef) (hf : f ∈ Token.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Token.contract f = some yul)
    (ctx : Ctx) (w : World Token.Storage ExtState Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    ToYulFnCorrect Token.contract Token.schema κ f yul ctx w st0 :=
  toYulFn_correct_callFree (S := Token.Storage) (X := ExtState) (E := Token.Event)
    (ε := Token.Error)
    Token.contract Token.schema Token.schema_lawful κ hκ
    f (token_fn_not_ctor hf) (token_fn_callFree hf) token_fields_lt
    (token_fn_params_bound hf) yul hyul ctx w st0 hctx hR

theorem token_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Token.contract = some yul)
    (ctx : Ctx) (w : World Token.Storage ExtState Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    RuntimeBlockCorrectCallFree Token.contract Token.schema κ yul ctx w st0 :=
  Lsc.Compiler.runtimeBlock_correct_callFree (S := Token.Storage) (X := ExtState)
    (E := Token.Event) (ε := Token.Error)
    Token.contract Token.schema Token.schema_lawful κ hκ
    (fun f hf => token_fn_callFree hf)
    (fun f hf => token_fn_not_ctor hf)
    token_fields_lt
    (fun f hf => token_fn_params_bound hf)
    yul hyul ctx w st0 hctx hR

end Lsc.Compiler.Proof
