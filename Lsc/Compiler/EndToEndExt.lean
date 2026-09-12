import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.EndToEndExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.ExtOracleTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
S2 glue helpers: composition of `bytecode_call_correct_ext` into a single
`EvmCallRunξ`, and `mkEvmStateExt` framing for `RX`. Exported guarantees
live in `EndToEndExtTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

theorem evmCallRun_of_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self (toCalls o))
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match selectedFn c yst0.env.calldata with
        | none => σ' = yst0.storage ∧ ξ' = evmForeign yst0
        | some f =>
            match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
                ctx { w with faults := fo } with
            | .ok (_, w') =>
                storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
                  ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                    RXs bs w' stObs
            | .error _ => σ' = yst0.storage ∧ ξ' = evmForeign yst0 := by
  obtain ⟨st', out, hrun⟩ :=
    yul_progress (I := I) bs c Γ hΓ evmKeccak hκ (toCalls o) (toCalls_total o)
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hconf hBind hslot
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext (I := I) bs c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot himm0
      st' out hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, hEvm, ?_⟩
  obtain ⟨fo, hconcl⟩ := hpred
  refine ⟨fo, ?_⟩
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    rcases hconcl with ⟨_, ⟨hh, _⟩⟩
    exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
        ctx { w with faults := fo } with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨_, hsucc, hR', hRX'⟩
      exact ⟨hR'.1, hR'.2.2.2, stObs, rfl, rfl, hRX'⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

theorem mkEvmStateExt_foreign_ne (cd σ ξ κ ctx a)
    (hne : accountKey a ≠ accountKey (BitVec.ofNat 256 ctx.self)) :
    evmForeign (mkEvmStateExt cd σ ξ κ ctx) a = ξ a := by
  funext slot
  simp [mkEvmStateExt_foreign, hne]

theorem RX_mkEvmStateExt_ne {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} (hF : α.ofState_foreign)
    {w : World S X E} {st : EvmState} {cd σ ξ κ ctx}
    (hRX : RX α bind w st) (hξ : ξ = evmForeign st)
    (hne : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
           accountKey (BitVec.ofNat 256 ctx.self)) :
    RX α bind w (mkEvmStateExt cd σ ξ κ ctx) :=
  RX_of_foreign hF (fun k => by rw [mkEvmStateExt_foreign, hξ, if_neg hne]) hRX

theorem RX_mkEvmStateExt_ctx {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} (hF : α.ofState_foreign)
    {w : World S X E} {cd cd' σ ξ κ ctx ctx'}
    (hself : ctx.self = ctx'.self)
    (hRX : RX α bind w (mkEvmStateExt cd σ ξ κ ctx)) :
    RX α bind w (mkEvmStateExt cd' σ ξ κ ctx') :=
  RX_of_foreign hF (fun k => by
    simp only [mkEvmStateExt_foreign, hself]) hRX

theorem RXs_mkEvmStateExt_ne {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    (hF : BindEnvs.ofState_foreign bs)
    {w : World S X E} {st : EvmState} {cd σ ξ κ ctx}
    (hRX : RXs bs w st) (hξ : ξ = evmForeign st)
    (hne : BindEnvs.neSelf bs ctx.self w.self) :
    RXs bs w (mkEvmStateExt cd σ ξ κ ctx) := by
  intro e he
  exact RX_mkEvmStateExt_ne (hF e he) (hRX e he) hξ (hne e he)

theorem RXs_mkEvmStateExt_ctx {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    (hF : BindEnvs.ofState_foreign bs)
    {w : World S X E} {cd cd' σ ξ κ ctx ctx'}
    (hself : ctx.self = ctx'.self)
    (hRX : RXs bs w (mkEvmStateExt cd σ ξ κ ctx)) :
    RXs bs w (mkEvmStateExt cd' σ ξ κ ctx') := by
  intro e he
  exact RX_mkEvmStateExt_ctx (hF e he) hself (hRX e he)

/-- Drop the `EvmStartOK` witness; `ExtAll` is a stricter `EvmTraceRunExt`.
The converse needs a start state for every call, which `EvmTraceRunExt` does not store. -/
theorem EvmTraceRunExt_of_ExtAll {is : List Instr}
    {tr : List EvmCall} {σ ξ σ' ξ'}
    (h : EvmTraceRunExtAll is tr σ ξ σ' ξ') :
    EvmTraceRunExt is tr σ ξ σ' ξ' := by
  induction h with
  | nil => exact .nil _ _
  | cons hstart h1 htl ih => exact .cons h1 ih

theorem evmCallRun_fnCalldata_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (hign : BindEnvs.ignoresLocal bs)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (ctx : Ctx) (f : FnDef) (args : List Nat) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hf : f ∈ c.functions) (hk : f.kind ≠ .constructor)
    (hlenA : args.length = f.params.length)
    (hW : ∀ n ∈ args, n < wordBound)
    (hctxWF : CtxWF ctx)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcd : (fnCalldata f args).length < wordBound)
    (hRX : RXs bs w (mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx))
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self (toCalls o))
    (hinj : BindEnvs.addrInj bs w.self) :
    let yst0 := mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match Tx.run (Core.denote Γ f.core args.reverse) ctx { w with faults := fo } with
        | .ok (_, w') =>
            storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
              ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                RXs bs w' stObs
        | .error _ => σ' = σ ∧ ξ' = evmForeign yst0 := by
  intro yst0
  have hsel : selectedFn c (fnCalldata f args) = some f :=
    selectedFn_fnCalldata c f args hf hnd hlenA
  have hdec : decodeArgs f (fnCalldata f args) = args :=
    decodeArgs_fnCalldata f args hk hlenA hW
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R c Γ evmKeccak w yst0 := R_mkEvmStateExt evmKeccak w _ σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  obtain ⟨σ', ξ', hRun, fo, hpost⟩ :=
    evmCallRun_of_correct_ext (I := I) bs c Γ hΓ hκ o hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
      hsame horth hinj hBind hslot himm0
  refine ⟨σ', ξ', hRun, fo, ?_⟩
  rw [mkEvmStateExt_calldata] at hpost
  simp only [hsel] at hpost
  rw [hdec] at hpost
  rw [show yst0.storage = σ from mkEvmStateExt_storage _ _ _ _ _] at hpost
  exact hpost

end Lsc.Compiler
