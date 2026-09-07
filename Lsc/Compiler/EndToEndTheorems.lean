import Lsc.Compiler.EndToEnd
import Lsc.Compiler.EndToEndProof

set_option linter.unusedVariables false

/-!
S1 bytecode glue: compiled call-free runtime, related to Core by the
dispatcher, related to EVM `Steps` by powdr `compile_correct`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- A compiled call-free runtime, started from a matching EVM frame with
enough gas, ends in a halt whose return data and storage are those of
`Core.denote` on the selected ABI function (or an empty revert if the
selector is unknown). Assumes the compiler accepted the contract
(`runtimeBlock` / `compile`), a lawful layout, keccak-separated keys, and
a closed external model (no `CALL`). This is the S1 link from Yul `Run` to
bytecode that Token's anti-exploit theorems instantiate. -/
theorem bytecode_call_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is :=
  Proof.bytecode_call_correct c Γ hΓ hκ hcf hctor hlen hbound rt hrt is hcomp
    ctx w yst0 hctx hR himm0

/-- If every call in a sequence has a matching EVM start state
(`EvmTraceRunAll`), the final storage is `storageRel` of folding
`Core.denote` along that sequence (`coreRun`). Each hop needs a start
state so halted `Steps` are unique; without that, two EVM runs of the
same bytecode could disagree. Token bytecode security uses this to move
a Core-level claim from `σ` to `σ'`. -/
theorem bytecode_trace_all {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound)
    (hE : EvmTraceRunAll is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ') :
    storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
    WorldWF c Γ (coreRun Γ calls { w with log := [] }) :=
  Proof.bytecode_trace_all c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp
    calls w σ σ' hs hlog hwf hcalls hE

end Lsc.Compiler
