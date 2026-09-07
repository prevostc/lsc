import Lsc.Compiler.EndToEnd
import Lsc.Compiler.EndToEndProof

set_option linter.unusedVariables false

/-!
Call-free bytecode: compiled runtime related to the high-level model by
the dispatcher, and to EVM steps by the pinned Yul-to-EVM compiler.

Shared assumptions: the compiler accepted the contract, the layout is
lawful, keccak keys do not collide, there are no CALLs, constructors
are excluded, and the frame has enough gas. Token instantiates this.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- A compiled call-free runtime, started from a matching EVM frame with
enough gas, ends in a halt whose return data and storage are those of
the high-level model on the selected function — or an empty revert if
the selector is unknown. The compiler must have accepted the contract
(`compileBlock`: erase or powdr spill); there are no CALLs; constructors
are excluded. This is the step that
carries a call-free Yul run down to bytecode; Token's anti-extraction
theorems instantiate it. -/
theorem bytecode_call_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is :=
  Proof.bytecode_call_correct c Γ hΓ hκ hcf hctor hlen hbound rt hrt is hcomp
    ctx w yst0 hctx hR himm0

/-- After any halted sequence of well-formed EVM calls against compiled
call-free runtime, the ending storage is exactly the storage the
high-level model predicts for those calls, and stored values still fit
in a word. Each hop needs a matching start state so halted runs are
unique; without that, two EVM runs of the same bytecode could disagree.
Unknown selectors are not in this statement — it is about decoded
functions. Token uses this to move a Core-level claim from start
storage to end storage. -/
theorem bytecode_trace_all {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
