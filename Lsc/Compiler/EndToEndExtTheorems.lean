import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.EndToEndExtProof

set_option linter.unusedVariables false

/-!
S2 bytecode glue: compiled runtime that may `CALL`, related to Core under a
fault oracle and to EVM `Steps` by powdr `compile_correct`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- Every Yul `Run` of a compiled S2 runtime is predicted by `Core.denote`
under some fault oracle, and powdr produces matching EVM `Steps`. Every
halted matching EVM execution agrees on post-storage and on foreign
account storage. Assumes the binding family (`Conforms`, `RXs`, address
separation, `lookupWF` / `avoids`), `CallsRealized`, and that the compiler
accepted the contract. This is the S2 analogue of `bytecode_call_correct`
used by Vault and AMM. -/
theorem bytecode_call_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt bs c Γ evmKeccak calls ctx w yst0 rt is :=
  Proof.bytecode_call_correct_ext (I := I) bs c Γ hΓ hκ calls hCalls hctor hS2
    hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
    hsame horth hinj hBind hslot himm0

/-- `CallsTotal` produces a Yul `Run` (`yul_progress`). Combined with
`bytecode_call_correct_ext` and EVM uniqueness of halted frames, every
matching EVM execution has the unique post-storage (and foreign storage)
Core predicts. Without a total CALL oracle the universal statement could
hold vacuously because powdr `compile_correct` is only forward. -/
theorem evmCallRunExtAll_of_progress {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RXs bs w yst0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunExtAll bs c Γ evmKeccak calls ctx w is yst0 σ' ξ' :=
  Proof.evmCallRunExtAll_of_progress (I := I) bs c Γ hΓ hκ calls hCalls htot
    hctor hS2 hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe
    hconf hsame horth hinj hBind hslot himm0

end Lsc.Compiler
