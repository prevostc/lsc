import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.EndToEndExtProof
import Lsc.Compiler.ExtOracle

set_option linter.unusedVariables false

/-!
Bytecode for contracts that CALL out: compiled runtime related to the
high-level model under some choice of which external calls fail, and
to EVM steps by the pinned Yul-to-EVM compiler.

Shared assumptions: bound tokens conform to their interface, are not
this contract, and do not alias each other; the compiler accepted the
contract; given enough gas. Other contracts are modelled as unable to
see this contract's private memory, which is true of the EVM. Vault
and AMM instantiate this.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- Every Yul run of a compiled runtime that may CALL out is predicted by
the high-level model under some choice of which external calls fail, and
the pinned compiler produces matching EVM steps. Every halted matching
EVM execution agrees on our storage and on the bound tokens' storage.
Bound tokens must conform, must not be this contract, and must not
alias each other. The external-call oracle cannot see this contract's
memory or `msize` — other contracts in the EVM cannot either. The
compiler may have used either the erase path or powdr spill
(`compileBlock`). This is the Vault/AMM analogue of
`bytecode_call_correct`. -/
theorem bytecode_call_correct_ext {I : Interface} {S X E ε : Type}
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
    BytecodeCallCorrectExt bs c Γ evmKeccak (toCalls o) ctx w yst0 rt is :=
  Proof.bytecode_call_correct_ext (I := I) bs c Γ hΓ hκ o hCalls hctor hS2
    hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf
    hsame horth hinj hBind hslot himm0

/-- Given a memory-blind CALL oracle, there is a matching EVM execution of
compiled runtime whose post-storage (and bound-token storage) is the
unique one the high-level model predicts. Without a total CALL oracle,
"every matching EVM execution" could hold vacuously, because the
Yul-to-EVM compiler only goes forward from a Yul run; a memory-blind
oracle is total by construction. Same conformance assumptions as
`bytecode_call_correct_ext`. The compiler may have used either compile
branch. -/
theorem evmCallRunExtAll_of_progress {I : Interface} {S X E ε : Type}
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
    ∃ σ' ξ', EvmCallRunExtAll bs c Γ evmKeccak (toCalls o) ctx w is yst0 σ' ξ' :=
  Proof.evmCallRunExtAll_of_progress (I := I) bs c Γ hΓ hκ o hCalls
    hctor hS2 hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe
    hconf hsame horth hinj hBind hslot himm0

end Lsc.Compiler
