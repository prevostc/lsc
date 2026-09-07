import Lsc.Compiler.DispatchExtDefs
import Lsc.Compiler.Proof.DispatchExtProof

set_option linter.unusedVariables false

/-!
ABI dispatcher for contracts that CALL out: same size guard and
selector as the call-free dispatcher, but the selected body may CALL
a bound token. Unknown selectors still revert with empty data.

Bound tokens must conform, must not be this contract, and the function
must never store a bound address. This is the Yul dispatcher that
`bytecode_call_correct_ext` lifts to EVM bytecode.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled runtime that may CALL out agrees with the high-level model
on every calldata, under some choice of which external calls fail: a
known selector runs the matching function; an unknown selector reverts
with storage unchanged. Bound tokens must conform and must not be this
contract; no runtime function may store a bound address. This is the
Yul dispatcher that `bytecode_call_correct_ext` lifts to bytecode. -/
theorem runtimeBlock_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RXs bs w st0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core) :
    RuntimeBlockCorrectExts bs c Γ κ calls yul ctx w st0 :=
  Proof.runtimeBlock_correct_ext bs c Γ hΓ κ hκ calls hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hRX hign hBindNe hconf hsame horth hinj hBind hslot

end Lsc.Compiler
