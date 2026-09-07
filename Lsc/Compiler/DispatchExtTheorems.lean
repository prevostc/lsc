import Lsc.Compiler.DispatchExtDefs
import Lsc.Compiler.Proof.DispatchExtProof

set_option linter.unusedVariables false

/-!
S2 ABI dispatcher: same guard/selector/`switch` as S1, but the selected
body may `CALL`. Unknown selectors still revert with empty data.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled S2 runtime block matches the selected function's `Core.denote`
under some fault oracle (or reverts on a bad selector). Every runtime
function must be `S2Frag` and not a constructor. `Conforms` / `RX` / address
separation are as in `toYulFn_correct_ext`. This is the Yul dispatcher
`bytecode_call_correct_ext` lifts through powdr. -/
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
