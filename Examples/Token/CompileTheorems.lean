import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Examples.Token.CompileProof
import Examples.Token.Contract

/-!
Token (S1) compiler instance: every runtime function is call-free, so
`toYulFn_correct_callFree` applies to the whole ABI surface. Constructors
are excluded (`hctor`); deploy is a separate theorem.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- Every Token runtime function compiles to Yul that matches `Core.denote`
under `R`. Token has mappings (balances, allowances) so this instance
exercises keccak slot layout, not just Counter's single scalar. External
CALLs are out of this fragment — Token never calls another contract. -/
theorem token_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (f : FnDef) (hf : f ∈ Token.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Token.contract f = some yul)
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    ToYulFnCorrect Token.contract Token.schema κ f yul ctx w st0 :=
  Proof.token_correct κ hκ f hf _hk yul hyul ctx w st0 hctx hR

/-- Token's dispatcher over the ERC20-style ABI (transfer, approve, …). Same
as Counter but with mapping slots and longer calldata. -/
theorem token_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Token.contract = some yul)
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    RuntimeBlockCorrectCallFree Token.contract Token.schema κ yul ctx w st0 :=
  Proof.token_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler
