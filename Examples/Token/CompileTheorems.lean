import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Examples.Token.CompileProof
import Examples.Token.Contract

/-!
Token's compiler instance: every runtime function, and the dispatcher,
compile to Yul that matches the high-level Token model on storage,
returns, and reverts.

Token never calls another contract. Mapping slots (balances, allowances)
are included. Constructors are excluded; deploy is a separate theorem.
Shared assumptions: the compiler accepted the function, keccak keys do
not collide, and the EVM frame matches the starting Token world.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- If the compiler accepted a Token runtime function, running the emitted Yul
has the same effect on storage, return data, and halt kind as the high-level
Token model: a successful call agrees on the new balances and allowances, a
revert rolls storage back and returns the same error bytes. Token uses
mapping slots, unlike Counter's single word. Constructors are excluded;
Token never calls another contract. -/
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

/-- The compiled Token dispatcher agrees with the high-level model on every
calldata: a known selector runs the matching function, an unknown selector
or short calldata reverts with storage unchanged. Same compiler and layout
assumptions as `token_correct`; this is the whole ABI surface, not one
function. -/
theorem token_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Token.contract = some yul)
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    RuntimeBlockCorrectCallFree Token.contract Token.schema κ yul ctx w st0 :=
  Proof.token_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler
