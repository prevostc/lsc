import Examples.CounterCompileDefs
import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Examples.CounterCompileProof
import Examples.Counter

/-!
Counter is the call-free compiler smoke test: four runtime functions, no
external CALL. Each theorem is `toYulFn_correct_callFree` specialised to
that entrypoint (or to the whole `functions` list).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- Compiled `increment` matches `Core.denote` of Counter.increment under `R`.
Call-free, no calldata args; keccak-injectivity and lawful layout as in
`toYulFn_correct_callFree`. -/
theorem counter_increment_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementFn yul ctx w st0 :=
  Proof.counter_increment_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Same as `counter_increment_correct` for `incrementBy n` (one ABI word). -/
theorem counter_incrementBy_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementByFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementByFn yul ctx w st0 :=
  Proof.counter_incrementBy_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Same for `decrement`, including the underflow revert path matching Core. -/
theorem counter_decrement_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract decrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ decrementFn yul ctx w st0 :=
  Proof.counter_decrement_correct κ hκ yul hyul ctx w st0 hctx hR

/-- `get` is a view returning the counter word; compiled Yul returns the same
word Core does, with storage unchanged. -/
theorem counter_get_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract getFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ getFn yul ctx w st0 :=
  Proof.counter_get_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Every runtime function of Counter is in the call-free fragment, so
`toYulFn_correct_callFree` applies uniformly. This is the S1 instance
PROOF_CHAIN cites as `counter_correct`. -/
theorem counter_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (f : FnDef) (hf : f ∈ Counter.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Counter.contract f = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ f yul ctx w st0 :=
  Proof.counter_correct κ hκ f hf _hk yul hyul ctx w st0 hctx hR

/-- Counter's dispatcher: increment/incrementBy/decrement/get, unknown
selectors revert. Specialises `runtimeBlock_correct_callFree`. -/
theorem counter_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Counter.contract = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    RuntimeBlockCorrectCallFree Counter.contract Counter.schema κ yul ctx w st0 :=
  Proof.counter_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler
