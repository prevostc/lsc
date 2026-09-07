import Examples.Counter.CompileDefs
import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Examples.Counter.CompileProof
import Examples.Counter.Contract

/-!
Counter is the smallest compiled contract: one storage word, four
runtime functions, no external calls, no wealth theorem.

Each theorem says the emitted Yul matches the high-level Counter model
on that entrypoint (or on the whole dispatcher). Shared assumptions:
the compiler accepted the function, keccak keys do not collide, and
the EVM frame matches the starting Counter world.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- Compiled `increment` adds one to the counter, or reverts on overflow,
exactly as the high-level model does; a successful call also emits the
same increment event. No calldata arguments. The compiler must have
accepted this function, and the EVM frame must match the starting
Counter world. -/
theorem counter_increment_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementFn yul ctx w st0 :=
  Proof.counter_increment_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Compiled `incrementBy` adds the calldata amount to the counter, or
reverts when the amount is zero or the add overflows, matching the
high-level model. Same compiler and layout assumptions as
`counter_increment_correct`; this is the one-argument entrypoint. -/
theorem counter_incrementBy_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementByFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ incrementByFn yul ctx w st0 :=
  Proof.counter_incrementBy_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Compiled `decrement` saturates at zero — a zero counter stays zero,
otherwise it subtracts one — matching the high-level model. It does not
revert on underflow. Same compiler and layout assumptions as the other
Counter entrypoints. -/
theorem counter_decrement_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract decrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ decrementFn yul ctx w st0 :=
  Proof.counter_decrement_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Compiled `get` returns the counter word and leaves storage unchanged,
matching the high-level view. Same compiler and layout assumptions as the
mutating Counter entrypoints. -/
theorem counter_get_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract getFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    ToYulFnCorrect Counter.contract Counter.schema κ getFn yul ctx w st0 :=
  Proof.counter_get_correct κ hκ yul hyul ctx w st0 hctx hR

/-- Every Counter runtime function compiles to Yul that matches the
high-level model: increment, incrementBy, decrement, and get. This is
the uniform statement; the four theorems above specialise it to one
entrypoint each. Constructors are excluded. Counter never calls another
contract. -/
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

/-- The compiled Counter dispatcher agrees with the high-level model on
every calldata: a known selector runs increment, incrementBy, decrement,
or get; an unknown selector or short calldata reverts with storage
unchanged. This is the whole ABI surface, not one function. -/
theorem counter_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Counter.contract = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :
    RuntimeBlockCorrectCallFree Counter.contract Counter.schema κ yul ctx w st0 :=
  Proof.counter_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler
