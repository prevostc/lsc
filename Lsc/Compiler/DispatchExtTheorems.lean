import Lsc.Compiler.DispatchExtDefs
import Lsc.Compiler.Proof.DispatchExtProof
import Lsc.Compiler.ExtOracleTheorems

set_option linter.unusedVariables false

/-!
ABI dispatcher for contracts that CALL out: same size guard and
selector as the call-free dispatcher, but the selected body may CALL.
Unknown selectors still revert with empty data.

`toCall` restores this contract's storage after an external CALL, so
reentrancy is a lemma (`ExtOracle.noReentry`), not a hypothesis. This is
the Yul dispatcher that `bytecode_call_correct_ext` lifts to EVM bytecode.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled runtime that may CALL out agrees with the high-level model
on every calldata: a known selector runs the matching function under
`w.oracle = Oracle.ofExt o` unless a non-payable function is sent native
value; an unknown selector or a value reject reverts with storage
unchanged. Reentrancy into this contract reverts while the transient
lock is held (`ExtOracle.noReentry`); everything else about the callee
is adversarial. This is the Yul dispatcher that
`bytecode_call_correct_ext` lifts to bytecode. -/
theorem runtimeBlock_correct_ext {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hAgr : ExtAgree ctx.self w.ext st0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hLock : LockFree st0) :
    RuntimeBlockCorrectExt c Γ κ o yul ctx w st0 :=
  Proof.runtimeBlock_correct_ext c Γ hΓ κ hκ o hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hAgr hOr (ExtOracle.noReentry o ctx.self) hLock

end Lsc.Compiler
