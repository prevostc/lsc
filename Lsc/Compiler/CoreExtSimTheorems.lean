import Lsc.Compiler.CoreExtSimDefs
import Lsc.Compiler.Proof.CoreExtSimProof
import Lsc.Compiler.CoreDefs

set_option linter.unusedVariables false

/-!
Core to Yul for functions that may CALL out. A Yul run, which sees the
EVM CALL success bit, is predicted by the high-level model under
`Oracle.ofExt`. Reentrancy is not modelled (`NoReentry` is the only
callee hypothesis); everything else about the callee is adversarial.
Constructors are excluded.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-- A function that never CALLs out still compiles under the external-call
dialect: a Yul run is predicted by the high-level model, and `ExtAgree`
is preserved on success. Needed because views never CALL but live in a
contract that does. -/
theorem core_sim_ext_callFree {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : CallFree core) :
    SimExt tag c Γ κ o ctx haltUnit core :=
  Proof.core_sim_ext_callFree tag hhalt hΓ hκ hlen core hM1

/-- If the compiler accepted a runtime function that may CALL out, every
Yul run of the emitted block is predicted by the high-level model with
`w.oracle = Oracle.ofExt o`, and `ExtAgree` holds on success.
`NoReentry o ctx.self` is the only assumption about the callee
(reentrancy is not modelled); everything else is adversarial. Unlike
`toYulFn_correct_callFree` this is backward (every Yul run, not every
high-level outcome). -/
theorem toYulFn_correct_ext {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hAgr : ExtAgree ctx.self w.ext st0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self) :
    ToYulFnCorrectExt c Γ κ o f yul ctx w st0 :=
  Proof.toYulFn_correct_ext hΓ κ hκ o f hf hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hAgr hOr hNR

end Lsc.Compiler
