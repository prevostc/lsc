import Lsc.Compiler.CoreExtSimDefs
import Lsc.Compiler.Proof.CoreExtSimProof
import Lsc.Compiler.CoreDefs

set_option linter.unusedVariables false

/-!
Core to Yul for functions that may CALL a bound token. A Yul run, which
sees the EVM CALL success bit, is predicted by the high-level model
under some choice of which calls fail.

Vault is one binding; AMM is two. Shared assumptions: tokens conform,
are not this contract, do not alias each other, and the function never
stores a bound address. Constructors are excluded.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-- A function that never CALLs out still compiles under the external-call
dialect: a Yul run is predicted by the high-level model, and bound-token
ghosts stay in sync on success. Needed because Vault views never CALL
but live in a contract that does. Bound tokens must ignore our storage,
and the function must not store a callee address. -/
theorem core_sim_ext_callFree {I : Interface} {S X E ε}
    (bs : List (BindEnv I S X)) {c Γ κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : BindEnvs.ignoresLocal bs)
    {calls : ExternalCalls} {t} (core : Core t) (hM1 : CallFree core)
    (hslot : BindEnvs.avoids Γ c bs core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv (yulD calls))
      (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st) (hRX : RXs bs w st)
      (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
      (hconf : BindEnvs.conforms bs ctx.self w.self calls)
      (hinj : BindEnvs.addrInj bs w.self)
      (hBind : BindEnvs.lookupWF c Γ bs)
      {e'} (hem : emitCore c {} env.length haltUnit core = some e')
      {V' st' o} (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
      ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
        match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
            Except (Err ε) (t.denote × World S X E)) with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
              R c Γ κ w' st' ∧ RXs bs w' st'
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
              haltError c Γ e bytes :=
  Proof.core_sim_ext_callFree bs hhalt hΓ hκ hlen hign core hM1 hslot

/-- If the compiler accepted a runtime function that may CALL bound tokens,
every Yul run of the emitted block is predicted by the high-level model
under some choice of which external calls fail, and each token's ghost
stays in sync with that account's storage on success. Tokens must
conform, must not be this contract, and must not alias each other; the
function must never store a bound address. Unlike
`toYulFn_correct_callFree` this is backward (every Yul run, not every
high-level outcome). Vault and AMM are instances. -/
theorem toYulFn_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RXs bs w st0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : BindEnvs.avoids Γ c bs f.core) :
    ToYulFnCorrectExts bs c Γ κ calls f yul ctx w st0 :=
  Proof.toYulFn_correct_ext bs c Γ hΓ κ hκ calls f hf hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hRX hign hBindNe hconf hsame horth hinj hBind hslot

/-- Specialisation of `toYulFn_correct_ext` to a single bound token. Vault
is this case: one ERC-20 in storage, so conformance and ghost agreement
are about that one address. AMM needs the family form because it has
two. -/
theorem toYulFn_correct_ext_one {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RX α bind w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core) :
    ToYulFnCorrectExt α bind c Γ κ calls f yul ctx w st0 :=
  Proof.toYulFn_correct_ext_one α bind c Γ hΓ κ hκ calls f hf hS2 hlen hbound
    yul hyul ctx w st0 hctx hR hRX hign hBindNe hconf hBind hslot

end Lsc.Compiler
