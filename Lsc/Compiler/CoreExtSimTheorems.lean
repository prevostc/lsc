import Lsc.Compiler.CoreExtSimDefs
import Lsc.Compiler.Proof.CoreExtSimProof
import Lsc.Compiler.CoreDefs

set_option linter.unusedVariables false

/-!
S2 Core → Yul: functions that may `CALL` through declared bindings. The
fault oracle is chosen existentially so a Yul run (which sees the EVM CALL
success bit) is predicted by `Core.denote` with `w.faults := fo`. Vault is
one binding; AMM is two `IERC20`s.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-- Call-free cores still compile under S2's external dialect: descend the
`yulD` run to the closed `evm` interpreter, apply S1 `core_sim`, and remap
the fault oracle. Binding packages must ignore local storage (`ignoresLocal`)
and the core must not store the callee address (`avoids`). This lemma is the
call-free case of `toYulFn_correct_ext`. -/
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

/-- If `f` is an S2Frag runtime function (`CallFree` plus `Op.call`/`Stmt.call`)
and `toYulFn` succeeds, every Yul `Run` on the external dialect is matched by
`Core.denote` under some fault oracle, and each binding's `RX` (ghost ↔
foreign storage) is preserved on success. Assumes `Conforms` for every
package (successful CALLs decode as the interface model), distinct addresses
do not alias ghosts, and the core never stores a bound address. This is the
S2 compiler theorem PROOF_CHAIN cites; Vault/AMM are instances. -/
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

/-- Specialisation of `toYulFn_correct_ext` to a single binding. Vault is this
case: one IERC20 `asset` in storage, so the family is the singleton
`[⟨α, bind⟩]` and `RX` / `Conforms` are the unpacked forms. -/
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
