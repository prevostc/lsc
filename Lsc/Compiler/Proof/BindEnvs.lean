import Lsc.Compiler.Proof.Oracle
import Lsc.Compiler.Proof.OfState
import Lsc.Lang.CoreTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
`BindEnvs.avoids` and address-preservation along M1/`CallFree` steps.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-- Binding address is the scalar at `slot`. Other-field stores (Lawful) leave it
unchanged; read through `R`/`storageRel`, not `∀ σ, bind.addr σ = bind.addr w.self`. -/
theorem bind_addr_store {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    (hΓ : Γ.st.Lawful c.fields) {slot f : Nat}
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar)
    (hne : slot ≠ f) (σ : S) (v : Nat) :
    bind.addr (Γ.st.scalarUpd f σ v) = bind.addr σ := by
  rw [← haddr, ← haddr, hΓ.scalar_scalar slot f σ v hkind, if_neg hne]

/-! ## Binding address is not stored (`haddr` elimination) -/

def stmtAvoids (slot : Nat) : Lsc.Stmt → Prop
  | .store f _ => f ≠ slot
  | .storeMap f _ _ => f ≠ slot
  | .storeMap2 f _ _ _ => f ≠ slot
  | _ => True

def coreAvoids (slot : Nat) : {t : RetTy} → Core t → Prop
  | _, .seq s k => stmtAvoids slot s ∧ coreAvoids slot k
  | _, .stmtTail s => stmtAvoids slot s
  | _, .letOp _ k => coreAvoids slot k
  | _, .letPure _ _ k => coreAvoids slot k
  | _, .ite _ a b => coreAvoids slot a ∧ coreAvoids slot b
  | _, _ => True

def stmtAvoidsB (slot : Nat) : Lsc.Stmt → Bool
  | .store f _ => !decide (f = slot)
  | .storeMap f _ _ => !decide (f = slot)
  | .storeMap2 f _ _ _ => !decide (f = slot)
  | _ => true

def coreAvoidsB (slot : Nat) : {t : RetTy} → Core t → Bool
  | _, .seq s k => stmtAvoidsB slot s && coreAvoidsB slot k
  | _, .stmtTail s => stmtAvoidsB slot s
  | _, .letOp _ k => coreAvoidsB slot k
  | _, .letPure _ _ k => coreAvoidsB slot k
  | _, .ite _ a b => coreAvoidsB slot a && coreAvoidsB slot b
  | _, _ => true

theorem stmtAvoidsB_eq (slot : Nat) (s : Lsc.Stmt) :
    stmtAvoidsB slot s = true ↔ stmtAvoids slot s := by
  cases s <;> simp [stmtAvoidsB, stmtAvoids]

theorem coreAvoidsB_eq (slot : Nat) {t} (core : Core t) :
    coreAvoidsB slot core = true ↔ coreAvoids slot core := by
  induction core with
  | ret _ | revertTail _ _ | opTail _ | opTailAddr _ | opTailFlag _ =>
    simp [coreAvoidsB, coreAvoids]
  | stmtTail s => simp [coreAvoidsB, coreAvoids, stmtAvoidsB_eq]
  | letOp _ k ih => simp [coreAvoidsB, coreAvoids, ih]
  | seq s k ih => simp [coreAvoidsB, coreAvoids, stmtAvoidsB_eq, ih]
  | letPure _ _ k ih => simp [coreAvoidsB, coreAvoids, ih]
  | ite _ a b iha ihb => simp [coreAvoidsB, coreAvoids, iha, ihb]

instance (slot : Nat) (s : Lsc.Stmt) : Decidable (stmtAvoids slot s) :=
  decidable_of_iff (stmtAvoidsB slot s = true) (stmtAvoidsB_eq slot s)

instance (slot : Nat) {t} (core : Core t) : Decidable (coreAvoids slot core) :=
  decidable_of_iff (coreAvoidsB slot core = true) (coreAvoidsB_eq slot core)

theorem coreAvoids_of_all {c : ContractDef} (slot : Nat)
    (h : c.functions.all (fun f => coreAvoidsB slot f.core) = true) :
    ∀ f ∈ c.functions, coreAvoids slot f.core :=
  fun f hf => (coreAvoidsB_eq slot f.core).mp ((List.all_eq_true.mp h) f hf)

theorem stmtAvoids_not_write {slot : Nat} {s : Lsc.Stmt} (h : stmtAvoids slot s) :
    slot ∉ (Stmt.effects s).writes := by
  cases s <;> simp [stmtAvoids, Stmt.effects] at h ⊢
  · exact Ne.symm h
  · exact Ne.symm h
  · exact Ne.symm h

theorem coreAvoids_not_write {slot : Nat} {t} {core : Core t} (h : coreAvoids slot core) :
    slot ∉ (Core.effects core).writes := by
  induction core with
  | ret _ | revertTail _ _ => simp [Core.effects]
  | opTail op | opTailAddr op | opTailFlag op =>
    cases op <;> simp [Core.effects, Op.effects]
  | stmtTail s =>
    simpa [Core.effects] using stmtAvoids_not_write (by simpa [coreAvoids] using h)
  | letOp _ k ih =>
    simpa [Core.effects, Effects.append, Op.effects_writes] using ih (by simpa [coreAvoids] using h)
  | seq s k ih =>
    have ⟨hs, hk⟩ := h
    simpa [Core.effects, Effects.append, List.mem_append, not_or] using
      ⟨stmtAvoids_not_write hs, ih hk⟩
  | letPure _ _ k ih =>
    simpa [Core.effects] using ih (by simpa [coreAvoids] using h)
  | ite _ a b iha ihb =>
    have ⟨ha, hb⟩ := h
    simpa [Core.effects, Effects.append, List.mem_append, not_or] using ⟨iha ha, ihb hb⟩

/-- Every package's address slot is a scalar that `core` does not store. -/
def BindEnvs.avoids {I : Interface} {S X E ε}
    (Γ : ContractSchema S X E ε) (c : ContractDef)
    (bs : List (BindEnv I S X)) {t} (core : Core t) : Prop :=
  ∀ e ∈ bs, ∃ slot : Nat,
    (∀ σ, Γ.st.scalar slot σ = e.bind.addr σ) ∧
    (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
    coreAvoids slot core

theorem BindEnvs.avoids_singleton {I S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {α : Abs I.Ghost} {bind : Binding I S X} {t} {core : Core t}
    (h : ∃ slot : Nat,
      (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
      (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
      coreAvoids slot core) :
    BindEnvs.avoids Γ c [⟨α, bind⟩] core := by
  intro e he
  have : e = ⟨α, bind⟩ := List.mem_singleton.mp he
  subst this; exact h

theorem BindEnvs.avoids_letOp {I S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {bs : List (BindEnv I S X)} {op} {t} {k : Core t}
    (h : BindEnvs.avoids Γ c bs (.letOp op k)) :
    BindEnvs.avoids Γ c bs k := by
  intro e he
  obtain ⟨slot, hs, hk, hav⟩ := h e he
  exact ⟨slot, hs, hk, by simpa [coreAvoids] using hav⟩

theorem BindEnvs.avoids_seq {I S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {bs : List (BindEnv I S X)} {s} {t} {k : Core t}
    (h : BindEnvs.avoids Γ c bs (.seq s k)) :
    BindEnvs.avoids Γ c bs k := by
  intro e he
  obtain ⟨slot, hs, hk, hav⟩ := h e he
  exact ⟨slot, hs, hk, hav.2⟩

theorem BindEnvs.avoids_letPure {I S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {bs : List (BindEnv I S X)} {p args} {t} {k : Core t}
    (h : BindEnvs.avoids Γ c bs (.letPure p args k)) :
    BindEnvs.avoids Γ c bs k := by
  intro e he
  obtain ⟨slot, hs, hk, hav⟩ := h e he
  exact ⟨slot, hs, hk, by simpa [coreAvoids] using hav⟩

theorem BindEnvs.avoids_ite {I S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {bs : List (BindEnv I S X)} {cond} {t} {a b : Core t}
    (h : BindEnvs.avoids Γ c bs (.ite cond a b)) :
    BindEnvs.avoids Γ c bs a ∧ BindEnvs.avoids Γ c bs b := by
  constructor
  · intro e he
    obtain ⟨slot, hs, hk, hav⟩ := h e he
    exact ⟨slot, hs, hk, hav.1⟩
  · intro e he
    obtain ⟨slot, hs, hk, hav⟩ := h e he
    exact ⟨slot, hs, hk, hav.2⟩

theorem m1stmt_preserves_addr {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    {slot : Nat} (hΓ : Γ.st.Lawful c.fields)
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[slot]?).map (·.kind) = some FieldKind.scalar)
    {s : Lsc.Stmt} (hM1 : M1Stmt s) (hwf : stmtWF c s = true)
    (hav : stmtAvoids slot s)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {w' : World S X E}
    (hok : Lsc.Stmt.denote Γ env s ctx w = .ok ((), w')) :
    bind.addr w'.self = bind.addr w.self := by
  match s with
  | .store f v =>
    simp [Lsc.Stmt.denote, Tx.run_store] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar := by
      have hpair : fieldKindOK c f FieldKind.scalar = true ∧ atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.scalar).mp hpair.1
      simp [hfd, hk]
    exact bind_addr_store (bind := bind) hΓ haddr hfkind (Ne.symm hav) w.self (v.eval env)
  | .storeMap f k v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map1 := by
      have hpair :
          (fieldKindOK c f FieldKind.map1 = true ∧ atomWF k = true) ∧ atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.map1).mp hpair.1.1
      simp [hfd, hk]
    rw [← haddr, ← haddr, hΓ.map1_scalar slot f w.self _ hfkind]
  | .storeMap2 f k₁ k₂ v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap2] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map2 := by
      have hpair :
          ((fieldKindOK c f FieldKind.map2 = true ∧ atomWF k₁ = true) ∧ atomWF k₂ = true) ∧
            atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.map2).mp hpair.1.1.1
      simp [hfd, hk]
    rw [← haddr, ← haddr, hΓ.map2_scalar slot f w.self _ hfkind]
  | .emit ev args =>
    have hred : Lsc.Stmt.denote Γ env (.emit ev args) ctx w =
        .ok ((), { w with log := w.log ++ [Γ.ev.build ev (args.map (·.eval env))] }) := rfl
    rw [hred] at hok; cases hok; rfl
  | .require cnd err args =>
    simp [Lsc.Stmt.denote, Tx.require] at hok
    split_ifs at hok <;> cases hok; rfl
  | .revert _ _ =>
    simp [Lsc.Stmt.denote, Tx.revert] at hok
  | .call .. => exact (show False from hM1).elim

/-! ## `CallFree` Core ignores the oracle except copying `faults` through -/

theorem callFree_preserves_addr {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    {slot : Nat} (hΓ : Γ.st.Lawful c.fields)
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[slot]?).map (·.kind) = some FieldKind.scalar)
    {t} {core : Core t} (hM1 : CallFree core) (hwf : coreWF c core = true)
    (hav : coreAvoids slot core)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    bind.addr w'.self = bind.addr w.self := by
  revert hM1 hwf hav env w v w' hok
  induction core with
  | ret r =>
    intro h hwf hav env w v w' hok
    have hred : Core.denote Γ (.ret r) env ctx w = .ok (r.eval env, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | opTail op | opTailAddr op | opTailFlag op =>
    intro h hwf hav env w v w' hok
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote] at hok
    have hw := m1op_world (Γ := Γ) hop env ctx w hok
    rw [hw]
  | stmtTail s =>
    intro h hwf hav env w v w' hok
    have hs : M1Stmt s := by simpa [CallFree, M1Frag] using h
    have hswf : stmtWF c s = true := by simpa [coreWF] using hwf
    simp only [Core.denote, RetTy.denote] at hok
    exact m1stmt_preserves_addr (bind := bind) hΓ haddr hkind hs hswf hav env ctx w hok
  | revertTail _ _ =>
    intro h hwf hav env w v w' hok
    simp [Core.denote] at hok
    nomatch hok
  | letOp op k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
    simp [Core.denote] at hok
    change Tx.run (Lsc.Op.denote Γ env op >>= fun x => Core.denote Γ k (x :: env))
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hopr : Tx.run (Lsc.Op.denote Γ env op) ctx w with
    | error _ => simp [hopr] at hok
    | ok p =>
      have hw := m1op_world (Γ := Γ) hop env ctx w (by simpa [Tx.run] using hopr)
      simp [hopr] at hok
      have := ih hk hkWF hav (p.1 :: env) p.2 hok
      rw [this, hw]
  | seq s k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hs, hk⟩ := m1frag_seq.mp h
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    have ⟨havs, havk⟩ := hav
    simp [Core.denote] at hok
    change Tx.run (Lsc.Stmt.denote Γ env s >>= fun _ => Core.denote Γ k env)
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hsr : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error _ => simp [hsr] at hok
    | ok p =>
      have ha := m1stmt_preserves_addr (bind := bind) hΓ haddr hkind hs hsWF havs env ctx w
        (by simpa [Tx.run] using hsr)
      simp [hsr] at hok
      have := ih hk hkWF havk env p.2 hok
      exact this.trans ha
  | letPure p args k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hp, hlen, hk⟩ := m1frag_letPure.mp h
    subst hp
    have hkWF : coreWF c k = true := by
      have hpair : (∀ x ∈ args, atomWF x = true) ∧ coreWF c k = true := by
        simpa [coreWF, Bool.and_eq_true] using hwf
      exact hpair.2
    simp [Core.denote] at hok
    exact ih hk hkWF hav (Prim.eval .id (args.map (·.eval env)) :: env) w hok
  | ite cnd a b iha ihb =>
    intro h hwf hav env w v w' hok
    have ⟨_, ha, hb⟩ := m1frag_ite.mp h
    have ⟨hava, havb⟩ := hav
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    simp [Core.denote] at hok
    split_ifs at hok
    · exact iha ha hwf'.1.2 hava env w hok
    · exact ihb hb hwf'.2 havb env w hok

/-! ## `α.ofState` across non-halting local `stepOp` / `ExecStmts` (`hstab`) -/

theorem callFree_addr_of_exists {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    (hΓ : Γ.st.Lawful c.fields) {t} {core : Core t}
    (hM1 : CallFree core) (hwf : coreWF c core = true)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot core)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    bind.addr w'.self = bind.addr w.self := by
  obtain ⟨slot, hs, hk, hav⟩ := hslot
  exact callFree_preserves_addr (I := I) (bind := bind) hΓ hs hk hM1 hwf hav env ctx w hok

theorem callFree_addrs {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef}
    {bs : List (BindEnv I S X)} {t} {core : Core t}
    (hΓ : Γ.st.Lawful c.fields) (hM1 : CallFree core) (hwf : coreWF c core = true)
    (hslot : BindEnvs.avoids Γ c bs core)
    (env : List Nat) (ctx : Ctx) (w : World S X E) {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    ∀ e ∈ bs, e.bind.addr w'.self = e.bind.addr w.self := by
  intro e he
  obtain ⟨slot, hs, hk, hav⟩ := hslot e he
  exact callFree_addr_of_exists (bind := e.bind) hΓ hM1 hwf ⟨slot, hs, hk, hav⟩ env ctx w hok

/-- Local `noExt` suffix (return / `stop`) leaves every package's `RX` intact. -/
theorem RXs_noExt_halt {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    {ctx : Ctx} {w : World S X E}
    (hign : BindEnvs.ignoresLocal bs)
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (hexec : ExecStmts (yulD calls) funs V st ss V' st' o)
    (hctx : ctxRel ctx st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hRX : RXs bs w st) :
    RXs bs w st' := by
  intro e he
  have hstab := ofState_noExt_halt (hign e he) hfuns hno hexec (e.bind.addr w.self)
    (foreign_of_ctx hctx (hBindNe e he))
  unfold RX
  rw [hstab]
  exact hRX e he

/-- Call-free `ExecStmts` (normal) re-establishes `RXs` when addresses and `ext` agree. -/
theorem RXs_noExt_normal {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {ss : YBlock}
    {V' : VEnv evm} {st' : EvmState}
    {ctx : Ctx} {w w' : World S X E}
    (hign : BindEnvs.ignoresLocal bs)
    (hexec : ExecStmts evm funs V st ss V' st' .normal)
    (hctx : ctxRel ctx st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (haddr : ∀ e ∈ bs, e.bind.addr w'.self = e.bind.addr w.self)
    (hext : w'.ext = w.ext)
    (hRX : RXs bs w st) :
    RXs bs w' st' :=
  RXs_callFree hRX
    (fun e he =>
      execStmts_normal_ofState (hign e he) hexec (e.bind.addr w.self)
        (foreign_of_ctx hctx (hBindNe e he)))
    hext haddr

end Lsc.Compiler
