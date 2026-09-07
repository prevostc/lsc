import Lsc.Compiler.CoreDefs
import Lsc.Compiler.Proof.CoreProof

/-!
Call-free `Core.denote` depends on `self`/`ext` only, so `transport_trace`'s
`hpc` hypothesis is free for every S1 contract.
-/

namespace Lsc.Compiler.Proof

open Lsc

variable {S X E ε : Type}

/-- Two `Tx.run` results agree on the value and on post-`self`/`ext`. -/
def exceptSelfExt {α} : Except (Err ε) (α × World S X E) →
    Except (Err ε) (α × World S X E) → Prop
  | .ok (v, w1), .ok (v', w1') => v = v' ∧ w1.self = w1'.self ∧ w1.ext = w1'.ext
  | .error e, .error e' => e = e'
  | _, _ => False

theorem m1op_run_self_ext {Γ : ContractSchema S X E ε} {op : Lsc.Op}
    (h : M1Op op) (env : List Nat) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Lsc.Op.denote Γ env op) ctx w)
      (Tx.run (Lsc.Op.denote Γ env op) ctx w') := by
  cases op with
  | call _ _ _ => exact (show False from h).elim
  | load f => simp [Lsc.Op.denote, Tx.run_load, exceptSelfExt, hs, he]
  | loadMap f k => simp [Lsc.Op.denote, Tx.run_loadMap, exceptSelfExt, hs, he]
  | loadMap2 f k₁ k₂ => simp [Lsc.Op.denote, Tx.run_loadMap2, exceptSelfExt, hs, he]
  | sender => simp [Lsc.Op.denote, Tx.run_sender, exceptSelfExt, hs, he]
  | value => simp [Lsc.Op.denote, Tx.run_value, exceptSelfExt, hs, he]
  | timestamp => simp [Lsc.Op.denote, Tx.run_timestamp, exceptSelfExt, hs, he]
  | blockNumber => simp [Lsc.Op.denote, Tx.run_blockNumber, exceptSelfExt, hs, he]
  | selfAddress => simp [Lsc.Op.denote, Tx.run_selfAddress, exceptSelfExt, hs, he]
  | addChecked a b =>
    simp [Lsc.Op.denote, Tx.run_addChecked]
    split <;> simp [exceptSelfExt, hs, he]
  | subChecked a b =>
    simp [Lsc.Op.denote, Tx.run_subChecked]
    split <;> simp [exceptSelfExt, hs, he]
  | mulChecked a b =>
    simp [Lsc.Op.denote, Tx.run_mulChecked]
    split <;> simp [exceptSelfExt, hs, he]
  | divChecked a b =>
    simp [Lsc.Op.denote, Tx.run_divChecked]
    split <;> simp [exceptSelfExt, hs, he]
  | mulDivDown a b c =>
    simp [Lsc.Op.denote]
    split <;> simp [exceptSelfExt, hs, he]
    split <;> simp [exceptSelfExt, hs, he]
  | mulDivUp a b c =>
    simp [Lsc.Op.denote]
    split <;> simp [exceptSelfExt, hs, he]
    split <;> simp [exceptSelfExt, hs, he]
  | pure a => simp [Lsc.Op.denote, exceptSelfExt, hs, he]

theorem m1stmt_run_self_ext {Γ : ContractSchema S X E ε} {s : Lsc.Stmt}
    (h : M1Stmt s) (env : List Nat) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Lsc.Stmt.denote Γ env s) ctx w)
      (Tx.run (Lsc.Stmt.denote Γ env s) ctx w') := by
  cases s with
  | call _ _ _ => exact (show False from h).elim
  | store f v => simp [Lsc.Stmt.denote, Tx.run_store, exceptSelfExt, hs, he]
  | storeMap f k v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap, exceptSelfExt, hs, he]
  | storeMap2 f k₁ k₂ v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap2, exceptSelfExt, hs, he]
  | require c err args =>
    simp [Lsc.Stmt.denote, Tx.run_require]
    split <;> simp [exceptSelfExt, hs, he]
  | emit ev args => simp [Lsc.Stmt.denote, Tx.run_emit, exceptSelfExt, hs, he]
  | revert err args => simp [Lsc.Stmt.denote, Tx.run_revert, exceptSelfExt]

theorem callFree_run_self_ext {Γ : ContractSchema S X E ε} {t}
    {core : Core t} (hM1 : CallFree core) (env : List Nat) (ctx : Ctx)
    (w w' : World S X E) (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Core.denote Γ core env) ctx w)
      (Tx.run (Core.denote Γ core env) ctx w') := by
  revert hM1 env w w' hs he
  induction core with
  | ret r =>
    intro h env w w' hs he
    simp [Core.denote, exceptSelfExt, hs, he]
  | opTail op | opTailAddr op | opTailFlag op =>
    intro h env w w' hs he
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simpa [Core.denote] using m1op_run_self_ext (Γ := Γ) hop env ctx w w' hs he
  | stmtTail s =>
    intro h env w w' hs he
    have hs' : M1Stmt s := by simpa [CallFree, M1Frag] using h
    simpa [Core.denote] using m1stmt_run_self_ext (Γ := Γ) hs' env ctx w w' hs he
  | revertTail err args =>
    intro h env w w' hs he
    simp [Core.denote, Tx.run_revert, exceptSelfExt]
  | letOp op k ih =>
    intro h env w w' hs he
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    simp [Core.denote, Tx.run_bind]
    have hopr := m1op_run_self_ext (Γ := Γ) hop env ctx w w' hs he
    cases h1 : Tx.run (Lsc.Op.denote Γ env op) ctx w with
    | error e =>
      cases h2 : Tx.run (Lsc.Op.denote Γ env op) ctx w' with
      | error e' => simp [exceptSelfExt] at hopr ⊢; exact hopr
      | ok _ => simp [exceptSelfExt, h1, h2] at hopr
    | ok p =>
      cases h2 : Tx.run (Lsc.Op.denote Γ env op) ctx w' with
      | error _ => simp [exceptSelfExt, h1, h2] at hopr
      | ok p' =>
        simp [exceptSelfExt, h1, h2] at hopr
        rcases p with ⟨v, w1⟩
        rcases p' with ⟨v', w1'⟩
        rcases hopr with ⟨rfl, hs1, he1⟩
        exact ih hk (v :: env) w1 w1' hs1 he1
  | seq s k ih =>
    intro h env w w' hs he
    have ⟨hsS, hk⟩ := m1frag_seq.mp h
    simp [Core.denote, Tx.run_bind]
    have hsr := m1stmt_run_self_ext (Γ := Γ) hsS env ctx w w' hs he
    cases h1 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error e =>
      cases h2 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w' with
      | error e' => simp [exceptSelfExt] at hsr ⊢; exact hsr
      | ok _ => simp [exceptSelfExt, h1, h2] at hsr
    | ok p =>
      cases h2 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w' with
      | error _ => simp [exceptSelfExt, h1, h2] at hsr
      | ok p' =>
        simp [exceptSelfExt, h1, h2] at hsr
        rcases p with ⟨v, w1⟩
        rcases p' with ⟨v', w1'⟩
        rcases hsr with ⟨_, hs1, he1⟩
        exact ih hk env w1 w1' hs1 he1
  | letPure p args k ih =>
    intro h env w w' hs he
    have ⟨hp, hlen, hk⟩ := m1frag_letPure.mp h
    subst hp
    simp [Core.denote]
    exact ih hk (Prim.eval .id (args.map (·.eval env)) :: env) w w' hs he
  | ite c a b iha ihb =>
    intro h env w w' hs he
    have ⟨_, ha, hb⟩ := m1frag_ite.mp h
    simp [Core.denote]
    split_ifs
    · exact iha ha env w w' hs he
    · exact ihb hb env w w' hs he

theorem worldAfter_callFree_congr {Γ : ContractSchema S X E ε} {t}
    (core : Core t) (hM1 : CallFree core) (env : List Nat) (ctx : Ctx)
    (w w' : World S X E) (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    (worldAfter (Core.denote Γ core env) ctx w).self =
      (worldAfter (Core.denote Γ core env) ctx w').self ∧
    (worldAfter (Core.denote Γ core env) ctx w).ext =
      (worldAfter (Core.denote Γ core env) ctx w').ext := by
  have hrun := callFree_run_self_ext (Γ := Γ) hM1 env ctx w w' hs he
  cases h1 : Tx.run (Core.denote Γ core env) ctx w with
  | error e =>
    cases h2 : Tx.run (Core.denote Γ core env) ctx w' with
    | error e' => simp [worldAfter, h1, h2, hs, he]
    | ok _ => simp [exceptSelfExt, h1, h2] at hrun
  | ok p =>
    cases h2 : Tx.run (Core.denote Γ core env) ctx w' with
    | error _ => simp [exceptSelfExt, h1, h2] at hrun
    | ok p' =>
      simp [exceptSelfExt, h1, h2] at hrun
      rcases p with ⟨v, w1⟩
      rcases p' with ⟨v', w1'⟩
      simp [worldAfter, h1, h2]
      exact ⟨hrun.2.1, hrun.2.2⟩

end Lsc.Compiler.Proof
