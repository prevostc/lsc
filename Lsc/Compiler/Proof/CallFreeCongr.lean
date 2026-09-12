import Lsc.Compiler.CoreDefs
import Lsc.Compiler.Proof.CoreProof
import Lsc.Security.Trace

set_option linter.unusedSimpArgs false

/-!
Call-free `Core.denote` depends on `self`/`ext` only, so `transport_trace`'s
`hpc` hypothesis is free for every S1 contract.
-/

namespace Lsc.Compiler.Proof

open Lsc Lsc.Compiler Lsc.Security

variable {S X E ε : Type}

/-- Two `Tx.run` results agree on the value and on post-`self`/`ext`. -/
@[reducible] def exceptSelfExt {α} : Except (Err ε) (α × World S X E) →
    Except (Err ε) (α × World S X E) → Prop
  | .ok (v, w1), .ok (v', w1') => v = v' ∧ w1.self = w1'.self ∧ w1.ext = w1'.ext
  | .error e, .error e' => e = e'
  | _, _ => False

@[simp] theorem exceptSelfExt.error_eq {α} {e : Err ε} :
    @exceptSelfExt S X E ε α (.error e) (.error e) := rfl

theorem m1op_run_self_ext {Γ : ContractSchema S X E ε} {op : Lsc.Op}
    (h : M1Op op) (env : List Nat) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Lsc.Op.denote Γ env op) ctx w)
      (Tx.run (Lsc.Op.denote Γ env op) ctx w') := by
  cases op with
  | call _ _ _ => exact (show False from h).elim
  | load f =>
    simp [Lsc.Op.denote, Tx.run_load, exceptSelfExt, hs, he]
  | loadMap f k =>
    simp [Lsc.Op.denote, Tx.run_loadMap, exceptSelfExt, hs, he]
  | loadMap2 f k₁ k₂ =>
    simp [Lsc.Op.denote, Tx.run_loadMap2, exceptSelfExt, hs, he]
  | sender =>
    change exceptSelfExt (.ok (ctx.sender, w)) (.ok (ctx.sender, w'))
    exact ⟨rfl, hs, he⟩
  | value =>
    change exceptSelfExt (.ok (ctx.value, w)) (.ok (ctx.value, w'))
    exact ⟨rfl, hs, he⟩
  | timestamp =>
    change exceptSelfExt (.ok (ctx.timestamp, w)) (.ok (ctx.timestamp, w'))
    exact ⟨rfl, hs, he⟩
  | blockNumber =>
    change exceptSelfExt (.ok (ctx.blockNumber, w)) (.ok (ctx.blockNumber, w'))
    exact ⟨rfl, hs, he⟩
  | selfAddress =>
    change exceptSelfExt (.ok (ctx.self, w)) (.ok (ctx.self, w'))
    exact ⟨rfl, hs, he⟩
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
    simp [Lsc.Op.denote, Tx.run_mulDivDown]
    by_cases hc : Atom.eval env c = 0
    · simp [hc]
    · by_cases hb : Atom.eval env a * Atom.eval env b < wordBound
      · simp [hc, hb]; exact ⟨rfl, hs, he⟩
      · simp [hc, hb]
  | mulDivUp a b c =>
    simp [Lsc.Op.denote, Tx.run_mulDivUp]
    by_cases hc : Atom.eval env c = 0
    · simp [hc]
    · by_cases hb : Atom.eval env a * Atom.eval env b < wordBound
      · simp [hc, hb]; exact ⟨rfl, hs, he⟩
      · simp [hc, hb]
  | pure a =>
    simp [Lsc.Op.denote, Tx.run_pure, exceptSelfExt, hs, he]

theorem m1stmt_run_self_ext {Γ : ContractSchema S X E ε} {s : Lsc.Stmt}
    (h : M1Stmt s) (env : List Nat) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Lsc.Stmt.denote Γ env s) ctx w)
      (Tx.run (Lsc.Stmt.denote Γ env s) ctx w') := by
  cases s with
  | call _ _ _ => exact (show False from h).elim
  | store f v =>
    simp [Lsc.Stmt.denote, Tx.run_store, exceptSelfExt, hs, he]
  | storeMap f k v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap, exceptSelfExt, hs, he]
  | storeMap2 f k₁ k₂ v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap2, exceptSelfExt, hs, he]
  | require c err args =>
    simp [Lsc.Stmt.denote, Tx.run_require]
    split <;> simp [exceptSelfExt, hs, he]
  | emit ev args =>
    simp [Lsc.Stmt.denote, Tx.run_emit, exceptSelfExt, hs, he]
  | revert err args =>
    simp [Lsc.Stmt.denote, Tx.run_revert, exceptSelfExt]

private theorem exceptSelfExt_error_error {α e e'}
    {r r' : Except (Err ε) (α × World S X E)}
    (h1 : r = .error e) (h2 : r' = .error e')
    (h : exceptSelfExt r r') : e = e' := by
  subst h1; subst h2; exact h

private theorem exceptSelfExt_ok_ok {α v v' w1 w1'}
    {r r' : Except (Err ε) (α × World S X E)}
    (h1 : r = .ok (v, w1)) (h2 : r' = .ok (v', w1'))
    (h : exceptSelfExt r r') :
    v = v' ∧ w1.self = w1'.self ∧ w1.ext = w1'.ext := by
  subst h1; subst h2; exact h

theorem callFree_run_self_ext {Γ : ContractSchema S X E ε} {t}
    {core : Core t} (hM1 : CallFree core) (env : List Nat) (ctx : Ctx)
    (w w' : World S X E) (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    exceptSelfExt (ε := ε) (Tx.run (Core.denote Γ core env) ctx w)
      (Tx.run (Core.denote Γ core env) ctx w') := by
  revert hM1 env w w' hs he
  induction core with
  | ret r =>
    intro h env w w' hs he
    simp [Core.denote, Tx.run_pure, exceptSelfExt, hs, he]
  | opTail op =>
    intro h env w w' hs he
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    dsimp [Core.denote, RetTy.denote]
    exact m1op_run_self_ext (Γ := Γ) hop env ctx w w' hs he
  | opTailAddr op =>
    intro h env w w' hs he
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    dsimp [Core.denote, RetTy.denote, Address]
    exact m1op_run_self_ext (Γ := Γ) hop env ctx w w' hs he
  | opTailFlag op =>
    intro h env w w' hs he
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    dsimp [Core.denote, RetTy.denote, Flag]
    exact m1op_run_self_ext (Γ := Γ) hop env ctx w w' hs he
  | stmtTail s =>
    intro h env w w' hs he
    have hs' : M1Stmt s := by simpa [CallFree, M1Frag] using h
    dsimp [Core.denote, RetTy.denote]
    exact m1stmt_run_self_ext (Γ := Γ) hs' env ctx w w' hs he
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
      | error e' =>
        have := exceptSelfExt_error_error h1 h2 hopr
        simp [exceptSelfExt, this]
      | ok _ =>
        simp [exceptSelfExt, h1, h2] at hopr
    | ok p =>
      cases h2 : Tx.run (Lsc.Op.denote Γ env op) ctx w' with
      | error _ =>
        simp [exceptSelfExt, h1, h2] at hopr
      | ok p' =>
        rcases p with ⟨v, w1⟩
        rcases p' with ⟨v', w1'⟩
        have ⟨hv, hs1, he1⟩ := exceptSelfExt_ok_ok h1 h2 hopr
        subst hv
        exact ih hk (v :: env) w1 w1' hs1 he1
  | seq s k ih =>
    intro h env w w' hs he
    have ⟨hsS, hk⟩ := m1frag_seq.mp h
    simp [Core.denote, Tx.run_bind]
    have hsr := m1stmt_run_self_ext (Γ := Γ) hsS env ctx w w' hs he
    cases h1 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error e =>
      cases h2 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w' with
      | error e' =>
        have := exceptSelfExt_error_error h1 h2 hsr
        simp [exceptSelfExt, this]
      | ok _ =>
        simp [exceptSelfExt, h1, h2] at hsr
    | ok p =>
      cases h2 : Tx.run (Lsc.Stmt.denote Γ env s) ctx w' with
      | error _ =>
        simp [exceptSelfExt, h1, h2] at hsr
      | ok p' =>
        rcases p with ⟨v, w1⟩
        rcases p' with ⟨v', w1'⟩
        have ⟨_, hs1, he1⟩ := exceptSelfExt_ok_ok h1 h2 hsr
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
    simp [Core.denote, Tx.run_ite]
    split_ifs
    · exact iha ha env w w' hs he
    · exact ihb hb env w w' hs he

/-- A call-free Core run's post-`self`/`ext` depend only on the pre-`self`/`ext`
(not log or faults). -/
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
      rcases p with ⟨v, w1⟩
      rcases p' with ⟨v', w1'⟩
      have ⟨_, hs1, he1⟩ := exceptSelfExt_ok_ok h1 h2 hrun
      simp [worldAfter, h1, h2, hs1, he1]

end Lsc.Compiler.Proof
