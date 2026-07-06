import Lsc.Compile.IR.Eval
import Lsc.Compile.IR.FreeVars

namespace Lsc.Compile.IR

open Lsc (Ident)

theorem observablyEqual_symm {a b : IRState} (h : observablyEqual a b) : observablyEqual b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem observablyEqual_trans {a b c : IRState}
    (h1 : observablyEqual a b) (h2 : observablyEqual b c) : observablyEqual a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem observablyEqual_setLocal (st : IRState) (name : Ident) (v : Nat) :
    observablyEqual (st.setLocal name v) st :=
  ⟨rfl, rfl, rfl⟩

private theorem not_mem_singleton_ne {name other : Ident} (h : name ∉ [other]) : name ≠ other := by
  intro heq
  subst heq
  simp at h

private theorem not_mem_or_left {xs ys : List Ident} {name : Ident}
    (h : ¬(name ∈ xs ∨ name ∈ ys)) : name ∉ xs := by
  intro hmem
  exact h (Or.inl hmem)

private theorem not_mem_or_right {xs ys : List Ident} {name : Ident}
    (h : ¬(name ∈ xs ∨ name ∈ ys)) : name ∉ ys := by
  intro hmem
  exact h (Or.inr hmem)

private theorem not_mem_append_left {xs ys : List Ident} {name : Ident}
    (h : name ∉ xs ++ ys) : name ∉ xs := by
  intro hmem
  exact h (List.mem_append_left ys hmem)

private theorem not_mem_append_right {xs ys : List Ident} {name : Ident}
    (h : name ∉ xs ++ ys) : name ∉ ys := by
  intro hmem
  exact h (List.mem_append_right xs hmem)

theorem evalExpr_setLocal_unused (st : IRState) (name : Ident) (v : Nat) (e : Expr)
    (h : name ∉ freeVarsExpr e) :
    evalExpr (st.setLocal name v) e = evalExpr st e := by
  match e with
  | .lit n => rfl
  | .local other =>
    have hne : name ≠ other := not_mem_singleton_ne (by simpa [freeVarsExpr] using h)
    simp [evalExpr, IRState.lookupLocal_setLocal_ne st name other v hne]
  | .sload slot => rfl
  | .add a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .sub a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .mul a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .div a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .lt a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .eq a b =>
    simp only [freeVarsExpr, List.mem_append] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a (not_mem_or_left h),
      evalExpr_setLocal_unused st name v b (not_mem_or_right h)]
  | .isZero a =>
    simp only [freeVarsExpr] at h
    simp [evalExpr, evalExpr_setLocal_unused st name v a h]

private theorem lookupLocal_setSlot (st : IRState) (slot : Nat) (v : Nat) (name : Ident) :
    (st.setSlot slot v).lookupLocal name = st.lookupLocal name := by
  simp [IRState.lookupLocal, IRState.setSlot]

private theorem lookupSlot_eq (st1 st2 : IRState) (slot : Nat) (h : st1.slots = st2.slots) :
    st1.lookupSlot slot = st2.lookupSlot slot := by
  simp [IRState.lookupSlot, h]

theorem evalExpr_obs_agree (st1 st2 : IRState) (e : Expr) (hobs : observablyEqual st1 st2)
    (hlookup : ∀ id ∈ freeVarsExpr e, st1.lookupLocal id = st2.lookupLocal id) :
    evalExpr st1 e = evalExpr st2 e := by
  match e with
  | .lit n => rfl
  | .local name => exact hlookup name (by simp [freeVarsExpr])
  | .sload slot => exact lookupSlot_eq st1 st2 slot hobs.1
  | .add a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .sub a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .mul a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .div a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .lt a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .eq a b =>
    simp only [freeVarsExpr, List.mem_append] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs (λ id hmem => hlookup id (Or.inl hmem)),
      evalExpr_obs_agree st1 st2 b hobs (λ id hmem => hlookup id (Or.inr hmem))]
  | .isZero a =>
    simp only [freeVarsExpr] at hlookup ⊢
    simp [evalExpr, evalExpr_obs_agree st1 st2 a hobs hlookup]

theorem lookupLocal_evalStmt_unused (st : IRState) (s : Stmt) (id : Ident)
    (h : id ∉ freeVarsStmt s) :
    (evalStmt st s).lookupLocal id = st.lookupLocal id := by
  match s with
  | .skip => rfl
  | .seq s1 s2 =>
    simp only [freeVarsStmt, List.mem_append] at h
    simp [evalStmt, lookupLocal_evalStmt_unused st s1 id (not_mem_or_left h),
      lookupLocal_evalStmt_unused (evalStmt st s1) s2 id (not_mem_or_right h)]
  | .letBind bindName e =>
    simp only [freeVarsStmt, List.mem_cons] at h
    by_cases heq : id = bindName
    · exact absurd heq (λ heq' => h (Or.inl heq'))
    · have hne : bindName ≠ id := λ h => heq (by simpa using h.symm)
      simp [evalStmt, IRState.lookupLocal_setLocal_ne st bindName id (evalExpr st e) hne]
  | .sstore slot e =>
    simp only [freeVarsStmt] at h
    simp [evalStmt, lookupLocal_setSlot st slot (evalExpr st e) id]
  | .ifRevert cond =>
    simp only [freeVarsStmt] at h
    by_cases hc : evalExpr st cond = 1 <;> simp [evalStmt, hc, IRState.lookupLocal]
  | .log0 topic =>
    simp only [freeVarsStmt] at h
    simp [evalStmt, IRState.lookupLocal]
  | .log1 topic data =>
    simp only [freeVarsStmt] at h
    simp [evalStmt, IRState.lookupLocal]
  | .revert0 => simp [evalStmt, IRState.lookupLocal]

mutual
  theorem lookupLocal_after_eval_agree (st1 st2 : IRState) (s : Stmt) (hobs : observablyEqual st1 st2)
      (hlookup : ∀ id ∈ freeVarsStmt s, st1.lookupLocal id = st2.lookupLocal id) :
      ∀ id ∈ freeVarsStmt s,
        (evalStmt st1 s).lookupLocal id = (evalStmt st2 s).lookupLocal id := by
    match s with
    | .skip => simpa using hlookup
    | .seq s1 s2 =>
      intro id hmem
      have hmem' : id ∈ freeVarsStmt s1 ∨ id ∈ freeVarsStmt s2 := by
        simpa [freeVarsStmt, List.mem_append] using hmem
      by_cases h₂ : id ∈ freeVarsStmt s2
      · have hl1 : ∀ id ∈ freeVarsStmt s1, st1.lookupLocal id = st2.lookupLocal id := by
          intro id hmem
          exact hlookup id (by simpa [freeVarsStmt, List.mem_append] using Or.inl hmem)
        have hobs' := evalStmt_obs_congr st1 st2 s1 hobs hl1
        have hlookup' : ∀ id ∈ freeVarsStmt s2, (evalStmt st1 s1).lookupLocal id = (evalStmt st2 s1).lookupLocal id := by
          intro id hmem
          by_cases h₁ : id ∈ freeVarsStmt s1
          · exact lookupLocal_after_eval_agree st1 st2 s1 hobs hl1 id h₁
          · simp [lookupLocal_evalStmt_unused st1 s1 id h₁,
              lookupLocal_evalStmt_unused st2 s1 id h₁,
              hlookup id (by simpa [freeVarsStmt, List.mem_append] using Or.inr hmem)]
        simpa [evalStmt] using lookupLocal_after_eval_agree (evalStmt st1 s1) (evalStmt st2 s1) s2 hobs' hlookup' id h₂
      · have h₁ : id ∈ freeVarsStmt s1 := by
          cases hmem' with
          | inl h₁' => exact h₁'
          | inr h₂' => exact absurd h₂' h₂
        simp [evalStmt, lookupLocal_evalStmt_unused (evalStmt st1 s1) s2 id h₂,
          lookupLocal_evalStmt_unused (evalStmt st2 s1) s2 id h₂,
          lookupLocal_after_eval_agree st1 st2 s1 hobs
            (λ id hmem => hlookup id (by simpa [freeVarsStmt, List.mem_append] using Or.inl hmem)) id h₁]
    | .letBind bindName e =>
      intro id hmem
      rcases (show id = bindName ∨ id ∈ freeVarsExpr e from by
        simpa [freeVarsStmt, List.mem_cons] using hmem) with heq | hmem
      · subst heq
        simp [evalStmt, evalExpr_obs_agree st1 st2 e hobs
          (λ id hmem => hlookup id (by simpa [freeVarsStmt, List.mem_cons] using Or.inr hmem))]
      · by_cases heq : id = bindName
        · subst heq
          simp [evalStmt, evalExpr_obs_agree st1 st2 e hobs
            (λ id hmem => hlookup id (by simpa [freeVarsStmt, List.mem_cons] using Or.inr hmem))]
        · have hne : bindName ≠ id := Ne.symm heq
          simp [evalStmt, IRState.lookupLocal_setLocal_ne st1 bindName id (evalExpr st1 e) hne,
            IRState.lookupLocal_setLocal_ne st2 bindName id (evalExpr st2 e) hne,
            hlookup id (by simpa [freeVarsStmt, List.mem_cons] using Or.inr hmem)]
    | .sstore slot e =>
      intro id hmem
      simpa [evalStmt, lookupLocal_setSlot, freeVarsStmt] using
        hlookup id (by simpa [freeVarsStmt] using hmem)
    | .ifRevert cond =>
      intro id hmem
      have heval := evalExpr_obs_agree st1 st2 cond hobs
        (λ id hmem => hlookup id (by simpa [freeVarsStmt] using hmem))
      by_cases hc : evalExpr st1 cond = 1
      · have hc2 : evalExpr st2 cond = 1 := by simpa [heval] using hc
        simp [evalStmt_ifRevert, hc, hc2, IRState.lookupLocal]
        exact hlookup id hmem
      · have hc2 : evalExpr st2 cond ≠ 1 := by
          intro h
          rw [← heval] at h
          exact hc h
        simp [evalStmt_ifRevert, hc, hc2, IRState.lookupLocal]
        exact hlookup id hmem
    | .log0 topic =>
      intro id hmem
      simp [freeVarsStmt] at hmem
    | .log1 topic data =>
      intro id hmem
      simpa [evalStmt, IRState.lookupLocal, freeVarsStmt] using
        hlookup id (by simpa [freeVarsStmt] using hmem)
    | .revert0 =>
      intro id hmem
      simpa [evalStmt, IRState.lookupLocal, freeVarsStmt] using
        hlookup id (by cases hmem)

  theorem evalStmt_obs_congr (st1 st2 : IRState) (s : Stmt) (hobs : observablyEqual st1 st2)
      (hlookup : ∀ id ∈ freeVarsStmt s, st1.lookupLocal id = st2.lookupLocal id) :
      observablyEqual (evalStmt st1 s) (evalStmt st2 s) := by
    match s with
    | .skip => exact hobs
    | .seq s1 s2 =>
      have hl1 : ∀ id ∈ freeVarsStmt s1, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [freeVarsStmt, List.mem_append] using Or.inl hmem)
      have h1 := evalStmt_obs_congr st1 st2 s1 hobs hl1
      have hl2 : ∀ id ∈ freeVarsStmt s2, (evalStmt st1 s1).lookupLocal id = (evalStmt st2 s1).lookupLocal id := by
        intro id hmem
        by_cases h₁ : id ∈ freeVarsStmt s1
        · exact lookupLocal_after_eval_agree st1 st2 s1 hobs hl1 id h₁
        · simp [lookupLocal_evalStmt_unused st1 s1 id h₁,
            lookupLocal_evalStmt_unused st2 s1 id h₁,
            hlookup id (by simpa [freeVarsStmt, List.mem_append] using Or.inr hmem)]
      simp only [evalStmt, observablyEqual]
      exact evalStmt_obs_congr (evalStmt st1 s1) (evalStmt st2 s1) s2 h1 hl2
    | .letBind bindName e =>
      simp only [evalStmt, observablyEqual, IRState.setLocal]
      exact hobs
    | .sstore slot e =>
      have hfree : ∀ id ∈ freeVarsExpr e, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [freeVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 e hobs hfree
      simp only [evalStmt_sstore, observablyEqual, heval, IRState.setSlot]
      exact ⟨by simp [hobs.1], hobs.2.1, hobs.2.2⟩
    | .ifRevert cond =>
      have hfree : ∀ id ∈ freeVarsExpr cond, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [freeVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 cond hobs hfree
      by_cases hc : evalExpr st1 cond = 1
      · have hc2 : evalExpr st2 cond = 1 := by simpa [heval] using hc
        simp only [evalStmt_ifRevert, observablyEqual, hc, hc2]
        exact ⟨hobs.1, hobs.2.1, rfl⟩
      · have hc2 : evalExpr st2 cond ≠ 1 := by
          intro h
          rw [← heval] at h
          exact hc h
        simp only [evalStmt_ifRevert, observablyEqual, hc, hc2]
        exact ⟨hobs.1, hobs.2.1, hobs.2.2⟩
    | .log0 topic =>
      have hlogs : st1.logs ++ [(topic, 0)] = st2.logs ++ [(topic, 0)] := by simp [hobs.2.1]
      simp only [evalStmt_log0, observablyEqual]
      exact ⟨hobs.1, hlogs, hobs.2.2⟩
    | .log1 topic data =>
      have hfree : ∀ id ∈ freeVarsExpr data, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [freeVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 data hobs hfree
      have hlogs : st1.logs ++ [(topic, evalExpr st2 data)] = st2.logs ++ [(topic, evalExpr st2 data)] := by
        simp [hobs.2.1]
      simp only [evalStmt_log1, observablyEqual, heval]
      exact ⟨hobs.1, hlogs, hobs.2.2⟩
    | .revert0 =>
      simp only [evalStmt_revert0, observablyEqual]
      exact ⟨hobs.1, hobs.2.1, trivial⟩
end

mutual
  theorem lookupLocal_bind_post (st1 st2 : IRState) (s : Stmt) (id : Ident)
      (hobs : observablyEqual st1 st2)
      (hl : ∀ id' ∈ readVarsStmt s, st1.lookupLocal id' = st2.lookupLocal id')
      (hfv : id ∈ freeVarsStmt s) (hnot : id ∉ readVarsStmt s) :
      (evalStmt st1 s).lookupLocal id = (evalStmt st2 s).lookupLocal id := by
    match s with
    | .skip => cases hfv
    | .seq s1 s2 =>
      simp only [freeVarsStmt, readVarsStmt, List.mem_append] at hfv hnot
      simp only [evalStmt]
      let hl1 : ∀ id' ∈ readVarsStmt s1, st1.lookupLocal id' = st2.lookupLocal id' :=
        fun id' h' => hl id' (by simpa [readVarsStmt, List.mem_append] using Or.inl h')
      let hl2 : ∀ id' ∈ readVarsStmt s2,
          (evalStmt st1 s1).lookupLocal id' = (evalStmt st2 s1).lookupLocal id' :=
        fun id' hr' => by
          by_cases h1' : id' ∈ readVarsStmt s1
          · exact lookupLocal_after_eval_read st1 st2 s1 hobs hl1 id' h1'
          · exact lookupLocal_eval_pre_read st1 st2 s1 id' hobs hl1 h1'
              (hl id' (by simpa [readVarsStmt, List.mem_append] using Or.inr hr'))
      by_cases hfv1 : id ∈ freeVarsStmt s1
      · have ih := lookupLocal_bind_post st1 st2 s1 id hobs hl1 hfv1 (not_mem_or_left hnot)
        by_cases hfv2 : id ∈ freeVarsStmt s2
        · exact lookupLocal_bind_post (evalStmt st1 s1) (evalStmt st2 s1) s2 id
            (evalStmt_obs_congr_read st1 st2 s1 hobs hl1) hl2 hfv2 (not_mem_or_right hnot)
        · simp [ih, lookupLocal_evalStmt_unused (evalStmt st1 s1) s2 id hfv2,
            lookupLocal_evalStmt_unused (evalStmt st2 s1) s2 id hfv2]
      · have hfv2 : id ∈ freeVarsStmt s2 := by
          rcases hfv with hfv1' | hfv2'
          · exact absurd hfv1' hfv1
          · exact hfv2'
        exact lookupLocal_bind_post (evalStmt st1 s1) (evalStmt st2 s1) s2 id
          (evalStmt_obs_congr_read st1 st2 s1 hobs hl1) hl2 hfv2 (not_mem_or_right hnot)
    | .letBind name e =>
      simp only [freeVarsStmt, readVarsStmt, List.mem_cons] at hfv hnot
      rcases hfv with heq | hmem
      · subst heq
        simp [evalStmt, evalExpr_obs_agree st1 st2 e hobs
          (λ id' hfree => hl id' (by simpa [readVarsStmt] using hfree))]
      · exact absurd hmem hnot
    | .sstore slot e =>
      simp only [freeVarsStmt, readVarsStmt] at hfv hnot
      exact absurd hfv hnot
    | .ifRevert cond =>
      simp only [freeVarsStmt, readVarsStmt] at hfv hnot
      exact absurd hfv hnot
    | .log0 _ =>
      simp only [freeVarsStmt, readVarsStmt] at hfv hnot
      exact absurd hfv hnot
    | .log1 _ data =>
      simp only [freeVarsStmt, readVarsStmt] at hfv hnot
      exact absurd hfv hnot
    | .revert0 => cases hfv

  theorem lookupLocal_eval_pre_read (st1 st2 : IRState) (s1 : Stmt) (id : Ident)
      (hobs : observablyEqual st1 st2)
      (hl1 : ∀ id' ∈ readVarsStmt s1, st1.lookupLocal id' = st2.lookupLocal id')
      (h₁ : id ∉ readVarsStmt s1) (heq : st1.lookupLocal id = st2.lookupLocal id) :
      (evalStmt st1 s1).lookupLocal id = (evalStmt st2 s1).lookupLocal id := by
    by_cases hfv : id ∈ freeVarsStmt s1
    · exact lookupLocal_bind_post st1 st2 s1 id hobs hl1 hfv h₁
    · simp [lookupLocal_evalStmt_unused st1 s1 id hfv,
        lookupLocal_evalStmt_unused st2 s1 id hfv, heq]

  theorem lookupLocal_after_eval_read (st1 st2 : IRState) (s : Stmt) (hobs : observablyEqual st1 st2)
      (hlookup : ∀ id ∈ readVarsStmt s, st1.lookupLocal id = st2.lookupLocal id) :
      ∀ id ∈ readVarsStmt s,
        (evalStmt st1 s).lookupLocal id = (evalStmt st2 s).lookupLocal id := by
    match s with
    | .skip => simpa using hlookup
    | .seq s1 s2 =>
      intro id hmem
      have hmem' : id ∈ readVarsStmt s1 ∨ id ∈ readVarsStmt s2 := by
        simpa [readVarsStmt, List.mem_append] using hmem
      by_cases h₂ : id ∈ readVarsStmt s2
      · have hl1 : ∀ id ∈ readVarsStmt s1, st1.lookupLocal id = st2.lookupLocal id := by
          intro id hmem
          exact hlookup id (by simpa [readVarsStmt, List.mem_append] using Or.inl hmem)
        have hobs' := evalStmt_obs_congr_read st1 st2 s1 hobs hl1
        have hlookup' : ∀ id ∈ readVarsStmt s2,
            (evalStmt st1 s1).lookupLocal id = (evalStmt st2 s1).lookupLocal id := by
          intro id hmem
          by_cases h₁ : id ∈ readVarsStmt s1
          · exact lookupLocal_after_eval_read st1 st2 s1 hobs hl1 id h₁
          · exact lookupLocal_eval_pre_read st1 st2 s1 id hobs hl1 h₁
              (hlookup id (by simpa [readVarsStmt, List.mem_append] using Or.inr hmem))
        simpa [evalStmt] using
          lookupLocal_after_eval_read (evalStmt st1 s1) (evalStmt st2 s1) s2 hobs' hlookup' id h₂
      · have h₁ : id ∈ readVarsStmt s1 := by
          cases hmem' with
          | inl h₁' => exact h₁'
          | inr h₂' => exact absurd h₂' h₂
        have hl1 : ∀ id' ∈ readVarsStmt s1, st1.lookupLocal id' = st2.lookupLocal id' := by
          intro id' hmem'
          exact hlookup id' (by simpa [readVarsStmt, List.mem_append] using Or.inl hmem')
        have ih := lookupLocal_after_eval_read st1 st2 s1 hobs hl1 id h₁
        rw [evalStmt]
        by_cases hfv2 : id ∈ freeVarsStmt s2
        · exact lookupLocal_bind_post (evalStmt st1 s1) (evalStmt st2 s1) s2 id
            (evalStmt_obs_congr_read st1 st2 s1 hobs hl1)
            (fun id' hr' => by
              by_cases h1' : id' ∈ readVarsStmt s1
              · exact lookupLocal_after_eval_read st1 st2 s1 hobs hl1 id' h1'
              · exact lookupLocal_eval_pre_read st1 st2 s1 id' hobs hl1 h1'
                  (hlookup id' (by simpa [readVarsStmt, List.mem_append] using Or.inr hr')))
            hfv2 h₂
        · simp [lookupLocal_evalStmt_unused (evalStmt st1 s1) s2 id hfv2,
            lookupLocal_evalStmt_unused (evalStmt st2 s1) s2 id hfv2, ih]
    | .letBind bindName e =>
      intro id hmem
      have hfree : id ∈ freeVarsExpr e := by simpa [readVarsStmt] using hmem
      by_cases heq : id = bindName
      · subst heq
        simp [evalStmt, evalExpr_obs_agree st1 st2 e hobs
          (λ id' hfree' => hlookup id' (by simpa [readVarsStmt] using hfree'))]
      · have hne : bindName ≠ id := Ne.symm heq
        simp [evalStmt, IRState.lookupLocal_setLocal_ne st1 bindName id (evalExpr st1 e) hne,
          IRState.lookupLocal_setLocal_ne st2 bindName id (evalExpr st2 e) hne,
          hlookup id (by simpa [readVarsStmt] using hfree)]
    | .sstore slot e =>
      intro id hmem
      simpa [evalStmt, lookupLocal_setSlot, readVarsStmt] using
        hlookup id (by simpa [readVarsStmt] using hmem)
    | .ifRevert cond =>
      intro id hmem
      have heval := evalExpr_obs_agree st1 st2 cond hobs
        (λ id hmem => hlookup id (by simpa [readVarsStmt] using hmem))
      by_cases hc : evalExpr st1 cond = 1
      · have hc2 : evalExpr st2 cond = 1 := by simpa [heval] using hc
        simp [evalStmt_ifRevert, hc, hc2, IRState.lookupLocal]
        exact hlookup id hmem
      · have hc2 : evalExpr st2 cond ≠ 1 := by
          intro h
          rw [← heval] at h
          exact hc h
        simp [evalStmt_ifRevert, hc, hc2, IRState.lookupLocal]
        exact hlookup id hmem
    | .log0 _ =>
      intro id hmem
      simp [readVarsStmt] at hmem
    | .log1 _ data =>
      intro id hmem
      simpa [evalStmt, IRState.lookupLocal, readVarsStmt] using
        hlookup id (by simpa [readVarsStmt] using hmem)
    | .revert0 =>
      intro id hmem
      simpa [evalStmt, IRState.lookupLocal, readVarsStmt] using
        hlookup id (by simp [readVarsStmt] at hmem)

  theorem evalStmt_obs_congr_read (st1 st2 : IRState) (s : Stmt) (hobs : observablyEqual st1 st2)
      (hlookup : ∀ id ∈ readVarsStmt s, st1.lookupLocal id = st2.lookupLocal id) :
      observablyEqual (evalStmt st1 s) (evalStmt st2 s) := by
    match s with
    | .skip => exact hobs
    | .seq s1 s2 =>
      have hl1 : ∀ id ∈ readVarsStmt s1, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [readVarsStmt, List.mem_append] using Or.inl hmem)
      have h1 := evalStmt_obs_congr_read st1 st2 s1 hobs hl1
      have hl2 : ∀ id ∈ readVarsStmt s2,
          (evalStmt st1 s1).lookupLocal id = (evalStmt st2 s1).lookupLocal id := by
        intro id hmem
        by_cases h₁ : id ∈ readVarsStmt s1
        · exact lookupLocal_after_eval_read st1 st2 s1 hobs hl1 id h₁
        · exact lookupLocal_eval_pre_read st1 st2 s1 id hobs hl1 h₁
            (hlookup id (by simpa [readVarsStmt, List.mem_append] using Or.inr hmem))
      simp only [evalStmt, observablyEqual]
      exact evalStmt_obs_congr_read (evalStmt st1 s1) (evalStmt st2 s1) s2 h1 hl2
    | .letBind bindName e =>
      simp only [evalStmt, observablyEqual, IRState.setLocal]
      exact hobs
    | .sstore slot e =>
      have hfree : ∀ id ∈ freeVarsExpr e, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [readVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 e hobs hfree
      simp only [evalStmt_sstore, observablyEqual, heval, IRState.setSlot]
      exact ⟨by simp [hobs.1], hobs.2.1, hobs.2.2⟩
    | .ifRevert cond =>
      have hfree : ∀ id ∈ freeVarsExpr cond, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [readVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 cond hobs hfree
      by_cases hc : evalExpr st1 cond = 1
      · have hc2 : evalExpr st2 cond = 1 := by simpa [heval] using hc
        simp only [evalStmt_ifRevert, observablyEqual, hc, hc2]
        exact ⟨hobs.1, hobs.2.1, rfl⟩
      · have hc2 : evalExpr st2 cond ≠ 1 := by
          intro h
          rw [← heval] at h
          exact hc h
        simp only [evalStmt_ifRevert, observablyEqual, hc, hc2]
        exact ⟨hobs.1, hobs.2.1, hobs.2.2⟩
    | .log0 topic =>
      have hlogs : st1.logs ++ [(topic, 0)] = st2.logs ++ [(topic, 0)] := by simp [hobs.2.1]
      simp only [evalStmt_log0, observablyEqual]
      exact ⟨hobs.1, hlogs, hobs.2.2⟩
    | .log1 topic data =>
      have hfree : ∀ id ∈ freeVarsExpr data, st1.lookupLocal id = st2.lookupLocal id := by
        intro id hmem
        exact hlookup id (by simpa [readVarsStmt] using hmem)
      have heval := evalExpr_obs_agree st1 st2 data hobs hfree
      have hlogs : st1.logs ++ [(topic, evalExpr st2 data)] = st2.logs ++ [(topic, evalExpr st2 data)] := by
        simp [hobs.2.1]
      simp only [evalStmt_log1, observablyEqual, heval]
      exact ⟨hobs.1, hlogs, hobs.2.2⟩
    | .revert0 =>
      simp only [evalStmt_revert0, observablyEqual]
      exact ⟨hobs.1, hobs.2.1, trivial⟩
end

theorem evalStmt_setLocal_unused_obs (st : IRState) (name : Ident) (v : Nat) (s : Stmt)
    (h : name ∉ freeVarsStmt s) :
    observablyEqual (evalStmt (st.setLocal name v) s) (evalStmt st s) := by
  induction s generalizing st name v with
  | skip =>
    simp only [evalStmt_skip, observablyEqual]
    exact observablyEqual_setLocal st name v
  | seq s1 s2 ih1 ih2 =>
    simp only [freeVarsStmt, List.mem_append] at h
    have hs1 := not_mem_or_left h
    have hs2 := not_mem_or_right h
    have h1 := ih1 st name v hs1
    have hl2 : ∀ id ∈ freeVarsStmt s2,
        (evalStmt (st.setLocal name v) s1).lookupLocal id = (evalStmt st s1).lookupLocal id := by
      intro id hmem
      by_cases h₁ : id ∈ freeVarsStmt s1
      · exact lookupLocal_after_eval_agree (st.setLocal name v) st s1 (observablyEqual_setLocal st name v)
          (λ id hmem => by
            by_cases heq : id = name
            · rw [heq] at hmem
              exact absurd hmem hs1
            · exact IRState.lookupLocal_setLocal_ne st name id v (Ne.symm heq)) id h₁
      · have hne : id ≠ name := by
          intro heq
          rw [heq] at hmem
          exact absurd hmem hs2
        simp [lookupLocal_evalStmt_unused st s1 id h₁,
          lookupLocal_evalStmt_unused (st.setLocal name v) s1 id h₁,
          IRState.lookupLocal_setLocal_ne st name id v (Ne.symm hne)]
    rw [evalStmt_seq, evalStmt_seq, observablyEqual]
    exact evalStmt_obs_congr (evalStmt (st.setLocal name v) s1) (evalStmt st s1) s2 h1 hl2
  | letBind other e =>
    simp only [freeVarsStmt, List.mem_cons] at h
    have hfree : name ∉ freeVarsExpr e := by
      intro hmem
      apply h
      simp [hmem]
    simp only [evalStmt_letBind, observablyEqual, IRState.setLocal]
    trivial
  | sstore slot e =>
    simp only [freeVarsStmt] at h
    simp only [evalStmt_sstore, observablyEqual, evalExpr_setLocal_unused st name v e h, IRState.setSlot]
    trivial
  | ifRevert cond =>
    simp only [freeVarsStmt] at h
    by_cases hc : evalExpr st cond = 1
    · simp [evalStmt_ifRevert, observablyEqual, evalExpr_setLocal_unused st name v cond h, hc]
      trivial
    · simp [evalStmt_ifRevert, observablyEqual, evalExpr_setLocal_unused st name v cond h, hc]
      trivial
  | log0 topic =>
    simp only [freeVarsStmt] at h
    simp only [evalStmt_log0, observablyEqual]
    trivial
  | log1 topic data =>
    simp only [freeVarsStmt] at h
    simp only [evalStmt_log1, observablyEqual, evalExpr_setLocal_unused st name v data h]
    trivial
  | revert0 =>
    simp only [evalStmt_revert0, observablyEqual]
    trivial

theorem evalStmt_unused_bind_ignored (st : IRState) (name : Ident) (e : Expr) (rest : Stmt)
    (h : name ∉ freeVarsStmt rest) :
    observablyEqual (evalStmt (evalStmt st (.letBind name e)) rest) (evalStmt st rest) :=
  evalStmt_setLocal_unused_obs st name (evalExpr st e) rest h

theorem lookupLocal_evalStmt_setLocal_unused (st : IRState) (setName id : Ident) (v : Nat) (s : Stmt)
    (hne : setName ≠ id) (h : setName ∉ freeVarsStmt s) :
    (evalStmt (st.setLocal setName v) s).lookupLocal id = (evalStmt st s).lookupLocal id := by
  by_cases hmem : id ∈ freeVarsStmt s
  · have hlookup : ∀ id' ∈ freeVarsStmt s, (st.setLocal setName v).lookupLocal id' = st.lookupLocal id' := by
      intro id' hmem'
      have hne' : setName ≠ id' := λ heq => absurd (heq ▸ hmem') h
      simp [IRState.lookupLocal_setLocal_ne st setName id' v hne']
    simpa using lookupLocal_after_eval_agree (st.setLocal setName v) st s
      (observablyEqual_setLocal st setName v) hlookup id hmem
  · simp [lookupLocal_evalStmt_unused st s id hmem,
      lookupLocal_evalStmt_unused (st.setLocal setName v) s id hmem,
      IRState.lookupLocal_setLocal_ne st setName id v hne]

theorem lookupLocal_unused_bind_ignored (st : IRState) (name id : Ident) (e : Expr) (rest : Stmt)
    (hne : name ≠ id) (h : name ∉ freeVarsStmt rest) :
    (evalStmt (evalStmt st (.letBind name e)) rest).lookupLocal id = (evalStmt st rest).lookupLocal id := by
  rw [evalStmt_letBind]
  by_cases hmem : id ∈ freeVarsStmt rest
  · simpa using lookupLocal_after_eval_agree (st.setLocal name (evalExpr st e)) st rest
      (observablyEqual_setLocal st name (evalExpr st e))
      (λ id' hmem' => by
        by_cases hn : id' = name
        · subst hn; exact absurd hmem' h
        · simp [IRState.lookupLocal_setLocal_ne st name id' (evalExpr st e) (Ne.symm hn)]) id hmem
  · simp [lookupLocal_evalStmt_unused st rest id hmem,
      lookupLocal_evalStmt_unused (st.setLocal name (evalExpr st e)) rest id hmem,
      IRState.lookupLocal_setLocal_ne st name id (evalExpr st e) hne]

end Lsc.Compile.IR
