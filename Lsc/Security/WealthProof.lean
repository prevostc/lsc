import Lsc.Lang.Chain
import Lsc.Lang.TxTheorems
import Lsc.Security.Wealth
import Lsc.Security.InvariantTheorems

/-!
Proofs of the generic extraction and solvency theorems. Statements live in
`WealthTheorems`.
-/

namespace Lsc.Security.Proof

variable {S X E ε : Type} {C : Spec S X E ε}

theorem no_unauthorized_extraction [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : World S X E → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C self Inv claim Auth)
    (hP : PreservesInv C self Inv) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong self rely tr w)
    (hA : NoAuthAlong self Auth a tr w) :
    claim a w ≤ claim a (run self tr w) := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have hw' : Inv (step self (.call c) w) := hP c w hw
      have hle : claim a w ≤ claim a (step self (.call c) w) :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step self (.call c) w) hw' hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      have hle : claim a w ≤ claim a { w with ext := x' } := hM w x' a hr
      exact Nat.le_trans hle (ih { w with ext := x' } hw' htl hA)

theorem no_unauthorized_extraction_at [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : World S X E → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C self Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr w) (hR : RelyAlong self rely tr w)
    (hA : NoAuthAlong self Auth a tr w) :
    claim a w ≤ claim a (run self tr w) := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have ⟨hs, hWtl⟩ := hW
      have hw' : Inv (step self (.call c) w) := hP c w hs hw
      have hle : claim a w ≤ claim a (step self (.call c) w) :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step self (.call c) w) hw' hWtl hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      have hle : claim a w ≤ claim a { w with ext := x' } := hM w x' a hr
      exact Nat.le_trans hle (ih { w with ext := x' } hw' hW htl hA)

theorem solvent_run [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : World S X E → X → Prop}
    {self : Address}
    (hP : PreservesInv C self Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr w) (hR : RelyAlong self rely tr w) :
    Solvent claim holdings self (run self tr w) :=
  hS self _ (inv_run hP hE hw tr hW hR)

theorem solvent_run_at [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : World S X E → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr w) (hR : RelyAlong self rely tr w) :
    Solvent claim holdings self (run self tr w) :=
  hS _ (inv_run_at hP hE hw tr hW hR)

theorem sum_update_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i n) + f i = H.sum f + n := by
  have hsum := Finset.sum_erase_add (s := H) (f := f) hi
  have hsum' := Finset.sum_erase_add (s := H) (f := Function.update f i n) hi
  have hframe : (H.erase i).sum (Function.update f i n) = (H.erase i).sum f :=
    Finset.sum_congr rfl fun y hy =>
      Function.update_of_ne (Finset.ne_of_mem_erase hy) n f
  rw [← hsum', Function.update_self, hframe, Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc, hsum]

theorem sum_update_not_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∉ H) (n : Nat) :
    H.sum (Function.update f i n) = H.sum f :=
  Finset.sum_congr rfl fun y hy =>
    Function.update_of_ne (by intro h; subst h; exact hi hy) n f

theorem Claim.eval_apply (c : Claim S X E) (a : Address) (w : World S X E) :
    Claim.eval c a w = c.tokens a w + c.native a w :=
  rfl

theorem Claim.eval_ofFun (f : Address → World S X E → Nat)
    (a : Address) (w : World S X E) :
    Claim.ofFun (S := S) (X := X) (E := E) f a w = f a w :=
  Nat.add_zero _

theorem Claim.eval_ofSelf (c : Address → S → Nat) (a : Address)
    (w : World S X E) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w = c a w.self :=
  Claim.eval_ofFun _ a w

theorem Claim.eval_ofNative (c : Address → S → Nat) (a : Address)
    (w : World S X E) :
    Claim.ofNative (S := S) (X := X) (E := E) c a w = c a w.self :=
  Nat.zero_add _

theorem Claim.ofSelf_congr (c : Address → S → Nat)
    {w w' : World S X E} {a : Address} (h : w.self = w'.self) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w =
      Claim.ofSelf (S := S) (X := X) (E := E) c a w' := by
  simp [Claim.eval_ofSelf, h]

theorem ClaimMonoEnv.of_self (c : Address → S → Nat)
    (rely : World S X E → X → Prop) :
    ClaimMonoEnv (Claim.ofSelf (S := S) (X := X) (E := E) c) rely := by
  intro _ _ _ _; exact Nat.le_refl _

theorem ClaimMonoEnv.of_native (c : Address → S → Nat)
    (rely : World S X E → X → Prop) :
    ClaimMonoEnv (Claim.ofNative (S := S) (X := X) (E := E) c) rely := by
  intro _ _ _ _; exact Nat.le_refl _

theorem Claim.booksOnly_ofSelf (c : Address → S → Nat) :
    Claim.booksOnly (Claim.ofSelf (S := S) (X := X) (E := E) c) := by
  intro a w w' h; simp [Claim.eval_ofSelf, h]

theorem Claim.booksOnly_ofNative (c : Address → S → Nat) :
    Claim.booksOnly (Claim.ofNative (S := S) (X := X) (E := E) c) := by
  intro a w w' h; simp [Claim.eval_ofNative, h]

theorem ClaimMonoCredit.of_books [HasCreditValue X] {claim : Claim S X E}
    (h : Claim.booksOnly claim) : ClaimMonoCredit claim := by
  intro w v a
  exact h a (World.creditValue w v) w (World.creditValue_self w v)

theorem selfNative_eq_nativeBalance (w : World S ExtState E) :
    selfNative w = World.nativeBalance w :=
  rfl

theorem native_outflow_victim {claim : Claim S X E} {dst : Address} {v : Nat}
    {w w' : World S X E} {a : Address}
    (h : NativeOutflow claim dst v w w') (hlt : claim a w' < claim a w) :
    a = dst := by
  by_contra hne
  exact Nat.lt_irrefl _ (h.frame a hne ▸ hlt)

theorem sendRaw_books {claim : Claim S X E} (hB : Claim.booksOnly claim)
    (dst amount : Nat) {ctx : Ctx} {w w' : World S X E} {ok : Bool}
    (h : Tx.run (Tx.sendRaw (ε := ε) dst amount) ctx w = .ok (ok, w')) :
    w'.self = w.self ∧ ∀ a, claim a w' = claim a w := by
  simp [Tx.run, Tx.sendRaw] at h
  cases hs : w.oracle.send dst amount w.ext with
  | none =>
    simp [hs] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  | some x' =>
    simp [hs] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun a => hB a _ w rfl⟩

theorem native_send_books {claim : Claim S X E} {a : Asset} (hB : Claim.booksOnly claim)
    (dst : Address) (amount : Amount a) (err : ε) {ctx : Ctx} {w w' : World S X E}
    (h : Tx.run (Native.send dst amount err) ctx w = .ok ((), w')) :
    w'.self = w.self ∧ ∀ a, claim a w' = claim a w := by
  unfold Native.send at h
  simp [Tx.run, Tx.sendRaw] at h
  cases hs : w.oracle.send dst amount.raw w.ext with
  | none =>
    simp [hs, Tx.require] at h
  | some x' =>
    simp [hs, Tx.require] at h
    have hrun : Tx.run (Tx.sendRaw (ε := ε) dst amount.raw) ctx w =
        .ok (true, { w with ext := x' }) := by
      simp [Tx.run, Tx.sendRaw, hs]
    have ⟨_, hcl⟩ := sendRaw_books (claim := claim) hB dst amount.raw hrun
    cases h
    exact ⟨rfl, hcl⟩

theorem sendRaw_debit [HasSelfBalance X] {dst v : Nat} {ctx : Ctx}
    {w w' : World S X E}
    (hO : DebitsOnSend w.oracle)
    (h : Tx.run (Tx.sendRaw (ε := ε) dst v) ctx w = .ok (true, w')) :
    selfNative w' + v = selfNative w := by
  simp [Tx.run, Tx.sendRaw] at h
  cases hs : w.oracle.send dst v w.ext with
  | none => simp [hs] at h
  | some x' =>
    simp [hs] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hO dst v w.ext x' hs

theorem NativeSendAuth.of_debits [HasSelfBalance X] {claim : Claim S X E}
    {dst : Address} {v : Nat} {w w' : World S X E}
    (hO : DebitsOnSend w.oracle)
    (hsend : w.oracle.send dst v w.ext = some w'.ext)
    (hout : NativeOutflow claim dst v w w') :
    NativeSendAuth claim dst v w w' := by
  refine ⟨hout, ?_⟩
  simpa [selfNative] using hO dst v w.ext w'.ext hsend

theorem NoUnauthorizedDecrease.of_fns [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C} {self : Address}
    (h : ∀ fn, NoUnauthorizedDecreaseFn C Inv claim Auth fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    NoUnauthorizedDecrease C self Inv claim Auth := by
  intro c w a hInv hlt
  have hp : C.payable c.fn = false := hnp c.fn
  by_cases hv : c.value = 0
  · rw [step_eq_worldAfter_of_not_payable self c w hp hv] at hlt
    simpa [Call.ofCtx_toCtx] using h c.fn c.args (c.toCtx self) w a hInv hlt
  · rw [step_reject_value (self := self) hp hv] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

theorem NoUnauthorizedDecrease.of_fns_credit [HasCreditValue X]
    {Inv : World S X E → Prop} {claim : Claim S X E} {Auth : AuthPred C}
    {self : Address}
    [HasPayable C] [HasSelfBalance X]
    (h : ∀ fn, NoUnauthorizedDecreaseCreditFn C Inv claim Auth fn) :
    NoUnauthorizedDecrease C self Inv claim Auth := by
  intro c w a hInv hlt
  rw [step_eq_run self] at hlt
  split_ifs at hlt with hvo hwrap
  · exact (Nat.lt_irrefl _ hlt).elim
  · cases hrun : C.exec c.fn c.args (c.toCtx self) (World.creditValue w c.value) with
    | error _ =>
      rw [hrun] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    | ok p =>
      rw [hrun] at hlt
      simpa [Call.ofCtx_toCtx] using
        h c.fn c.args (c.toCtx self) w a p.1 p.2 hvo hInv hrun hlt
  · exact (Nat.lt_irrefl _ hlt).elim

theorem NoUnauthorizedDecreaseFn_of_native_send {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C} {fn : C.Fn}
    (hAuth : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
      Auth ctx.sender (Call.ofCtx ctx fn args) w)
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      (∀ a, claim a w ≤ claim a w') ∨
        ∃ v, NativeOutflow claim ctx.sender v w w') :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn := by
  intro args ctx w a hInv hdec
  cases hrun : Tx.run (C.exec fn args) ctx w with
  | error _ => simp [worldAfter_error hrun] at hdec
  | ok p =>
    have hdec' : claim a p.2 < claim a w := by
      simpa [worldAfter_ok hrun] using hdec
    cases hok args ctx w p.1 p.2 hInv hrun with
    | inl hge => exact (Nat.not_lt.mpr (hge a) hdec').elim
    | inr hv =>
      obtain ⟨v, hout⟩ := hv
      have ha : a = ctx.sender := native_outflow_victim hout hdec'
      simpa [ha] using hAuth args ctx w

/-- Same as `NoUnauthorizedDecreaseFn_of_native_send`, but `Auth` is
judged on the success path (tight permission such as `amount ≤ balances`). -/
theorem NoUnauthorizedDecreaseFn_of_native_send_ok {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C} {fn : C.Fn}
    (hAuth : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      Auth ctx.sender (Call.ofCtx ctx fn args) w)
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      (∀ a, claim a w ≤ claim a w') ∨
        ∃ v, NativeOutflow claim ctx.sender v w w') :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn := by
  intro args ctx w a hInv hdec
  cases hrun : Tx.run (C.exec fn args) ctx w with
  | error _ => simp [worldAfter_error hrun] at hdec
  | ok p =>
    have hdec' : claim a p.2 < claim a w := by
      simpa [worldAfter_ok hrun] using hdec
    cases hok args ctx w p.1 p.2 hInv hrun with
    | inl hge => exact (Nat.not_lt.mpr (hge a) hdec').elim
    | inr hv =>
      obtain ⟨v, hout⟩ := hv
      have ha : a = ctx.sender := native_outflow_victim hout hdec'
      simpa [ha] using hAuth args ctx w p.1 p.2 hrun

theorem NoUnauthorizedDecreaseFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      claim a w' < claim a w →
      Auth a (Call.ofCtx ctx fn args) w) :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn := by
  intro args ctx w a hInv hdec
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ => simp [worldAfter_error h] at hdec
  | ok p =>
    exact hok args ctx w a p.1 p.2 hInv h (by simpa [worldAfter_ok h] using hdec)

/-- Non-payable `NoUnauthorizedDecreaseFn` yields the credit form: `valueOk`
forces `value = 0`, so `creditValue` is the identity. -/
theorem NoUnauthorizedDecreaseCreditFn_of_fn [HasCreditValue X]
    {Inv : World S X E → Prop} {claim : Claim S X E} {Auth : AuthPred C}
    {fn : C.Fn} [HasPayable C] (hp : C.payable fn = false)
    (h : NoUnauthorizedDecreaseFn C Inv claim Auth fn) :
    NoUnauthorizedDecreaseCreditFn C Inv claim Auth fn := by
  intro args ctx w a ret w' hvo hInv hrun hdec
  have hv : ctx.value = 0 := C.value_eq_zero_of_valueOk hp hvo
  rw [hv, World.creditValue_zero] at hrun
  have hlt : claim a (worldAfter (C.exec fn args) ctx w) < claim a w := by
    simpa [worldAfter_ok hrun] using hdec
  exact h args ctx w a hInv hlt

theorem Conservation.of_fns [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C} {self : Address}
    (h : ∀ fn, ConservesFn C Inv claim inflow fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    Conservation C self Inv claim inflow := by
  intro c w hInv
  have hp : C.payable c.fn = false := hnp c.fn
  by_cases hv : c.value = 0
  · rw [step_eq_worldAfter_of_not_payable self c w hp hv]
    exact h c.fn c.args (c.toCtx self) w hInv
  · rw [step_reject_value (self := self) hp hv]
    refine ⟨∅, fun _ _ => rfl, by simp⟩

theorem ConservesFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (ret : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      ∃ T : Finset Address,
        (∀ a, a ∉ T → claim a w' = claim a w) ∧
        T.sum (fun a => claim a w') ≤
          T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w) :
    ConservesFn C Inv claim inflow fn := by
  intro args ctx w hInv
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ =>
    refine ⟨∅, ?_, ?_⟩
    · intro a _; simp [worldAfter_error h]
    · simp [worldAfter_error h]
  | ok p =>
    simpa [worldAfter_ok h] using hok args ctx w p.1 p.2 hInv h

theorem sum_mul_div_le {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) (num den : Nat)
    (hsum : H.sum f = den) (hpos : 0 < den) :
    H.sum (fun a => f a * num / den) ≤ num := by
  have hmul_right : ∀ (s : Finset α) (g : α → Nat) (n : Nat),
      s.sum g * n = s.sum (fun a => g a * n) := by
    intro s g n
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mul, ih]
  have hmul_left : ∀ (s : Finset α) (g : α → Nat) (n : Nat),
      n * s.sum g = s.sum (fun a => n * g a) := by
    intro s g n
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.mul_add, ih]
  have hle : ∀ (s : Finset α) (g h : α → Nat), (∀ a ∈ s, g a ≤ h a) → s.sum g ≤ s.sum h := by
    intro s g h hh
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Nat.add_le_add (hh a (Finset.mem_insert_self _ _))
        (ih fun x hx => hh x (Finset.mem_insert_of_mem hx))
  have hbound :
      H.sum (fun a => f a * num / den) * den ≤ H.sum (fun a => f a * num) := by
    rw [hmul_right]
    exact hle _ _ _ fun _ _ => Nat.div_mul_le_self _ _
  have hrhs : H.sum (fun a => f a * num) = num * den := by
    have h1 : H.sum (fun a => f a * num) = H.sum (fun a => num * f a) :=
      Finset.sum_congr rfl fun _ _ => Nat.mul_comm _ _
    rw [h1, ← hmul_left, hsum]
  have : H.sum (fun a => f a * num / den) * den ≤ num * den := by
    rw [← hrhs]; exact hbound
  exact Nat.le_of_mul_le_mul_right this hpos

end Lsc.Security.Proof
