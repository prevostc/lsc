import Lsc.Lang.Core

/-!
Proofs of the `Core.effects` frame theorems. Statements and documentation live
in `Lsc.Lang.CoreTheorems`.
-/

namespace Lsc.Proof

variable {S X E ε : Type}

/-- Successful `Op.denote` never mutates `self`. CALLs leave `self` unchanged
(no reentrancy in this slice). -/
theorem Op.effects_frame {Γ : ContractSchema S X E ε} (op : Op) (env : List Nat)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E}
    (h : Tx.run (Op.denote Γ env op) ctx w = .ok (v, w')) :
    w'.self = w.self := by
  cases op with
  | call t sel args ret =>
    simp [Op.denote] at h
    exact Tx.callAsNat_self (S := S) (X := X) (E := E) ret
      (Atom.eval env t) sel (args.map (Atom.eval env)) h
  | view t sel args ret =>
    simp [Op.denote] at h
    exact congrArg World.self
      (Tx.viewAsNat_world (S := S) (X := X) (E := E) ret
        (Atom.eval env t) sel (args.map (Atom.eval env)) h)
  | load _ | loadMap _ _ | loadMap2 _ _ _ | value | timestamp | blockNumber | pure _ =>
    simp [Op.denote] at h
    rw [h.2]
  | sender =>
    have hs : Tx.run (Op.denote Γ env .sender) ctx w = .ok ((ctx.sender : Nat), w) := rfl
    rw [hs] at h
    injection h with hxy
    injection hxy with _ hw
    exact congrArg World.self hw.symm
  | selfAddress =>
    have hs : Tx.run (Op.denote Γ env .selfAddress) ctx w = .ok ((ctx.self : Nat), w) := rfl
    rw [hs] at h
    injection h with hxy
    injection hxy with _ hw
    exact congrArg World.self hw.symm
  | addChecked _ _ | subChecked _ _ | mulChecked _ _ | divChecked _ _
  | mulDivDown _ _ _ | mulDivUp _ _ _ | pow10 _ =>
    simp [Op.denote] at h
    repeat' split at h
    all_goals simp at h
    all_goals rw [h.2]

/-- If `f` is not among `s`'s writes, a successful `Stmt.denote` leaves projection `P` unchanged. -/
theorem Stmt.effects_frame_on {α} {Γ : ContractSchema S X E ε} (P : S → α)
    (s : Stmt) (env : List Nat) (f : Nat)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    P w'.self = P w.self := by
  cases s with
  | store i x =>
    simp [Stmt.denote] at h
    subst h
    exact hStore i w.self _ (fun heq => hf (by simp [Stmt.effects, heq]))
  | storeMap i k x =>
    simp [Stmt.denote] at h
    subst h
    exact hStoreMap i w.self _ (fun heq => hf (by simp [Stmt.effects, heq]))
  | storeMap2 i k₁ k₂ x =>
    simp [Stmt.denote] at h
    subst h
    exact hStoreMap2 i w.self _ (fun heq => hf (by simp [Stmt.effects, heq]))
  | require c err args =>
    simp [Stmt.denote] at h
    split at h
    · simp at h
      rw [h]
    · simp at h
  | emit ev args =>
    simp [Stmt.denote] at h
    subst h
    rfl
  | revert err args =>
    simp [Stmt.denote] at h
  | call t sel args ret =>
    simp [Stmt.denote] at h
    cases hRun : Tx.run (Op.denote Γ env (.call t sel args ret)) ctx w with
    | error _ => simp [hRun] at h
    | ok p =>
      rcases p with ⟨val, w1⟩
      simp [hRun] at h
      subst h
      exact congrArg P (Op.effects_frame (.call t sel args ret) env hRun)
  | view t sel args ret =>
    simp [Stmt.denote] at h
    cases hRun : Tx.run (Op.denote Γ env (.view t sel args ret)) ctx w with
    | error _ => simp [hRun] at h
    | ok p =>
      rcases p with ⟨val, w1⟩
      simp [hRun] at h
      subst h
      exact congrArg P (Op.effects_frame (.view t sel args ret) env hRun)

/-- Scalar specialisation of `Stmt.effects_frame_on`. -/
theorem Stmt.effects_frame {Γ : ContractSchema S X E ε} (s : Stmt) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Stmt.effects_frame_on (Γ.st.scalar f) s env f
    (fun i σ v hne => hΓ f i σ v hne)
    (fun i σ m _ => hMap1 i σ m)
    (fun i σ m _ => hMap2 i σ m)
    hf h

/-- If `f` is not among `c`'s writes, a successful `Core.denote` leaves projection `P` unchanged. -/
theorem effects_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    P w'.self = P w.self := by
  induction c generalizing env ctx w w' with
  | ret r =>
    simp [Core.denote] at h
    rw [h.2]
  | opTail op =>
    simp [Core.denote] at h
    exact congrArg P (Op.effects_frame op env h)
  | opTailAddr op =>
    simp [Core.denote] at h
    exact congrArg P (Op.effects_frame op env h)
  | opTailFlag op =>
    simp [Core.denote] at h
    exact congrArg P (Op.effects_frame op env h)
  | stmtTail s =>
    simp [Core.denote] at h
    exact Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hf h
  | revertTail err args =>
    simp [Core.denote] at h
  | letOp op k ih =>
    simp [Core.denote, Tx.run_bind] at h
    cases hOp : Tx.run (Op.denote Γ env op) ctx w with
    | error _ => simp [hOp] at h
    | ok p =>
      rcases p with ⟨a, w1⟩
      simp [hOp] at h
      have hself := Op.effects_frame op env hOp
      have hf' : f ∉ (Core.effects k).writes := by
        simpa [Core.effects, Effects.append, Op.effects_writes] using hf
      rw [ih (a :: env) hf' h, hself]
  | seq s k ih =>
    simp [Core.denote, Tx.run_bind] at h
    have hfsk : f ∉ (Stmt.effects s).writes ∧ f ∉ (Core.effects k).writes := by
      simpa [Core.effects, Effects.append, List.mem_append, not_or] using hf
    cases hS : Tx.run (Stmt.denote Γ env s) ctx w with
    | error _ => simp [hS] at h
    | ok p =>
      rcases p with ⟨u, w1⟩
      simp [hS] at h
      have hs :=
        Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hfsk.1 hS
      rw [ih env hfsk.2 h, hs]
  | letPure p args k ih =>
    simp [Core.denote] at h
    exact ih (Prim.eval p (args.map (·.eval env)) :: env) hf h
  | ite c a b iha ihb =>
    simp [Core.denote, Tx.run_ite] at h
    have hfab : f ∉ (Core.effects a).writes ∧ f ∉ (Core.effects b).writes := by
      simpa [Core.effects, Effects.append, List.mem_append, not_or] using hf
    split at h
    · exact iha env hfab.1 h
    · exact ihb env hfab.2 h

/-- A successful run does not change scalar field `f` unless `f` is in `writes`. -/
theorem effects_frame {Γ : ContractSchema S X E ε} {t} (c : Core t) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  effects_frame_on c env f (Γ.st.scalar f)
    (fun i σ v hne => hΓ f i σ v hne)
    (fun i σ m _ => hMap1 i σ m)
    (fun i σ m _ => hMap2 i σ m)
    hf h

/-- A successful run does not change mapping field `f` unless `f` is in `writes`. -/
theorem effects_frame_map1 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map1 f (Γ.st.scalarUpd i σ v) = Γ.st.map1 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map1Upd i σ m) = Γ.st.map1 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map2Upd i σ m) = Γ.st.map1 f σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map1 f w'.self = Γ.st.map1 f w.self :=
  effects_frame_on c env f (Γ.st.map1 f) hΓ hMap1 hMap2 hf h

/-- A successful run does not change a double mapping field `f` unless `f` is in `writes`. -/
theorem effects_frame_map2 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map2 f (Γ.st.scalarUpd i σ v) = Γ.st.map2 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map1Upd i σ m) = Γ.st.map2 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map2Upd i σ m) = Γ.st.map2 f σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map2 f w'.self = Γ.st.map2 f w.self :=
  effects_frame_on c env f (Γ.st.map2 f) hΓ hMap1 hMap2 hf h

/-- `effects_frame_on` on `worldAfter`: reverts keep `self`, so an unwritten
projection is unchanged whether the Core run succeeds or reverts. -/
theorem worldAfter_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Core.effects c).writes)
    (ctx : Ctx) (w : World S X E) :
    P (Lang.worldAfter (Core.denote Γ c env) ctx w).self = P w.self := by
  cases h : Tx.run (Core.denote Γ c env) ctx w with
  | error _ => simp [Lang.worldAfter, h]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [Lang.worldAfter, h]
    exact effects_frame_on c env f P hStore hStoreMap hStoreMap2 hf h


/-! ### `map_denote_*` certificate lemmas -/

/-- Push `f <$>` through `letOp`. Certificate wrap of an Amount/Bool body. -/
theorem map_denote_letOp {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v => f <$> Core.denote Γ k (v :: env) := by
  simp only [Core.denote]
  exact Tx.map_bind f (Op.denote Γ env op) (fun v => Core.denote Γ k (v :: env))

/-- Push `f <$>` through `seq`. -/
theorem map_denote_seq {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ => f <$> Core.denote Γ k env := by
  simp only [Core.denote]
  exact Tx.map_bind f (Stmt.denote Γ env s) (fun _ => Core.denote Γ k env)

/-- `f <$> ret` is `pure (f (eval r))`. -/
theorem map_denote_ret {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (r : RetExpr t) (env : List Nat) :
    f <$> Core.denote Γ (.ret r) env = pure (f (r.eval env)) := by
  simp only [Core.denote, Tx.map_pure]

/-- Push `f <$>` through `ite`. -/
theorem map_denote_ite {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (c : Cond) (a b : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.ite c a b) env =
      if c.denote env then f <$> Core.denote Γ a env
      else f <$> Core.denote Γ b env :=
  Tx.map_ite (c.denote env) f (Core.denote Γ a env) (Core.denote Γ b env)

/-- `letPure` is substitution; the wrap stays on the continuation. -/
theorem map_denote_letPure {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core t)
    (env : List Nat) :
    f <$> Core.denote Γ (.letPure p args k) env =
      f <$> Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) := by
  simp only [Core.denote]

/-- Tail op: wrap stays on the primitive. -/
theorem map_denote_opTail {γ : Type} (f : Nat → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTail op) env = f <$> Op.denote Γ env op := by
  simp only [Core.denote]

theorem map_denote_opTailFlag {γ : Type} (f : Nat → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTailFlag op) env = f <$> Op.denote Γ env op := by
  simp only [Core.denote]

theorem map_denote_opTailAddr {γ : Type} (f : Address → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTailAddr op) env =
      f <$> (Op.denote Γ env op : Tx S X E ε Nat) := by
  simp only [Core.denote]

theorem map_denote_stmtTail {γ : Type} (f : Unit → γ)
    (Γ : ContractSchema S X E ε) (s : Stmt) (env : List Nat) :
    f <$> Core.denote Γ (.stmtTail s) env = f <$> Stmt.denote Γ env s := by
  simp only [Core.denote]

theorem map_denote_revertTail {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (err : Nat) (args : List Atom) (env : List Nat) :
    f <$> Core.denote Γ (.revertTail err args) env =
      Tx.revert (Γ.err.build err (args.map (·.eval env))) := by
  simp only [Core.denote, Tx.map_revert]

/-- Amount wrap through `letOp`. First-order key for `lsc_reify`. -/
theorem map_denote_letOp_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Amount.ofWord (a := a) <$> Core.denote Γ k (v :: env) :=
  map_denote_letOp (Amount.ofWord (a := a)) Γ op k env

theorem map_denote_seq_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Amount.ofWord (a := a) <$> Core.denote Γ k env :=
  map_denote_seq (Amount.ofWord (a := a)) Γ s k env

theorem map_denote_ret_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (r : RetExpr .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.ret r) env =
      pure (Amount.ofWord (a := a) (r.eval env)) :=
  map_denote_ret (Amount.ofWord (a := a)) Γ r env

theorem map_denote_ite_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.ite c th el) env =
      if c.denote env then Amount.ofWord (a := a) <$> Core.denote Γ th env
      else Amount.ofWord (a := a) <$> Core.denote Γ el env :=
  map_denote_ite (Amount.ofWord (a := a)) Γ c th el env

theorem map_denote_letPure_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core .word)
    (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.letPure p args k) env =
      Amount.ofWord (a := a) <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  map_denote_letPure (Amount.ofWord (a := a)) Γ p args k env

/-- Bool wrap through `letOp`. `RetTy.flag` denotes to `Nat`. -/
theorem map_denote_letOp_natToBool
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Tx.natToBool <$> Core.denote Γ k (v :: env) :=
  map_denote_letOp Tx.natToBool Γ op k env

theorem map_denote_seq_natToBool
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Tx.natToBool <$> Core.denote Γ k env :=
  map_denote_seq Tx.natToBool Γ s k env

theorem map_denote_ret_natToBool
    (Γ : ContractSchema S X E ε) (r : RetExpr .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.ret r) env =
      pure (Tx.natToBool (r.eval env)) :=
  map_denote_ret Tx.natToBool Γ r env

theorem map_denote_ite_natToBool
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.ite c th el) env =
      if c.denote env then Tx.natToBool <$> Core.denote Γ th env
      else Tx.natToBool <$> Core.denote Γ el env :=
  map_denote_ite Tx.natToBool Γ c th el env

theorem map_denote_letPure_natToBool
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core .flag)
    (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.letPure p args k) env =
      Tx.natToBool <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  map_denote_letPure Tx.natToBool Γ p args k env

/-- Pair-of-Amount wrap through `letOp`. Core `RetTy` is `.pair .word .word`. -/
theorem map_denote_letOp_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ k (v :: env) :=
  map_denote_letOp
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ op k env

theorem map_denote_seq_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ k env :=
  map_denote_seq
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ s k env

theorem map_denote_ret_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (r : RetExpr (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.ret r) env =
      pure (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))
        (r.eval env)) :=
  map_denote_ret
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ r env

theorem map_denote_ite_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.ite c th el) env =
      if c.denote env then
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ th env
      else
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ el env :=
  map_denote_ite
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ c th el env

theorem map_denote_letPure_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom)
    (k : Core (.pair .word .word)) (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.letPure p args k) env =
      Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  map_denote_letPure
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ p args k env

end Lsc.Proof
