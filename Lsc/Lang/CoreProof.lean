import Lsc.Lang.Core

set_option linter.unusedSimpArgs false

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
  | load _ | loadMap _ _ | loadMap2 _ _ _ | value | timestamp | blockNumber | selfBalance | pure _ =>
    simp [Op.denote] at h
    rw [h.2]
  | send t amt =>
    rw [Op.denote] at h
    rw [Tx.run_sendAsNat (t.eval env) (amt.eval env)] at h
    split at h <;> cases h <;> rfl
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
    have hf' : f ∉ (Stmt.effects s).writes := by simpa [Core.effects] using hf
    exact Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hf' h
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
    have hf' : f ∉ (Core.effects k).writes := by simpa [Core.effects] using hf
    exact ih (Prim.eval p (args.map (·.eval env)) :: env) hf' h
  | ite c a b iha ihb =>
    simp [Core.denote, Tx.run_ite] at h
    have hfab : f ∉ (Core.effects a).writes ∧ f ∉ (Core.effects b).writes := by
      simpa [Core.effects, Effects.append, List.mem_append, not_or] using hf
    split at h
    · exact iha env hfab.1 h
    · exact ihb env hfab.2 h
  | @seqIf tBr _ c th el k ihth ihel ihk =>
    simp only [Core.denote, Tx.run_bind] at h
    have hfth :
        f ∉ (Core.effects th).writes ∧ f ∉ (Core.effects el).writes ∧
          f ∉ (Core.effects k).writes := by
      simpa [Core.effects, Effects.append, List.mem_append, not_or] using hf
    cases hIf : Tx.run
        (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) ctx w with
    | error _ => simp [hIf] at h
    | ok p =>
      rcases p with ⟨vBr, w1⟩
      simp [hIf] at h
      have hbr : P w1.self = P w.self := by
        split at hIf
        · exact ihth env hfth.1 hIf
        · exact ihel env hfth.2.1 hIf
      have hk : P w'.self = P w1.self := by
        cases tBr with
        | unit => exact ihk env hfth.2.2 h
        | word => exact ihk (vBr :: env) hfth.2.2 h
        | addr => exact ihk ((vBr : Nat) :: env) hfth.2.2 h
        | flag => exact ihk (vBr :: env) hfth.2.2 h
        | pair _ _ => exact ihk env hfth.2.2 h
      rw [hk, hbr]
  | callTail i args =>
    simp [Core.denote, Core.denoteDummy, Tx.run_revert] at h
  | letCall i args k _ih =>
    simp [Core.denote, Tx.run_bind, Core.denoteDummy, Tx.run_revert] at h

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

/-- `seqIf` is bind of the chosen branch into `seqIfCont`. -/
theorem denote_seqIf {t u : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core u)
    (env : List Nat) :
    Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Core.seqIfCont Γ v k env := by
  simp only [Core.denote]
  cases t <;> rfl

/-- Push `f <$>` through `seqIf`. -/
theorem map_denote_seqIf {t u : RetTy} {γ : Type} (f : u.denote → γ)
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core u)
    (env : List Nat) :
    f <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => f <$> Core.seqIfCont Γ v k env := by
  rw [denote_seqIf]
  exact Tx.map_bind f
    (if c.denote env then Core.denote Γ th env else Core.denote Γ el env)
    (fun v => Core.seqIfCont Γ v k env)

/-- Amount wrap through `seqIf`. -/
theorem map_denote_seqIf_ofWord {a : Asset} {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core .word)
    (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Amount.ofWord (a := a) <$> Core.seqIfCont Γ v k env :=
  map_denote_seqIf (Amount.ofWord (a := a)) Γ c th el k env

/-- Bool wrap through `seqIf`. -/
theorem map_denote_seqIf_natToBool {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core .flag)
    (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Tx.natToBool <$> Core.seqIfCont Γ v k env :=
  map_denote_seqIf Tx.natToBool Γ c th el k env

/-- Pair-of-Amount wrap through `seqIf`. -/
theorem map_denote_seqIf_ofWord_pair {a b : Asset} {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t)
    (k : Core (.pair .word .word)) (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v =>
          Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
            Core.seqIfCont Γ v k env :=
  map_denote_seqIf
    (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) Γ c th el k env

theorem atom_eval_rename (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) (a : Atom) :
    (a.rename ρ).eval env' = a.eval env := by
  cases a with
  | lit _ => rfl
  | var i => exact h i

theorem list_atom_eval_rename (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) (args : List Atom) :
    (args.map (·.rename ρ)).map (·.eval env') = args.map (·.eval env) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [atom_eval_rename ρ h, ih]

theorem cond_denote_rename (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) (c : Cond) :
    Cond.denote env' (c.rename ρ) ↔ c.denote env := by
  induction c with
  | lt a b | le a b | eq a b | ne a b =>
    simp [Cond.rename, Cond.denote, atom_eval_rename ρ h]
  | and c d ihc ihd | or c d ihc ihd =>
    simp [Cond.rename, Cond.denote, ihc, ihd]
  | not c ih => simp [Cond.rename, Cond.denote, ih]
  | tt | ff => simp [Cond.rename, Cond.denote]

theorem liftRename_eval (ρ : Nat → Atom) {env env' : List Nat} {v : Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) :
    ∀ i, (liftRename ρ i).eval (v :: env') = (v :: env).getD i 0
  | 0 => rfl
  | i + 1 => by
    dsimp [liftRename]
    cases hρ : ρ i with
    | var j =>
      have := h i
      simp [hρ, Atom.eval] at this ⊢
      simp [this]
    | lit n =>
      have := h i
      simp [hρ, Atom.eval] at this ⊢
      simp [this]

theorem denoteDummy_bind {Γ : ContractSchema S X E ε} {t u : RetTy}
    (k : t.denote → Tx S X E ε u.denote) :
    Core.denoteDummy (t := t) Γ >>= k = Core.denoteDummy (t := u) Γ := by
  funext ctx w
  simp [Core.denoteDummy, Tx.bind_apply, Tx.run_revert, Tx.revert]

theorem retExpr_eval_rename (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) {t} (r : RetExpr t) :
    (r.rename ρ).eval env' = r.eval env := by
  induction r with
  | unit => rfl
  | word a | addr a | flag a => exact atom_eval_rename ρ h a
  | pair x y ihx ihy =>
    simp [RetExpr.rename, RetExpr.eval, ihx, ihy]

theorem op_denote_rename {Γ : ContractSchema S X E ε} (ρ : Nat → Atom)
    {env env' : List Nat} (h : ∀ i, (ρ i).eval env' = env.getD i 0) (op : Op) :
    Op.denote Γ env' (op.rename ρ) = Op.denote Γ env op := by
  cases op <;> simp [Op.rename, Op.denote, atom_eval_rename ρ h,
    list_atom_eval_rename ρ h] <;> rfl

theorem stmt_denote_rename {Γ : ContractSchema S X E ε} (ρ : Nat → Atom)
    {env env' : List Nat} (h : ∀ i, (ρ i).eval env' = env.getD i 0) (s : Stmt) :
    Stmt.denote Γ env' (s.rename ρ) = Stmt.denote Γ env s := by
  cases s with
  | store f v =>
    simp [Stmt.rename, Stmt.denote, atom_eval_rename ρ h]
  | storeMap f k v =>
    simp [Stmt.rename, Stmt.denote, atom_eval_rename ρ h]
  | storeMap2 f k₁ k₂ v =>
    simp [Stmt.rename, Stmt.denote, atom_eval_rename ρ h]
  | require c err args =>
    simp [Stmt.rename, Stmt.denote, list_atom_eval_rename ρ h]
    exact Tx.require_iff _ (cond_denote_rename ρ h c)
  | emit ev args | revert err args =>
    simp [Stmt.rename, Stmt.denote, list_atom_eval_rename ρ h]
  | call t sel args ret =>
    simp [Stmt.rename, Stmt.denote]
    have hcall := op_denote_rename (Γ := Γ) ρ h (.call t sel args ret)
    simpa [Op.rename] using congrArg (fun x => (fun _ => ()) <$> x) hcall
  | view t sel args ret =>
    simp [Stmt.rename, Stmt.denote]
    have hview := op_denote_rename (Γ := Γ) ρ h (.view t sel args ret)
    simpa [Op.rename] using congrArg (fun x => (fun _ => ()) <$> x) hview

theorem denote_rename {Γ : ContractSchema S X E ε} {t : RetTy}
    (k : Core t) (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) :
    Core.denote Γ (k.rename ρ) env' = Core.denote Γ k env := by
  induction k generalizing env env' ρ with
  | ret r => simp [Core.rename, Core.denote, retExpr_eval_rename ρ h]
  | opTail op =>
    simp [Core.rename, Core.denote, op_denote_rename ρ h]
  | opTailAddr op | opTailFlag op =>
    simp [Core.rename, Core.denote, op_denote_rename ρ h]
    try rfl
  | stmtTail s => simp [Core.rename, Core.denote, stmt_denote_rename ρ h]
  | revertTail err args =>
    simp [Core.rename, Core.denote, list_atom_eval_rename ρ h]
  | letOp op k ih =>
    simp [Core.rename, Core.denote, op_denote_rename ρ h]
    refine congrArg (fun f => Op.denote Γ env op >>= f) ?_
    funext v
    exact ih (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
  | seq s k ih =>
    simp [Core.rename, Core.denote, stmt_denote_rename ρ h]
    exact congrArg (fun t => Stmt.denote Γ env s >>= fun _ => t) (ih (ρ := ρ) h)
  | letPure p args k ih =>
    simp [Core.rename, Core.denote, list_atom_eval_rename ρ h]
    exact ih (ρ := liftRename ρ) (liftRename_eval ρ h)
  | ite c a b iha ihb =>
    have hc := cond_denote_rename ρ h c
    simp only [Core.rename, Core.denote]
    by_cases hcond : c.denote env
    · have hc' : Cond.denote env' (c.rename ρ) := hc.mpr hcond
      simp [hc', hcond]
      exact iha (ρ := ρ) h
    · have hc' : ¬ Cond.denote env' (c.rename ρ) := fun h' => hcond (hc.mp h')
      simp [hc', hcond]
      exact ihb (ρ := ρ) h
  | @seqIf tBr _ c th el k ihth ihel ihk =>
    have hc := cond_denote_rename ρ h c
    simp only [Core.rename, Core.denote]
    rw [ihth (ρ := ρ) h, ihel (ρ := ρ) h]
    have hif :
        (if Cond.denote env' (c.rename ρ) then Core.denote Γ th env
          else Core.denote Γ el env) =
        (if c.denote env then Core.denote Γ th env
          else Core.denote Γ el env) := by
      simp [hc]
    rw [hif]
    refine congrArg
      (fun f =>
        (if c.denote env then Core.denote Γ th env
          else Core.denote Γ el env) >>= f)
      ?_
    funext v
    cases tBr with
    | unit =>
      simp [seqIfRename]
      exact ihk (ρ := ρ) h
    | pair _ _ =>
      simp [seqIfRename]
      exact ihk (ρ := ρ) h
    | word =>
      simp [seqIfRename]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
    | addr =>
      simp [seqIfRename]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := (v : Nat)) ρ h)
    | flag =>
      simp [seqIfRename]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
  | callTail i args =>
    simp [Core.rename, Core.denote]
  | letCall i args k _ih =>
    simp [Core.rename, Core.denote, denoteDummy_bind]

/-- Slice-1 `denote` treats an internal call as `denoteDummy`. -/
theorem denote_callTail {Γ : ContractSchema S X E ε} {t : RetTy}
    (i : Nat) (args : List Atom) (env : List Nat) :
    Core.denote Γ (.callTail (t := t) i args) env = Core.denoteDummy Γ :=
  rfl

/-- `letCall` is dummy-call bound into `k`. -/
theorem denote_letCall {Γ : ContractSchema S X E ε} {t u : RetTy}
    (i : Nat) (args : List Atom) (k : Core u) (env : List Nat) :
    Core.denote Γ (.letCall (t := t) i args k) env =
      Core.denoteDummy (t := t) Γ >>= fun v =>
        Core.denote Γ k (RetTy.flatten v ++ env) :=
  rfl

/-- `seqUnit` is bind of a unit core into `k`. -/
theorem denote_seqUnit {u : RetTy} (Γ : ContractSchema S X E ε)
    (a : Core .unit) (k : Core u) (env : List Nat) :
    Core.denote Γ (a.seqUnit k) env =
      Core.denote Γ a env >>= fun _ => Core.denote Γ k env := by
  cases a with
  | ret r =>
    cases r
    simp [Core.seqUnit, Core.denote, Tx.pure_bind]
  | stmtTail s =>
    simp [Core.seqUnit, Core.denote]
  | revertTail e args =>
    simp [Core.seqUnit, Core.denote]
    funext ctx w
    simp [Tx.bind_apply, Tx.run_revert, Tx.revert]
  | letOp op k' =>
    simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
    refine congrArg (fun f => Op.denote Γ env op >>= f) ?_
    funext v
    have hρ : ∀ i, Atom.eval (v :: env) (.var (i + 1)) = env.getD i 0 :=
      fun _ => rfl
    rw [denote_seqUnit (Γ := Γ) k' (k.rename fun i => .var (i + 1)) (v :: env),
      denote_rename (ρ := fun i => .var (i + 1)) (h := hρ)]
  | seq s k' =>
    simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
    exact congrArg (fun t => Stmt.denote Γ env s >>= fun _ => t)
      (denote_seqUnit (Γ := Γ) k' k env)
  | letPure p args k' =>
    simp [Core.seqUnit, Core.denote]
    have hρ : ∀ i,
        Atom.eval (Prim.eval p (args.map (·.eval env)) :: env) (.var (i + 1)) =
          env.getD i 0 := fun _ => rfl
    rw [denote_seqUnit (Γ := Γ) k' (k.rename fun i => .var (i + 1)) _,
      denote_rename (ρ := fun i => .var (i + 1)) (h := hρ)]
  | ite c th el =>
    simp [Core.seqUnit, Core.denote, Tx.bind_ite]
    rw [denote_seqUnit (Γ := Γ) th k env, denote_seqUnit (Γ := Γ) el k env]
  | @seqIf tBr _ c th el k' =>
    cases tBr with
    | unit =>
      simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
      refine congrArg
        (fun f =>
          (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>= f)
        ?_
      funext _
      exact denote_seqUnit (Γ := Γ) k' k env
    | pair _ _ =>
      simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
      refine congrArg
        (fun f =>
          (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>= f)
        ?_
      funext _
      exact denote_seqUnit (Γ := Γ) k' k env
    | word =>
      simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
      refine congrArg
        (fun f =>
          (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>= f)
        ?_
      funext v
      have hρ : ∀ i, Atom.eval (v :: env) (.var (i + 1)) = env.getD i 0 :=
        fun _ => rfl
      rw [denote_seqUnit (Γ := Γ) k' (k.rename fun i => .var (i + 1)) (v :: env),
        denote_rename (ρ := fun i => .var (i + 1)) (h := hρ)]
    | addr =>
      simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
      refine congrArg
        (fun f =>
          (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>= f)
        ?_
      funext v
      have hρ : ∀ i, Atom.eval ((v : Nat) :: env) (.var (i + 1)) = env.getD i 0 :=
        fun _ => rfl
      rw [denote_seqUnit (Γ := Γ) k' (k.rename fun i => .var (i + 1)) ((v : Nat) :: env),
        denote_rename (ρ := fun i => .var (i + 1)) (h := hρ)]
    | flag =>
      simp [Core.seqUnit, Core.denote, Tx.bind_assoc]
      refine congrArg
        (fun f =>
          (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>= f)
        ?_
      funext v
      have hρ : ∀ i, Atom.eval (v :: env) (.var (i + 1)) = env.getD i 0 :=
        fun _ => rfl
      rw [denote_seqUnit (Γ := Γ) k' (k.rename fun i => .var (i + 1)) (v :: env),
        denote_rename (ρ := fun i => .var (i + 1)) (h := hρ)]
  | letCall i args k' =>
    funext ctx w
    simp [Core.seqUnit, Core.denote, Tx.bind_apply, Tx.bind_assoc,
      Core.denoteDummy, Tx.run_revert]
  | callTail i args =>
    funext ctx w
    simp [Core.seqUnit, Core.denote, Tx.bind_apply, Core.denoteDummy, Tx.run_revert]
termination_by a
decreasing_by all_goals decreasing_tactic

/-- `seqIf` of unit branches is `ite` with `k` copied into both sides. -/
theorem seqIf_eq_ite {u : RetTy} (Γ : ContractSchema S X E ε)
    (c : Cond) (th el : Core .unit) (k : Core u) (env : List Nat) :
    Core.denote Γ (.seqIf c th el k) env =
      Core.denote Γ (.ite c (th.seqUnit k) (el.seqUnit k)) env := by
  rw [denote_seqIf, Core.denote]
  simp [Core.seqIfCont, denote_seqUnit, Tx.bind_ite]

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

theorem RetExpr.flatten_eval {t : RetTy} (r : RetExpr t) (env : List Nat) :
    RetTy.flatten (r.eval env) = ((RetExpr.atoms r).map (·.eval env)).reverse := by
  induction r with
  | unit => rfl
  | word a | addr a | flag a =>
    simp [RetTy.flatten, RetExpr.eval, RetExpr.atoms]
  | pair x y ihx ihy =>
    simp [RetTy.flatten, RetExpr.eval, RetExpr.atoms, List.map_append,
      List.reverse_append, ihx, ihy]

theorem getD_append_right {α} (l₁ l₂ : List α) (i : Nat) (x : α)
    (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i x = l₂.getD (i - l₁.length) x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_append_left {α} (l₁ l₂ : List α) (i : Nat) (x : α)
    (h : i < l₁.length) :
    (l₁ ++ l₂).getD i x = l₁.getD i x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, h]

theorem getD_reverse {α} (l : List α) (i : Nat) (x : α)
    (h : i < l.length) :
    l.reverse.getD i x = l.getD (l.length - 1 - i) x := by
  have h' : l.length - 1 - i < l.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_reverse h,
    List.getElem?_eq_getElem h, List.getElem?_eq_getElem h']

theorem getD_map_atom_eval (as : List Atom) (env : List Nat) (i : Nat) :
    (as.map (·.eval env)).getD i 0 = (as.getD i (.lit 0)).eval env := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases as[i]? <;> simp [Atom.eval]

theorem substFlatten_eval {t : RetTy} (r : RetExpr t) (d : Nat)
    (vs orig : List Nat) (hd : vs.length = d) (i : Nat) :
    (substFlatten r d i).eval (vs ++ orig) =
      (RetTy.flatten (r.eval (vs ++ orig)) ++ orig).getD i 0 := by
  have hn : (RetExpr.atoms r).length = t.wordCount := RetExpr.atoms_length r
  have hf : (RetTy.flatten (r.eval (vs ++ orig))).length = t.wordCount :=
    RetTy.flatten_length _
  simp only [substFlatten]
  by_cases hlt : i < t.wordCount
  · rw [if_pos hlt]
    rw [← getD_map_atom_eval, RetExpr.flatten_eval]
    have hiL : i < ((RetExpr.atoms r).map (·.eval (vs ++ orig))).reverse.length := by
      simp [List.length_map, hn]; omega
    rw [getD_append_left _ orig i 0 (by simpa using hiL)]
    rw [getD_reverse _ i 0 (by simpa using hiL)]
    simp [List.length_map, hn]
  · rw [if_neg hlt]
    have hge : t.wordCount ≤ i := Nat.le_of_not_gt hlt
    simp only [Atom.eval]
    have : i - t.wordCount + d = vs.length + (i - t.wordCount) := by omega
    rw [this, getD_append_right vs orig _ 0 (by omega)]
    rw [getD_append_right (RetTy.flatten (r.eval (vs ++ orig))) orig i 0
      (by omega)]
    simp [hf]

theorem denote_splice {Γ : ContractSchema S X E ε} {t u : RetTy}
    (d : Nat) (body : Core t) (k : Core u) (vs orig : List Nat)
    (hd : vs.length = d) :
    Core.denote Γ (Core.splice d body k) (vs ++ orig) =
      Core.denote Γ body (vs ++ orig) >>= fun v =>
        Core.denote Γ k (RetTy.flatten v ++ orig) := by
  induction body generalizing d vs with
  | ret r =>
    simp [Core.splice, Core.denote, Tx.pure_bind]
    exact denote_rename k (ρ := substFlatten r d)
      (substFlatten_eval r d vs orig hd)
  | opTail op =>
    simp [Core.splice, Core.denote]
    refine congrArg (fun f => Op.denote Γ (vs ++ orig) op >>= f) ?_
    funext v
    have hd' : (v :: vs).length = d + 1 := by simp [hd]
    have henv : v :: (vs ++ orig) = (v :: vs) ++ orig := rfl
    rw [henv, denote_rename (Γ := Γ) k
      (ρ := substFlatten (RetExpr.word (.var 0)) (d + 1))
      (substFlatten_eval (RetExpr.word (.var 0)) (d + 1) (v :: vs) orig hd')]
    simp [RetTy.flatten, RetExpr.eval, Atom.eval]
  | opTailAddr op =>
    simp [Core.splice, Core.denote]
    refine congrArg (fun f => Op.denote Γ (vs ++ orig) op >>= f) ?_
    funext v
    have hd' : (v :: vs).length = d + 1 := by simp [hd]
    have henv : v :: (vs ++ orig) = (v :: vs) ++ orig := rfl
    rw [henv, denote_rename (Γ := Γ) k
      (ρ := substFlatten (RetExpr.addr (.var 0)) (d + 1))
      (substFlatten_eval (RetExpr.addr (.var 0)) (d + 1) (v :: vs) orig hd')]
    simp [RetTy.flatten, RetExpr.eval, Atom.eval]
  | opTailFlag op =>
    simp [Core.splice, Core.denote]
    refine congrArg (fun f => Op.denote Γ (vs ++ orig) op >>= f) ?_
    funext v
    have hd' : (v :: vs).length = d + 1 := by simp [hd]
    have henv : v :: (vs ++ orig) = (v :: vs) ++ orig := rfl
    rw [henv, denote_rename (Γ := Γ) k
      (ρ := substFlatten (RetExpr.flag (.var 0)) (d + 1))
      (substFlatten_eval (RetExpr.flag (.var 0)) (d + 1) (v :: vs) orig hd')]
    simp [RetTy.flatten, RetExpr.eval, Atom.eval]
  | stmtTail s =>
    simp [Core.splice, Core.denote]
    rw [denote_rename (Γ := Γ) k (ρ := substFlatten RetExpr.unit d)
      (substFlatten_eval RetExpr.unit d vs orig hd)]
    try simp [RetTy.flatten]
  | revertTail e args =>
    simp [Core.splice, Core.denote]
    funext ctx w
    simp [Tx.bind_apply, Tx.run_revert, Tx.revert]
  | letOp op k' ih =>
    simp [Core.splice, Core.denote, Tx.bind_assoc]
    refine congrArg (fun f => Op.denote Γ (vs ++ orig) op >>= f) ?_
    funext v
    exact ih (d + 1) (v :: vs) (by simp [hd])
  | seq s k' ih =>
    simp [Core.splice, Core.denote, Tx.bind_assoc]
    exact congrArg (fun t => Stmt.denote Γ (vs ++ orig) s >>= fun _ => t)
      (ih d vs hd)
  | letPure p args k' ih =>
    simp [Core.splice, Core.denote]
    exact ih (d + 1) (Prim.eval p (args.map (·.eval (vs ++ orig))) :: vs)
      (by simp [hd])
  | ite c a b iha ihb =>
    simp [Core.splice, Core.denote]
    by_cases hc : Cond.denote (vs ++ orig) c
    · simp [hc]; exact iha d vs hd
    · simp [hc]; exact ihb d vs hd
  | @seqIf tBr _ c th el k' _ _ ihk =>
    simp [Core.splice, Core.denote, Tx.bind_assoc]
    refine congrArg
      (fun f =>
        (if Cond.denote (vs ++ orig) c then Core.denote Γ th (vs ++ orig)
          else Core.denote Γ el (vs ++ orig)) >>= f) ?_
    funext v
    cases tBr with
    | unit =>
      simpa [RetTy.flatten] using ihk d vs hd
    | pair _ _ =>
      simpa [RetTy.flatten] using ihk d vs hd
    | word =>
      exact ihk (d + 1) (v :: vs) (by simp [hd])
    | addr =>
      exact ihk (d + 1) (Address.toWord v :: vs) (by simp [hd])
    | flag =>
      exact ihk (d + 1) (v :: vs) (by simp [hd])
  | letCall i args k' _ =>
    simp [Core.splice, Core.denote]
    exact denoteDummy_bind _
  | callTail i args =>
    simp [Core.splice, Core.denote]
    exact denoteDummy_bind _

theorem denote_splice0 {Γ : ContractSchema S X E ε} {t u : RetTy}
    (body : Core t) (k : Core u) (env : List Nat) :
    Core.denote Γ (Core.splice 0 body k) env =
      Core.denote Γ body env >>= fun v =>
        Core.denote Γ k (RetTy.flatten v ++ env) := by
  simpa using denote_splice (Γ := Γ) 0 body k [] env rfl

theorem liftRenameN_eval (n : Nat) (ρ : Nat → Atom)
    {env env' : List Nat} (vs : List Nat) (hvs : vs.length = n)
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) :
    ∀ i, (liftRenameN n ρ i).eval (vs ++ env') = (vs ++ env).getD i 0 := by
  intro i
  simp only [liftRenameN]
  by_cases hi : i < n
  · rw [if_pos hi]
    simp only [Atom.eval]
    have : i < vs.length := by omega
    rw [getD_append_left vs env' i 0 (by omega), getD_append_left vs env i 0 (by omega)]
  · have hge : n ≤ i := Nat.le_of_not_gt hi
    rw [if_neg hi]
    have hρ := h (i - n)
    cases hρi : ρ (i - n) with
    | var j =>
      simp only [hρi, Atom.eval] at hρ ⊢
      have : j + n = vs.length + j := by omega
      rw [this, getD_append_right vs env' _ 0 (by omega)]
      rw [getD_append_right vs env i 0 (by omega)]
      simpa [hvs]
    | lit m =>
      simp only [hρi, Atom.eval] at hρ ⊢
      rw [getD_append_right vs env i 0 (by omega)]
      simpa [hvs]

theorem denoteTbl_ret {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (r : RetExpr t) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.ret r) env tbl = pure (r.eval env) := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_opTail {Γ : ContractSchema S X E ε} (fuel : Nat)
    (op : Op) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.opTail op) env tbl = Op.denote Γ env op := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_opTailAddr {Γ : ContractSchema S X E ε} (fuel : Nat)
    (op : Op) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.opTailAddr op) env tbl = Op.denote Γ env op := by
  cases fuel <;> (simp [Core.denoteTbl]; rfl)

theorem denoteTbl_opTailFlag {Γ : ContractSchema S X E ε} (fuel : Nat)
    (op : Op) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.opTailFlag op) env tbl = Op.denote Γ env op := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_stmtTail {Γ : ContractSchema S X E ε} (fuel : Nat)
    (s : Stmt) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.stmtTail s) env tbl = Stmt.denote Γ env s := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_revertTail {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (err : Nat) (args : List Atom) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.revertTail (t := t) err args) env tbl =
      Tx.revert (Γ.err.build err (args.map (·.eval env))) := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_letOp {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (op : Op) (k : Core t) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.letOp op k) env tbl =
      Op.denote Γ env op >>= fun v => Core.denoteTbl Γ fuel k (v :: env) tbl := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_seq {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (s : Stmt) (k : Core t) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.seq s k) env tbl =
      Stmt.denote Γ env s >>= fun _ => Core.denoteTbl Γ fuel k env tbl := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_letPure {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (p : Prim) (args : List Atom) (k : Core t) (env : List Nat)
    (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.letPure p args k) env tbl =
      Core.denoteTbl Γ fuel k (Prim.eval p (args.map (·.eval env)) :: env) tbl := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_ite {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t} (c : Cond) (a b : Core t) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.ite c a b) env tbl =
      if c.denote env then Core.denoteTbl Γ fuel a env tbl
      else Core.denoteTbl Γ fuel b env tbl := by
  cases fuel <;> simp [Core.denoteTbl]

theorem denoteTbl_seqIf {Γ : ContractSchema S X E ε} (fuel : Nat)
    {t u} (c : Cond) (th el : Core t) (k : Core u) (env : List Nat)
    (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (.seqIf c th el k) env tbl =
      (if c.denote env then Core.denoteTbl Γ fuel th env tbl
        else Core.denoteTbl Γ fuel el env tbl) >>=
        fun v => Core.seqIfContTbl Γ fuel v k env tbl := by
  simp [Core.denoteTbl]

theorem denoteTbl_rename {Γ : ContractSchema S X E ε} {t : RetTy}
    (fuel : Nat) (k : Core t) (ρ : Nat → Atom) {env env' : List Nat}
    (h : ∀ i, (ρ i).eval env' = env.getD i 0) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel (k.rename ρ) env' tbl =
      Core.denoteTbl Γ fuel k env tbl := by
  induction k generalizing env env' ρ with
  | ret r =>
    simp [Core.rename, denoteTbl_ret, retExpr_eval_rename ρ h]
  | opTail op =>
    simp [Core.rename, denoteTbl_opTail, op_denote_rename ρ h]
  | opTailAddr op =>
    simp [Core.rename, denoteTbl_opTailAddr, op_denote_rename ρ h]; rfl
  | opTailFlag op =>
    simp [Core.rename, denoteTbl_opTailFlag, op_denote_rename ρ h]
  | stmtTail s =>
    simp [Core.rename, denoteTbl_stmtTail, stmt_denote_rename ρ h]
  | revertTail err args =>
    simp [Core.rename, denoteTbl_revertTail, list_atom_eval_rename ρ h]
  | letOp op k ih =>
    simp [Core.rename, denoteTbl_letOp, op_denote_rename ρ h]
    refine congrArg (fun f => Op.denote Γ env op >>= f) ?_
    funext v
    exact ih (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
  | seq s k ih =>
    simp [Core.rename, denoteTbl_seq, stmt_denote_rename ρ h]
    exact congrArg (fun t => Stmt.denote Γ env s >>= fun _ => t) (ih (ρ := ρ) h)
  | letPure p args k ih =>
    simp [Core.rename, denoteTbl_letPure, list_atom_eval_rename ρ h]
    exact ih (ρ := liftRename ρ) (liftRename_eval ρ h)
  | ite c a b iha ihb =>
    have hc := cond_denote_rename ρ h c
    simp only [Core.rename, denoteTbl_ite]
    by_cases hcond : c.denote env
    · have hc' : Cond.denote env' (c.rename ρ) := hc.mpr hcond
      simp [hc', hcond]
      exact iha (ρ := ρ) h
    · have hc' : ¬ Cond.denote env' (c.rename ρ) := fun h' => hcond (hc.mp h')
      simp [hc', hcond]
      exact ihb (ρ := ρ) h
  | @seqIf tBr _ c th el k ihth ihel ihk =>
    have hc := cond_denote_rename ρ h c
    simp only [Core.rename, denoteTbl_seqIf]
    rw [ihth (ρ := ρ) h, ihel (ρ := ρ) h]
    have hif :
        (if Cond.denote env' (c.rename ρ) then Core.denoteTbl Γ fuel th env tbl
          else Core.denoteTbl Γ fuel el env tbl) =
        (if c.denote env then Core.denoteTbl Γ fuel th env tbl
          else Core.denoteTbl Γ fuel el env tbl) := by
      simp [hc]
    rw [hif]
    refine congrArg
      (fun f =>
        (if c.denote env then Core.denoteTbl Γ fuel th env tbl
          else Core.denoteTbl Γ fuel el env tbl) >>= f)
      ?_
    funext v
    cases tBr with
    | unit =>
      simp [seqIfRename, Core.seqIfContTbl]
      exact ihk (ρ := ρ) h
    | pair _ _ =>
      simp [seqIfRename, Core.seqIfContTbl]
      exact ihk (ρ := ρ) h
    | word =>
      simp [seqIfRename, Core.seqIfContTbl]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
    | addr =>
      simp [seqIfRename, Core.seqIfContTbl]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := Address.toWord v) ρ h)
    | flag =>
      simp [seqIfRename, Core.seqIfContTbl]
      exact ihk (ρ := liftRename ρ) (liftRename_eval (v := v) ρ h)
  | callTail i args =>
    cases fuel with
    | zero => simp [Core.rename, Core.denoteTbl]
    | succ n =>
      simp [Core.rename, Core.denoteTbl, list_atom_eval_rename ρ h]
  | letCall i args k ih =>
    cases fuel with
    | zero => simp [Core.rename, Core.denoteTbl, denoteDummy_bind]
    | succ n =>
      simp [Core.rename, Core.denoteTbl, list_atom_eval_rename ρ h]
      refine congrArg
        (fun f =>
          (if hi : i < tbl.length then
            let d := tbl[i]
            if hret : d.ret = _ then
              Core.denoteTbl Γ n (hret ▸ d.body) (args.map (·.eval env)) (tbl.take i)
            else Core.denoteDummy Γ
          else Core.denoteDummy Γ) >>= f) ?_
      funext v
      exact ih (ρ := liftRenameN _ ρ)
        (liftRenameN_eval _ ρ (RetTy.flatten v)
          (RetTy.flatten_length v) h)

theorem denoteTbl_eq_denote_expandGo {Γ : ContractSchema S X E ε} {t : RetTy}
    (fuel : Nat) (c : Core t) (env : List Nat) (tbl : List InternalDef) :
    Core.denoteTbl Γ fuel c env tbl =
      Core.denote Γ (Core.expandGo fuel c tbl) env := by
  induction fuel generalizing t c env tbl with
  | zero =>
    induction c generalizing env with
    | ret r => simp [Core.expandGo, denoteTbl_ret, Core.denote]
    | opTail op => simp [Core.expandGo, denoteTbl_opTail, Core.denote]
    | opTailAddr op => simp [Core.expandGo, denoteTbl_opTailAddr, Core.denote]; rfl
    | opTailFlag op => simp [Core.expandGo, denoteTbl_opTailFlag, Core.denote]
    | stmtTail s => simp [Core.expandGo, denoteTbl_stmtTail, Core.denote]
    | revertTail err args =>
      simp [Core.expandGo, denoteTbl_revertTail, Core.denote]
    | letOp op k ih =>
      simp [Core.expandGo, denoteTbl_letOp, Core.denote]
      refine congrArg (fun f => Op.denote Γ env op >>= f) ?_
      funext v; exact ih (v :: env)
    | seq s k ih =>
      simp [Core.expandGo, denoteTbl_seq, Core.denote]
      exact congrArg (fun t => Stmt.denote Γ env s >>= fun _ => t) (ih env)
    | letPure p args k ih =>
      simp [Core.expandGo, denoteTbl_letPure, Core.denote]
      exact ih _
    | ite c a b iha ihb =>
      simp [Core.expandGo, denoteTbl_ite, Core.denote]
      by_cases hc : Cond.denote env c
      · simp [hc]; exact iha env
      · simp [hc]; exact ihb env
    | @seqIf tBr _ c th el k ihth ihel ihk =>
      simp [Core.expandGo, denoteTbl_seqIf, Core.denote]
      rw [ihth env, ihel env]
      refine congrArg
        (fun f =>
          (if Cond.denote env c then Core.denote Γ (Core.expandGo 0 th tbl) env
            else Core.denote Γ (Core.expandGo 0 el tbl) env) >>= f) ?_
      funext v
      cases tBr with
      | unit | pair _ _ =>
        simp [Core.seqIfContTbl]; exact ihk env
      | word | addr | flag =>
        simp [Core.seqIfContTbl]; exact ihk _
    | letCall i args k ih =>
      simp [Core.expandGo, Core.denoteTbl, Core.denote, denoteDummy_bind]
    | callTail i args =>
      simp [Core.expandGo, Core.denoteTbl, Core.denote]
  | succ n ihf =>
    induction c generalizing env with
    | ret r => simp [Core.expandGo, denoteTbl_ret, Core.denote]
    | opTail op => simp [Core.expandGo, denoteTbl_opTail, Core.denote]
    | opTailAddr op => simp [Core.expandGo, denoteTbl_opTailAddr, Core.denote]; rfl
    | opTailFlag op => simp [Core.expandGo, denoteTbl_opTailFlag, Core.denote]
    | stmtTail s => simp [Core.expandGo, denoteTbl_stmtTail, Core.denote]
    | revertTail err args =>
      simp [Core.expandGo, denoteTbl_revertTail, Core.denote]
    | letOp op k ih =>
      simp [Core.expandGo, denoteTbl_letOp, Core.denote]
      refine congrArg (fun f => Op.denote Γ env op >>= f) ?_
      funext v; exact ih (v :: env)
    | seq s k ih =>
      simp [Core.expandGo, denoteTbl_seq, Core.denote]
      exact congrArg (fun t => Stmt.denote Γ env s >>= fun _ => t) (ih env)
    | letPure p args k ih =>
      simp [Core.expandGo, denoteTbl_letPure, Core.denote]
      exact ih _
    | ite c a b iha ihb =>
      simp [Core.expandGo, denoteTbl_ite, Core.denote]
      by_cases hc : Cond.denote env c
      · simp [hc]; exact iha env
      · simp [hc]; exact ihb env
    | @seqIf tBr _ c th el k ihth ihel ihk =>
      simp [Core.expandGo, denoteTbl_seqIf, Core.denote]
      rw [ihth env, ihel env]
      refine congrArg
        (fun f =>
          (if Cond.denote env c then
            Core.denote Γ (Core.expandGo (n + 1) th tbl) env
          else Core.denote Γ (Core.expandGo (n + 1) el tbl) env) >>= f) ?_
      funext v
      cases tBr with
      | unit | pair _ _ =>
        simp [Core.seqIfContTbl]; exact ihk env
      | word | addr | flag =>
        simp [Core.seqIfContTbl]; exact ihk _
    | @callTail tRet i args =>
      simp [Core.expandGo, Core.denoteTbl]
      by_cases hi : i < tbl.length
      · simp [hi]
        by_cases hret : tbl[i].ret = tRet
        · rw [dif_pos hret, dif_pos hret]
          have hρ : ∀ j, (substArgs args j).eval env =
              (args.map (·.eval env)).getD j 0 := substArgs_eval args env
          trans Core.denoteTbl Γ n
              ((hret ▸ tbl[i].body).rename (substArgs args)) env (tbl.take i)
          · exact (denoteTbl_rename (Γ := Γ) n (hret ▸ tbl[i].body)
              (substArgs args) hρ (tbl.take i)).symm
          · exact ihf _ env (tbl.take i)
        · rw [dif_neg hret, dif_neg hret]
          simp [Core.denote]
      · simp [hi, Core.denote]
    | @letCall tArg _u i args k ih =>
      simp [Core.expandGo, Core.denoteTbl]
      by_cases hi : i < tbl.length
      · simp [hi]
        by_cases hret : tbl[i].ret = tArg
        · rw [dif_pos hret, dif_pos hret]
          have hρ : ∀ j, (substArgs args j).eval env =
              (args.map (·.eval env)).getD j 0 := substArgs_eval args env
          rw [denote_splice0]
          have hbody :
              Core.denoteTbl Γ n (hret ▸ tbl[i].body)
                (args.map (·.eval env)) (tbl.take i) =
              Core.denote Γ
                (Core.expandGo n
                  ((hret ▸ tbl[i].body).rename (substArgs args))
                  (tbl.take i)) env := by
            trans Core.denoteTbl Γ n
                ((hret ▸ tbl[i].body).rename (substArgs args))
                env (tbl.take i)
            · exact (denoteTbl_rename (Γ := Γ) n (hret ▸ tbl[i].body)
                (substArgs args) hρ (tbl.take i)).symm
            · exact ihf _ env (tbl.take i)
          rw [hbody]
          refine congrArg
            (fun f =>
              Core.denote Γ
                (Core.expandGo n
                  ((hret ▸ tbl[i].body).rename (substArgs args))
                  (tbl.take i)) env >>= f) ?_
          funext v
          exact ih _
        · rw [dif_neg hret, dif_neg hret]
          simp [Core.denote, denoteDummy_bind]
      · simp [hi, Core.denote, denoteDummy_bind]

theorem denoteTbl_eq_denote_expand {Γ : ContractSchema S X E ε} {t : RetTy}
    (tbl : List InternalDef) (c : Core t) (env : List Nat) :
    Core.denoteTbl Γ tbl.length c env tbl =
      Core.denote Γ (Core.expand tbl c) env :=
  denoteTbl_eq_denote_expandGo tbl.length c env tbl

theorem expandGo_eq_self {t : RetTy} (fuel : Nat) (c : Core t)
    (tbl : List InternalDef) (h : Core.hasInternalCall c = false) :
    Core.expandGo fuel c tbl = c := by
  induction c generalizing fuel with
  | ret r => simp [Core.expandGo]
  | opTail op | opTailAddr op | opTailFlag op => simp [Core.expandGo]
  | stmtTail s => simp [Core.expandGo]
  | revertTail err args => simp [Core.expandGo]
  | letOp op k ih =>
    simp [Core.hasInternalCall] at h
    simp [Core.expandGo, ih fuel h]
  | seq s k ih =>
    simp [Core.hasInternalCall] at h
    simp [Core.expandGo, ih fuel h]
  | letPure p args k ih =>
    simp [Core.hasInternalCall] at h
    simp [Core.expandGo, ih fuel h]
  | ite c a b iha ihb =>
    simp [Core.hasInternalCall, Bool.or_eq_false_iff] at h
    simp [Core.expandGo, iha fuel h.1, ihb fuel h.2]
  | seqIf c th el k ihth ihel ihk =>
    simp [Core.hasInternalCall, Bool.or_eq_false_iff] at h
    simp [Core.expandGo, ihth fuel h.1.1, ihel fuel h.1.2, ihk fuel h.2]
  | letCall i args k =>
    simp [Core.hasInternalCall] at h
  | callTail i args =>
    simp [Core.hasInternalCall] at h

theorem expand_eq_self {t : RetTy} (tbl : List InternalDef) (c : Core t)
    (h : Core.hasInternalCall c = false) :
    Core.expand tbl c = c :=
  expandGo_eq_self tbl.length c tbl h

end Lsc.Proof
