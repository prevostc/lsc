import Lsc.Lang.Core

/-!
Frame theorem for `Core.effects`. Extra hypotheses beyond the blueprint's `hΓ`:
mapping updates (`hMap1`/`hMap2`) and `ext.call` not mutating `self` (`hCall`).
Generated schemas satisfy the mapping facts via `StorageSchema.Lawful`.
-/

namespace Lsc

variable {S X E ε : Type}

/-- Successful `Op.denote` never mutates `self`. CALLs are discharged by `hCall`. -/
theorem Op.effects_frame {Γ : ContractSchema S X E ε} (op : Op) (env : List Nat)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E}
    (h : Tx.run (Op.denote Γ env op) ctx w = .ok (v, w')) :
    w'.self = w.self := by
  cases op with
  | call b m args =>
    exact hCall b m _ ctx w v w' h
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
  | mulDivDown _ _ _ | mulDivUp _ _ _ =>
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
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
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
  | call b m args =>
    simp [Stmt.denote] at h
    cases hRun : Tx.run (Γ.ext.call b m (args.map (·.eval env))) ctx w with
    | error _ => simp [hRun] at h
    | ok p =>
      rcases p with ⟨val, w1⟩
      simp [hRun] at h
      subst h
      exact congrArg P (hCall b m (args.map (·.eval env)) ctx w val w1 hRun)

/-- Scalar specialisation of `Stmt.effects_frame_on`. -/
theorem Stmt.effects_frame {Γ : ContractSchema S X E ε} (s : Stmt) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Stmt.effects_frame_on (Γ.st.scalar f) s env f
    (fun i σ v hne => hΓ f i σ v hne)
    (fun i σ m _ => hMap1 i σ m)
    (fun i σ m _ => hMap2 i σ m)
    hCall hf h

/-- If `f` is not among `c`'s writes, a successful `Core.denote` leaves projection `P` unchanged. -/
theorem effects_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
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
    exact congrArg P (Op.effects_frame op env hCall h)
  | opTailAddr op =>
    simp [Core.denote] at h
    exact congrArg P (Op.effects_frame op env hCall h)
  | opTailFlag op =>
    simp [Core.denote] at h
    exact congrArg P (Op.effects_frame op env hCall h)
  | stmtTail s =>
    simp [Core.denote] at h
    exact Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hCall hf h
  | revertTail err args =>
    simp [Core.denote] at h
  | letOp op k ih =>
    simp [Core.denote, Tx.run_bind] at h
    cases hOp : Tx.run (Op.denote Γ env op) ctx w with
    | error _ => simp [hOp] at h
    | ok p =>
      rcases p with ⟨a, w1⟩
      simp [hOp] at h
      have hself := Op.effects_frame op env hCall hOp
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
        Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hCall hfsk.1 hS
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
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  effects_frame_on c env f (Γ.st.scalar f)
    (fun i σ v hne => hΓ f i σ v hne)
    (fun i σ m _ => hMap1 i σ m)
    (fun i σ m _ => hMap2 i σ m)
    hCall hf h

/-- A successful run does not change mapping field `f` unless `f` is in `writes`. -/
theorem effects_frame_map1 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map1 f (Γ.st.scalarUpd i σ v) = Γ.st.map1 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map1Upd i σ m) = Γ.st.map1 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map2Upd i σ m) = Γ.st.map1 f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map1 f w'.self = Γ.st.map1 f w.self :=
  effects_frame_on c env f (Γ.st.map1 f) hΓ hMap1 hMap2 hCall hf h

/-- A successful run does not change a double mapping field `f` unless `f` is in `writes`. -/
theorem effects_frame_map2 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map2 f (Γ.st.scalarUpd i σ v) = Γ.st.map2 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map1Upd i σ m) = Γ.st.map2 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map2Upd i σ m) = Γ.st.map2 f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map2 f w'.self = Γ.st.map2 f w.self :=
  effects_frame_on c env f (Γ.st.map2 f) hΓ hMap1 hMap2 hCall hf h

end Lsc
