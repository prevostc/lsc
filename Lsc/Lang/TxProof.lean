import Lsc.Lang.Tx
import Lsc.Lang.Interface

/-!
Proofs of the `Tx.run` peeling lemmas, monad laws, and `Lang.worldAfter`
lemmas. Statements live in `TxTheorems.lean`.
-/

namespace Lsc.Tx.Proof

variable {S X E ε : Type} {α K K₁ K₂ V : Type}

theorem run_pure (a : α) (ctx : Ctx) (w : World S X E) :
    run (pure a : Tx S X E ε α) ctx w = .ok (a, w) :=
  rfl

theorem readerRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    ReaderT.run x ctx w = run x ctx w :=
  rfl

theorem stateRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    StateT.run (ReaderT.run x ctx) w = run x ctx w :=
  rfl

theorem run_bind {β : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β) (ctx : Ctx)
    (w : World S X E) :
    run (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e := by
  simp only [run, bind, ReaderT.bind, StateT.bind]
  cases x ctx w <;> rfl

theorem bind_apply {β : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β)
    (ctx : Ctx) (w : World S X E) :
    (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e :=
  run_bind x f ctx w

theorem run_load (proj : S → α) (ctx : Ctx) (w : World S X E) :
    run (load (X := X) (E := E) (ε := ε) proj) ctx w = .ok (proj w.self, w) :=
  rfl

theorem run_loadMap (proj : S → K → V) (k : K) (ctx : Ctx) (w : World S X E) :
    run (loadMap (X := X) (E := E) (ε := ε) proj k) ctx w = .ok (proj w.self k, w) :=
  rfl

theorem run_loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) (ctx : Ctx)
    (w : World S X E) :
    run (loadMap2 (X := X) (E := E) (ε := ε) proj k₁ k₂) ctx w =
      .ok (proj w.self k₁ k₂, w) :=
  rfl

theorem run_store (upd : S → α → S) (v : α) (ctx : Ctx) (w : World S X E) :
    run (store (X := X) (E := E) (ε := ε) upd v) ctx w =
      .ok ((), { w with self := upd w.self v }) :=
  rfl

theorem run_storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S)
    (k : K) (v : V) (ctx : Ctx) (w : World S X E) :
    run (storeMap (X := X) (E := E) (ε := ε) proj upd k v) ctx w =
      .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) }) :=
  rfl

theorem run_storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) (ctx : Ctx)
    (w : World S X E) :
    run (storeMap2 (X := X) (E := E) (ε := ε) proj upd k₁ k₂ v) ctx w =
      let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
      .ok ((), { w with self := upd w.self m }) :=
  rfl

theorem run_require (c : Prop) [Decidable c] (e : ε) (ctx : Ctx) (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w =
      if c then .ok ((), w) else .error (.user e) :=
  rfl

theorem run_require_true {c : Prop} [Decidable c] (h : c) (e : ε) (ctx : Ctx)
    (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w = .ok ((), w) := by
  simp [run_require, h]

theorem run_require_false {c : Prop} [Decidable c] (h : ¬c) (e : ε) (ctx : Ctx)
    (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w = .error (.user e) := by
  simp [run_require, h]

theorem require_iff {c d : Prop} [Decidable c] [Decidable d] (e : ε)
    (h : c ↔ d) :
    require (S := S) (X := X) (E := E) c e = require d e := by
  funext ctx w
  simp only [require]
  by_cases hc : c
  · have hd : d := h.mp hc
    simp [hc, hd]
  · have hd : ¬ d := mt h.mpr hc
    simp [hc, hd]

theorem run_revert (e : ε) (ctx : Ctx) (w : World S X E) :
    run (revert (S := S) (X := X) (E := E) (α := α) e) ctx w = .error (.user e) :=
  rfl

theorem run_emit (ev : E) (ctx : Ctx) (w : World S X E) :
    run (emit (S := S) (X := X) (ε := ε) ev) ctx w =
      .ok ((), { w with log := w.log ++ [ev] }) :=
  rfl

theorem run_sender (ctx : Ctx) (w : World S X E) :
    run (sender (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.sender, w) :=
  rfl

theorem run_value (ctx : Ctx) (w : World S X E) :
    run (valueRaw (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.value, w) :=
  rfl

theorem run_selfBalance [HasSelfBalance X] (ctx : Ctx) (w : World S X E) :
    run (selfBalanceRaw (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (HasSelfBalance.get w.ext, w) :=
  rfl

theorem run_sendRaw (to amount : Nat) (ctx : Ctx) (w : World S X E) :
    run (sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w =
      match w.oracle.send to amount w.ext with
      | none => .ok (false, w)
      | some x' => .ok (true, { w with ext := x' }) :=
  rfl

/-- A successful `sendRaw` updates only `ext`. -/
theorem sendRaw_self (to amount : Nat)
    {ctx : Ctx} {w : World S X E} {v : Bool} {w' : World S X E}
    (h : run (sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w = .ok (v, w')) :
    w'.self = w.self := by
  rw [run_sendRaw] at h
  split at h <;> cases h <;> rfl

theorem run_timestamp (ctx : Ctx) (w : World S X E) :
    run (timestamp (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (ctx.timestamp, w) :=
  rfl

theorem run_blockNumber (ctx : Ctx) (w : World S X E) :
    run (blockNumber (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (ctx.blockNumber, w) :=
  rfl

theorem run_selfAddress (ctx : Ctx) (w : World S X E) :
    run (selfAddress (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.self, w) :=
  rfl

theorem run_addChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (addChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow) :=
  rfl

theorem run_subChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (subChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≤ a then .ok (a - b, w) else .error (.arith .underflow) :=
  rfl

theorem run_mulChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow) :=
  rfl

theorem run_divChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (divChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero) :=
  rfl

theorem run_map {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    run (f <$> x) ctx w =
      match run x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e := by
  cases h : x ctx w with
  | error e =>
    change ((fun (p : α × World S X E) => (f p.1, p.2)) <$> x ctx w) = _
    simp [run, h, Functor.map, Except.map]
  | ok p =>
    change ((fun (p : α × World S X E) => (f p.1, p.2)) <$> x ctx w) = _
    simp [run, h, Functor.map, Except.map]

theorem map_apply {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    (f <$> x) ctx w =
      match x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e :=
  run_map f x ctx w

/-- `boolBit <$> sendRaw` is the Core denotation of `Op.send`. -/
theorem run_sendAsNat (to amount : Nat) (ctx : Ctx) (w : World S X E) :
    run (boolBit <$> sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w =
      match w.oracle.send to amount w.ext with
      | none => .ok (0, w)
      | some x' => .ok (1, { w with ext := x' }) := by
  rw [run_map, run_sendRaw]
  cases w.oracle.send to amount w.ext <;> rfl

theorem run_ite (c : Prop) [Decidable c] (x y : Tx S X E ε α) (ctx : Ctx)
    (w : World S X E) :
    run (if c then x else y) ctx w = if c then run x ctx w else run y ctx w := by
  split <;> rfl

theorem run_ok_error {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} {e : Err ε}
    (hok : run x ctx w = .ok (a, w')) (herr : run x ctx w = .error e) : False :=
  nomatch hok.symm.trans herr

theorem run_ok_toOption {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} (h : run x ctx w = .ok (a, w')) :
    (run x ctx w).toOption = some (a, w') := by
  rw [h]; rfl

theorem run_toOption_ok {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} (h : (run x ctx w).toOption = some (a, w')) :
    run x ctx w = .ok (a, w') := by
  revert h
  simp only [run]
  cases x ctx w with
  | error _ => intro h; cases h
  | ok p =>
    intro h
    exact congrArg Except.ok (Option.some.inj h)

theorem run_toOption_iff {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} :
    (run x ctx w).toOption = some (a, w') ↔ run x ctx w = .ok (a, w') :=
  ⟨run_toOption_ok, run_ok_toOption⟩

theorem run_toOption_some {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {p : α × World S X E} (h : (run x ctx w).toOption = some p) :
    ∃ a w', run x ctx w = .ok (a, w') ∧ p = (a, w') := by
  cases p with
  | mk a w' => exact ⟨a, w', run_toOption_ok h, rfl⟩

theorem bind_assoc {β γ : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β)
    (g : β → Tx S X E ε γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext ctx w
  simp only [bind, ReaderT.bind, StateT.bind]
  cases x ctx w <;> rfl

theorem bind_assoc_pure {β γ : Type} (x : Tx S X E ε α)
    (k : α → Tx S X E ε β) (f : β → γ) :
    (x >>= k) >>= (fun b => pure (f b)) =
      x >>= fun a => k a >>= fun b => pure (f b) :=
  bind_assoc x k (fun b => pure (f b))

theorem discard_bind_pure {β γ : Type} (x : Tx S X E ε α) (y : Tx S X E ε β)
    (f : β → γ) :
    (x >>= fun _ => y) >>= (fun b => pure (f b)) =
      x >>= fun _ => y >>= fun b => pure (f b) :=
  bind_assoc_pure x (fun _ => y) f

theorem pure_bind {β : Type} (a : α) (f : α → Tx S X E ε β) :
    pure a >>= f = f a := by
  funext ctx w
  simp only [bind, pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure]
  rfl

theorem bind_pure (x : Tx S X E ε α) : x >>= pure = x := by
  funext ctx w
  simp only [bind, pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure]
  cases x ctx w <;> rfl

theorem map_eq_pure_bind {β : Type} (f : α → β) (x : Tx S X E ε α) :
    f <$> x = x >>= fun a => pure (f a) := by
  funext ctx w
  change run (f <$> x) ctx w = run (x >>= fun a => pure (f a)) ctx w
  simp only [run_map, run_bind, run_pure]

theorem map_bind {β γ : Type} (f : β → γ) (x : Tx S X E ε α) (k : α → Tx S X E ε β) :
    f <$> (x >>= k) = x >>= fun a => f <$> k a := by
  funext ctx w
  change run (f <$> (x >>= k)) ctx w = run (x >>= fun a => f <$> k a) ctx w
  simp only [run_map, run_bind]
  cases run x ctx w <;> rfl

theorem bind_map {β γ : Type} (f : α → β) (x : Tx S X E ε α) (k : β → Tx S X E ε γ) :
    (f <$> x) >>= k = x >>= fun a => k (f a) := by
  funext ctx w
  change run ((f <$> x) >>= k) ctx w = run (x >>= fun a => k (f a)) ctx w
  simp only [run_map, run_bind]
  cases run x ctx w <;> rfl

theorem map_discard {β γ : Type} (f : α → β) (x : Tx S X E ε γ)
    (y : Tx S X E ε α) :
    f <$> (x >>= fun _ => y) = x >>= fun _ => f <$> y :=
  map_bind f x (fun _ => y)

theorem map_pure {β : Type} (f : α → β) (a : α) :
    f <$> (pure a : Tx S X E ε α) = pure (f a) := by
  rw [map_eq_pure_bind, pure_bind]

theorem map_ite {β : Type} (c : Prop) [Decidable c] (f : α → β)
    (t e : Tx S X E ε α) :
    f <$> (if c then t else e) = if c then (f <$> t) else (f <$> e) := by
  split <;> rfl

theorem map_revert {β : Type} (f : α → β) (e : ε) :
    f <$> (revert (S := S) (X := X) (E := E) (α := α) e) = revert e := by
  funext ctx w
  change run (f <$> revert e) ctx w = run (revert e) ctx w
  simp [run_map, run_revert]

theorem bind_ite {β : Type} (c : Prop) [Decidable c] (t e : Tx S X E ε α)
    (k : α → Tx S X E ε β) :
    (if c then t else e) >>= k = if c then (t >>= k) else (e >>= k) := by
  split <;> rfl

end Lsc.Tx.Proof

namespace Lsc.Lang.Proof

theorem worldAfter_ok {S X E ε α} {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' := by
  simp [worldAfter, h]

theorem worldAfter_error {S X E ε α} {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w := by
  simp [worldAfter, h]

theorem worldAfter_map {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter (f <$> x) ctx w = worldAfter x ctx w := by
  simp [worldAfter, Tx.Proof.run_map]
  cases Tx.run x ctx w <;> rfl

theorem worldAfter_wrap {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (f <$> x) ctx w :=
  (worldAfter_map f x ctx w).symm

theorem worldAfter_wrap_eq {S X E ε α β} (f : α → β) {x : Tx S X E ε α}
    {y : Tx S X E ε β} {ctx : Ctx} {w : World S X E}
    (h : f <$> x = y) :
    worldAfter x ctx w = worldAfter y ctx w := by
  rw [worldAfter_wrap f, h]

end Lsc.Lang.Proof
