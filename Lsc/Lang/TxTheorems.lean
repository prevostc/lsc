import Lsc.Lang.TxProof
import Lsc.Lang.InterfaceTheorems

/-!
# `Tx.run` peeling lemmas and monad laws

The simp / `obtain` set for a `Tx` program, plus the specialized monad
laws `lsc_reify` names in certificates. Success-as-hypothesis forms take
`Tx.run f ctx w = .ok (r, w')` (or a concrete `c` / oracle `none`) and
conclude about `w'` or rewrite the `run`.

In `Lsc.Lang.WordTheorems`: `run_mulDivDown` / `run_mulDivUp` / `run_pow10`.

In `Lsc.Lang.AmountTheorems`: `run_add` / `run_sub` / `run_mulScalar` /
`run_divScalar` / `run_mulDivDown` / `run_mulDivUp`.

In `Lsc.Lang.InterfaceTheorems`: `run_call` / `run_view` / `run_tryCall` /
`run_tryView`, plus `run_call_ok` / `run_call_none` / `run_view_ok` /
`run_view_none`, and `run_call_toOption` / `run_call_toOption_err`.

Schema-level `run_read` / `run_write` aliases live in `CoreTheorems`
(they need `ContractSchema`).
-/

namespace Lsc.Tx

variable {S X E ε : Type} {α K K₁ K₂ V : Type}

/-- `pure a` succeeds with `a` and does not change the world. -/
@[simp] theorem run_pure (a : α) (ctx : Ctx) (w : World S X E) :
    run (pure a : Tx S X E ε α) ctx w = .ok (a, w) :=
  Proof.run_pure a ctx w

/-- `ReaderT.run x ctx w` is `Tx.run`. -/
@[simp] theorem readerRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    ReaderT.run x ctx w = run x ctx w :=
  Proof.readerRun_eq_run x ctx w

/-- `StateT.run (ReaderT.run x ctx) w` is `Tx.run`. -/
@[simp] theorem stateRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    StateT.run (ReaderT.run x ctx) w = run x ctx w :=
  Proof.stateRun_eq_run x ctx w

/-- `run (x >>= f)` runs `x`, then `f` on success, and forwards a revert. -/
@[simp] theorem run_bind {β : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β) (ctx : Ctx)
    (w : World S X E) :
    run (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e :=
  Proof.run_bind x f ctx w

/-- `(x >>= f) ctx w` unfolds like `Tx.run (x >>= f)`. -/
@[simp] theorem bind_apply {β : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β)
    (ctx : Ctx) (w : World S X E) :
    (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e :=
  Proof.bind_apply x f ctx w

/-- A scalar load returns the projected field and does not change the world. -/
@[simp] theorem run_load (proj : S → α) (ctx : Ctx) (w : World S X E) :
    run (load (X := X) (E := E) (ε := ε) proj) ctx w = .ok (proj w.self, w) :=
  Proof.run_load proj ctx w

/-- A one-key mapping load returns the entry and does not change the world. -/
@[simp] theorem run_loadMap (proj : S → K → V) (k : K) (ctx : Ctx) (w : World S X E) :
    run (loadMap (X := X) (E := E) (ε := ε) proj k) ctx w = .ok (proj w.self k, w) :=
  Proof.run_loadMap proj k ctx w

/-- A two-key mapping load returns the entry and does not change the world. -/
@[simp] theorem run_loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) (ctx : Ctx)
    (w : World S X E) :
    run (loadMap2 (X := X) (E := E) (ε := ε) proj k₁ k₂) ctx w =
      .ok (proj w.self k₁ k₂, w) :=
  Proof.run_loadMap2 proj k₁ k₂ ctx w

/-- A scalar store updates `self` through `upd` and leaves the rest of the world. -/
@[simp] theorem run_store (upd : S → α → S) (v : α) (ctx : Ctx) (w : World S X E) :
    run (store (X := X) (E := E) (ε := ε) upd v) ctx w =
      .ok ((), { w with self := upd w.self v }) :=
  Proof.run_store upd v ctx w

/-- A one-key mapping store writes `k ↦ v` through `upd`. -/
@[simp] theorem run_storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S)
    (k : K) (v : V) (ctx : Ctx) (w : World S X E) :
    run (storeMap (X := X) (E := E) (ε := ε) proj upd k v) ctx w =
      .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) }) :=
  Proof.run_storeMap proj upd k v ctx w

/-- A two-key mapping store writes `(k₁, k₂) ↦ v` through `upd`. -/
@[simp] theorem run_storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) (ctx : Ctx)
    (w : World S X E) :
    run (storeMap2 (X := X) (E := E) (ε := ε) proj upd k₁ k₂ v) ctx w =
      let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
      .ok ((), { w with self := upd w.self m }) :=
  Proof.run_storeMap2 proj upd k₁ k₂ v ctx w

/-- `require c e` succeeds with an unchanged world when `c`, else reverts `e`. -/
@[simp] theorem run_require (c : Prop) [Decidable c] (e : ε) (ctx : Ctx) (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w =
      if c then .ok ((), w) else .error (.user e) :=
  Proof.run_require c e ctx w

/-- A successful `require` leaves the world unchanged. -/
theorem run_require_true {c : Prop} [Decidable c] (h : c) (e : ε) (ctx : Ctx)
    (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w = .ok ((), w) :=
  Proof.run_require_true h e ctx w

/-- A failing `require` reverts with the user error. -/
theorem run_require_false {c : Prop} [Decidable c] (h : ¬c) (e : ε) (ctx : Ctx)
    (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w = .error (.user e) :=
  Proof.run_require_false h e ctx w

/-- `require` depends only on the truth of the condition. -/
theorem require_iff {c d : Prop} [Decidable c] [Decidable d] (e : ε)
    (h : c ↔ d) :
    require (S := S) (X := X) (E := E) c e = require d e :=
  Proof.require_iff e h

/-- `revert e` is the user-error revert. -/
@[simp] theorem run_revert (e : ε) (ctx : Ctx) (w : World S X E) :
    run (revert (S := S) (X := X) (E := E) (α := α) e) ctx w = .error (.user e) :=
  Proof.run_revert e ctx w

/-- `emit ev` appends `ev` to the log and otherwise leaves the world. -/
@[simp] theorem run_emit (ev : E) (ctx : Ctx) (w : World S X E) :
    run (emit (S := S) (X := X) (ε := ε) ev) ctx w =
      .ok ((), { w with log := w.log ++ [ev] }) :=
  Proof.run_emit ev ctx w

/-- `sender` returns `ctx.sender` and does not change the world. -/
@[simp] theorem run_sender (ctx : Ctx) (w : World S X E) :
    run (sender (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.sender, w) :=
  Proof.run_sender ctx w

/-- `valueRaw` returns `ctx.value` and does not change the world. -/
@[simp] theorem run_value (ctx : Ctx) (w : World S X E) :
    run (valueRaw (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.value, w) :=
  Proof.run_value ctx w

/-- `selfBalanceRaw` returns the `HasSelfBalance` projection of `ext`. -/
@[simp] theorem run_selfBalance [HasSelfBalance X] (ctx : Ctx) (w : World S X E) :
    run (selfBalanceRaw (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (HasSelfBalance.get w.ext, w) :=
  Proof.run_selfBalance ctx w

/-- `sendRaw` is `oracle.send`: failure is `false` and leaves `w`. -/
@[simp] theorem run_sendRaw (to amount : Nat) (ctx : Ctx) (w : World S X E) :
    run (sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w =
      match w.oracle.send to amount w.ext with
      | none => .ok (false, w)
      | some x' => .ok (true, { w with ext := x' }) :=
  Proof.run_sendRaw to amount ctx w

/-- A successful `sendRaw` updates only `ext`. -/
theorem sendRaw_self (to amount : Nat)
    {ctx : Ctx} {w : World S X E} {v : Bool} {w' : World S X E}
    (h : run (sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w = .ok (v, w')) :
    w'.self = w.self :=
  Proof.sendRaw_self to amount h

/-- `boolBit <$> sendRaw` is the Core denotation of `Op.send`. -/
@[simp] theorem run_sendAsNat (to amount : Nat) (ctx : Ctx) (w : World S X E) :
    run (boolBit <$> sendRaw (S := S) (E := E) (ε := ε) to amount) ctx w =
      match w.oracle.send to amount w.ext with
      | none => .ok (0, w)
      | some x' => .ok (1, { w with ext := x' }) :=
  Proof.run_sendAsNat to amount ctx w

/-- `timestamp` returns `ctx.timestamp` and does not change the world. -/
@[simp] theorem run_timestamp (ctx : Ctx) (w : World S X E) :
    run (timestamp (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (ctx.timestamp, w) :=
  Proof.run_timestamp ctx w

/-- `blockNumber` returns `ctx.blockNumber` and does not change the world. -/
@[simp] theorem run_blockNumber (ctx : Ctx) (w : World S X E) :
    run (blockNumber (S := S) (X := X) (E := E) (ε := ε)) ctx w =
      .ok (ctx.blockNumber, w) :=
  Proof.run_blockNumber ctx w

/-- `selfAddress` returns `ctx.self` and does not change the world. -/
@[simp] theorem run_selfAddress (ctx : Ctx) (w : World S X E) :
    run (selfAddress (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.self, w) :=
  Proof.run_selfAddress ctx w

/-- Checked add: the mathematical sum when it fits in a word, else overflow. -/
@[simp] theorem run_addChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (addChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow) :=
  Proof.run_addChecked a b ctx w

/-- Checked subtract: the mathematical difference when it does not underflow. -/
@[simp] theorem run_subChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (subChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≤ a then .ok (a - b, w) else .error (.arith .underflow) :=
  Proof.run_subChecked a b ctx w

/-- Checked multiply: the mathematical product when it fits in a word. -/
@[simp] theorem run_mulChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow) :=
  Proof.run_mulChecked a b ctx w

/-- Checked divide: the mathematical quotient when the divisor is nonzero. -/
@[simp] theorem run_divChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (divChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero) :=
  Proof.run_divChecked a b ctx w

/-- `run (f <$> x)` maps the successful value and forwards a revert. -/
@[simp] theorem run_map {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    run (f <$> x) ctx w =
      match run x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e :=
  Proof.run_map f x ctx w

/-- `(f <$> x) ctx w` unfolds like `Tx.run (f <$> x)`. -/
@[simp] theorem map_apply {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    (f <$> x) ctx w =
      match x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e :=
  Proof.map_apply f x ctx w

/-- `run` of an `if` is the `if` of the two runs. -/
@[simp] theorem run_ite (c : Prop) [Decidable c] (x y : Tx S X E ε α) (ctx : Ctx)
    (w : World S X E) :
    run (if c then x else y) ctx w = if c then run x ctx w else run y ctx w :=
  Proof.run_ite c x y ctx w

/-- A run cannot be both `.ok` and `.error`. -/
theorem run_ok_error {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} {e : Err ε}
    (hok : run x ctx w = .ok (a, w')) (herr : run x ctx w = .error e) : False :=
  Proof.run_ok_error hok herr

/-- A successful `Tx.run` is `some` as an `Option`. -/
theorem run_ok_toOption {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} (h : run x ctx w = .ok (a, w')) :
    (run x ctx w).toOption = some (a, w') :=
  Proof.run_ok_toOption h

/-- `toOption = some` implies a successful `Tx.run`. -/
theorem run_toOption_ok {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} (h : (run x ctx w).toOption = some (a, w')) :
    run x ctx w = .ok (a, w') :=
  Proof.run_toOption_ok h

/-- `toOption` of a run is `some p` exactly when the run is `.ok p`. -/
theorem run_toOption_iff {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} :
    (run x ctx w).toOption = some (a, w') ↔ run x ctx w = .ok (a, w') :=
  Proof.run_toOption_iff

/-- A `some` unwraps to a successful run. -/
theorem run_toOption_some {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {p : α × World S X E} (h : (run x ctx w).toOption = some p) :
    ∃ a w', run x ctx w = .ok (a, w') ∧ p = (a, w') :=
  Proof.run_toOption_some h

/-- `bind` is associative as an equality of `Tx` values. -/
theorem bind_assoc {β γ : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β)
    (g : β → Tx S X E ε γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g :=
  Proof.bind_assoc x f g

/-- First-order `bind_assoc` when the outer continuation is `pure ∘ f`. -/
theorem bind_assoc_pure {β γ : Type} (x : Tx S X E ε α)
    (k : α → Tx S X E ε β) (f : β → γ) :
    (x >>= k) >>= (fun b => pure (f b)) =
      x >>= fun a => k a >>= fun b => pure (f b) :=
  Proof.bind_assoc_pure x k f

/-- Discarded bind then `pure ∘ f`, first-order in the discarded body. -/
theorem discard_bind_pure {β γ : Type} (x : Tx S X E ε α) (y : Tx S X E ε β)
    (f : β → γ) :
    (x >>= fun _ => y) >>= (fun b => pure (f b)) =
      x >>= fun _ => y >>= fun b => pure (f b) :=
  Proof.discard_bind_pure x y f

/-- `pure` is a left identity of `bind`. -/
theorem pure_bind {β : Type} (a : α) (f : α → Tx S X E ε β) :
    pure a >>= f = f a :=
  Proof.pure_bind a f

/-- `pure` is a right identity of `bind`. -/
theorem bind_pure (x : Tx S X E ε α) : x >>= pure = x :=
  Proof.bind_pure x

/-- `f <$> x` is `x` then `pure (f ·)`. -/
theorem map_eq_pure_bind {β : Type} (f : α → β) (x : Tx S X E ε α) :
    f <$> x = x >>= fun a => pure (f a) :=
  Proof.map_eq_pure_bind f x

/-- `map` slides inside `bind`. -/
theorem map_bind {β γ : Type} (f : β → γ) (x : Tx S X E ε α) (k : α → Tx S X E ε β) :
    f <$> (x >>= k) = x >>= fun a => f <$> k a :=
  Proof.map_bind f x k

/-- Binding after `map` applies `k` to the mapped value. -/
theorem bind_map {β γ : Type} (f : α → β) (x : Tx S X E ε α) (k : β → Tx S X E ε γ) :
    (f <$> x) >>= k = x >>= fun a => k (f a) :=
  Proof.bind_map f x k

/-- `map` slides past a discarded bind. -/
theorem map_discard {β γ : Type} (f : α → β) (x : Tx S X E ε γ)
    (y : Tx S X E ε α) :
    f <$> (x >>= fun _ => y) = x >>= fun _ => f <$> y :=
  Proof.map_discard f x y

/-- `f <$> pure a` is `pure (f a)`. -/
theorem map_pure {β : Type} (f : α → β) (a : α) :
    f <$> (pure a : Tx S X E ε α) = pure (f a) :=
  Proof.map_pure f a

/-- `map` distributes over `if`. -/
theorem map_ite {β : Type} (c : Prop) [Decidable c] (f : α → β)
    (t e : Tx S X E ε α) :
    f <$> (if c then t else e) = if c then (f <$> t) else (f <$> e) :=
  Proof.map_ite c f t e

/-- Mapping a reverted program is still that revert. -/
theorem map_revert {β : Type} (f : α → β) (e : ε) :
    f <$> (revert (S := S) (X := X) (E := E) (α := α) e) = revert e :=
  Proof.map_revert f e

/-- `bind` distributes over `if`. -/
theorem bind_ite {β : Type} (c : Prop) [Decidable c] (t e : Tx S X E ε α)
    (k : α → Tx S X E ε β) :
    (if c then t else e) >>= k = if c then (t >>= k) else (e >>= k) :=
  Proof.bind_ite c t e k

end Lsc.Tx

namespace Lsc.Lang

/-- A successful run's post-world is the returned world. -/
@[simp] theorem worldAfter_ok {S X E ε α} {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' :=
  Proof.worldAfter_ok h

/-- A reverting run's post-world is the starting world. -/
@[simp] theorem worldAfter_error {S X E ε α} {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w :=
  Proof.worldAfter_error h

/-- Mapping the result does not change the post-world. -/
theorem worldAfter_map {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter (f <$> x) ctx w = worldAfter x ctx w :=
  Proof.worldAfter_map f x ctx w

/-- Reverse `worldAfter_map`: wrapping a result does not change the post-world. -/
theorem worldAfter_wrap {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (f <$> x) ctx w :=
  Proof.worldAfter_wrap f x ctx w

/-- `worldAfter_wrap` under an equality `f <$> x = y`. -/
theorem worldAfter_wrap_eq {S X E ε α β} (f : α → β) {x : Tx S X E ε α}
    {y : Tx S X E ε β} {ctx : Ctx} {w : World S X E}
    (h : f <$> x = y) :
    worldAfter x ctx w = worldAfter y ctx w :=
  Proof.worldAfter_wrap_eq f h

end Lsc.Lang
