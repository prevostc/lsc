import Mathlib.Logic.Function.Basic

/-!
# the contract monad

The surface language is plain Lean: contract functions are ordinary definitions in the
`Tx S X E ε` monad, written with `do` notation and a fixed set of primitives. Everything
in this file is the *semantics*; the reifier (`Lsc.Lang.Reify`) recovers a `Core` term from
such definitions and certifies `Core.denote core = f` by `rfl`, or by the monad laws below
when an `@[lsc_inline]` helper sits mid-`do` (`bind` is not definitionally associative).

Design constraints that matter for the certificate:

* every primitive is a transparent function `Ctx → World → Except …`, so that the
  kernel can unfold both the user program and `Core.denote` to the same normal form
  when association already matches;
* `Address` is a `def` newtype over `Nat` (definitionally a word) so that the untyped
  `Core` and the typed surface agree up to unfolding;
* checked arithmetic lives in the monad (`let x ← a +? b`) because it can revert;
  pure arithmetic on words is only available in its wrapping form (`a +↻ b`).
-/

namespace Lsc

/-- EVM address. A `def` newtype: definitionally `Nat`, syntactically distinct so the
reifier and the ABI layer can tell addresses from amounts. -/
def Address : Type := Nat

namespace Address
instance : DecidableEq Address := inferInstanceAs (DecidableEq Nat)
instance : OfNat Address n := ⟨(n : Nat)⟩
instance : Repr Address := inferInstanceAs (Repr Nat)
instance : Inhabited Address := ⟨(0 : Nat)⟩
instance : ToString Address := inferInstanceAs (ToString Nat)
/-- Unfolds to the underlying word. Used so ABI `List Nat` encodes without
getting stuck under `rw` (`Address` is a `def` newtype). -/
@[reducible] def toWord (a : Address) : Nat := a
end Address

/-- Storage mappings are plain functions with default zero. -/
abbrev Mapping (K V : Type) := K → V

/-- `2^256`: the EVM word bound. -/
def wordBound : Nat := 2 ^ 256

/-- Transaction context (the part of the EVM environment a contract can observe). -/
structure Ctx where
  sender : Address
  value : Nat := 0
  timestamp : Nat := 0
  blockNumber : Nat := 0
  self : Address := 0
  deriving Repr

/-- The world a contract executes in: own storage `self`, external ghosts `ext`,
the event log, and the fault oracle (`faults` / `ncalls`). `faults` defaults to
success; theorems quantify over all oracles. `ext` has no type-class default
(that would constrain `World`/`Tx` by `Inhabited` and change `Tx`'s arity).
Call sites that omit a ghost use `ext := default` (e.g. `X := Unit`). -/
structure World (S X E : Type) where
  self : S
  ext : X
  log : List E := []
  faults : Nat → Bool := fun _ => false
  ncalls : Nat := 0

/-- Reasons an arithmetic primitive reverts (Solidity `Panic` codes 0x11/0x12). -/
inductive ArithError
  | overflow
  | underflow
  | divByZero
  deriving DecidableEq, Repr

/-- A revert is a user-declared error, an arithmetic panic, or a failed external call. -/
inductive Err (ε : Type)
  | user (e : ε)
  | arith (a : ArithError)
  | callFailed
  deriving DecidableEq, Repr

/-- The contract monad: read the context, thread the world, revert with `Err ε`.
A revert discards state and logs, exactly like the EVM. -/
abbrev Tx (S X E ε : Type) (α : Type) : Type :=
  ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α

namespace Tx

variable {S X E ε : Type} {α K K₁ K₂ V : Type}

/-- Run a transaction: the function view used by all simp lemmas. -/
def run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) : Except (Err ε) (α × World S X E) :=
  x ctx w

/-! ### Storage -/

/-- Read a scalar field. `proj` is a projection of the storage structure. -/
def load (proj : S → α) : Tx S X E ε α :=
  fun _ w => .ok (proj w.self, w)

/-- Read a single-key mapping field. -/
def loadMap (proj : S → K → V) (k : K) : Tx S X E ε V :=
  fun _ w => .ok (proj w.self k, w)

/-- Read a double-key mapping field. -/
def loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) : Tx S X E ε V :=
  fun _ w => .ok (proj w.self k₁ k₂, w)

/-- Write a scalar field. `upd σ v` is the structure update `{ σ with f := v }`. -/
def store (upd : S → α → S) (v : α) : Tx S X E ε Unit :=
  fun _ w => .ok ((), { w with self := upd w.self v })

/-- Write one key of a single-key mapping field. -/
def storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S) (k : K) (v : V) :
    Tx S X E ε Unit :=
  fun _ w => .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) })

/-- Write one key pair of a double-key mapping field. -/
def storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) : Tx S X E ε Unit :=
  fun _ w =>
    let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
    .ok ((), { w with self := upd w.self m })

/-! ### Control -/

/-- Revert with a user error unless `c` holds. -/
def require (c : Prop) [Decidable c] (e : ε) : Tx S X E ε Unit :=
  fun _ w => if c then .ok ((), w) else .error (.user e)

/-- Revert with a user error. -/
def revert (e : ε) : Tx S X E ε α :=
  fun _ _ => .error (.user e)

/-- Emit an event. -/
def emit (ev : E) : Tx S X E ε Unit :=
  fun _ w => .ok ((), { w with log := w.log ++ [ev] })

/-! ### Context -/

def sender : Tx S X E ε Address := fun ctx w => .ok (ctx.sender, w)
def value : Tx S X E ε Nat := fun ctx w => .ok (ctx.value, w)
def timestamp : Tx S X E ε Nat := fun ctx w => .ok (ctx.timestamp, w)
def blockNumber : Tx S X E ε Nat := fun ctx w => .ok (ctx.blockNumber, w)
def selfAddress : Tx S X E ε Address := fun ctx w => .ok (ctx.self, w)

/-! ### Checked arithmetic (reverts like Solidity ≥ 0.8) -/

def addChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow)

def subChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if b ≤ a then .ok (a - b, w) else .error (.arith .underflow)

def mulChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow)

def divChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero)

/-! ### Checked arithmetic class (`Word`, `Amount a`, and `Fixed d` share `+? -? *? /?`) -/

/-- Checked add: same type on both sides, revert on overflow. -/
class HAddChecked (α β : Type) (γ : outParam Type) where
  hAdd {S X E ε : Type} : α → β → Tx S X E ε γ

/-- Checked subtract: same type on both sides, revert on underflow. -/
class HSubChecked (α β : Type) (γ : outParam Type) where
  hSub {S X E ε : Type} : α → β → Tx S X E ε γ

/-- Checked multiply. `Amount a *? Word` scales; `Amount a *? Amount b` is not an instance. -/
class HMulChecked (α β : Type) (γ : outParam Type) where
  hMul {S X E ε : Type} : α → β → Tx S X E ε γ

/-- Checked divide. `Amount a /? Word` scales; `Amount a /? Amount b` is not an instance. -/
class HDivChecked (α β : Type) (γ : outParam Type) where
  hDiv {S X E ε : Type} : α → β → Tx S X E ε γ

instance : HAddChecked Nat Nat Nat where
  hAdd := addChecked
instance : HSubChecked Nat Nat Nat where
  hSub := subChecked
instance : HMulChecked Nat Nat Nat where
  hMul := mulChecked
instance : HDivChecked Nat Nat Nat where
  hDiv := divChecked

/-! ### Wrapping arithmetic (pure, exactly the EVM) -/

def addWrap (a b : Nat) : Nat := (a + b) % wordBound
def subWrap (a b : Nat) : Nat := (a + wordBound - b) % wordBound
def mulWrap (a b : Nat) : Nat := (a * b) % wordBound

/-! ### Run lemmas: the simp set that turns a `Tx` program into a case analysis -/

section RunLemmas

@[simp] theorem run_pure (a : α) (ctx : Ctx) (w : World S X E) :
    run (pure a : Tx S X E ε α) ctx w = .ok (a, w) := rfl

/-- `x.run ctx w` is `ReaderT.run`; rewrite it to `Tx.run` so the `run_*` lemmas match. -/
@[simp] theorem readerRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    ReaderT.run x ctx w = run x ctx w := rfl

@[simp] theorem stateRun_eq_run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    StateT.run (ReaderT.run x ctx) w = run x ctx w := rfl

@[simp] theorem run_bind {β : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β) (ctx : Ctx)
    (w : World S X E) :
    run (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e := by
  simp only [run, bind, ReaderT.bind, StateT.bind]
  cases x ctx w <;> rfl

@[simp] theorem run_load (proj : S → α) (ctx : Ctx) (w : World S X E) :
    run (load (X := X) (E := E) (ε := ε) proj) ctx w = .ok (proj w.self, w) := rfl

@[simp] theorem run_loadMap (proj : S → K → V) (k : K) (ctx : Ctx) (w : World S X E) :
    run (loadMap (X := X) (E := E) (ε := ε) proj k) ctx w = .ok (proj w.self k, w) := rfl

@[simp] theorem run_loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) (ctx : Ctx)
    (w : World S X E) :
    run (loadMap2 (X := X) (E := E) (ε := ε) proj k₁ k₂) ctx w = .ok (proj w.self k₁ k₂, w) := rfl

@[simp] theorem run_store (upd : S → α → S) (v : α) (ctx : Ctx) (w : World S X E) :
    run (store (X := X) (E := E) (ε := ε) upd v) ctx w =
      .ok ((), { w with self := upd w.self v }) := rfl

@[simp] theorem run_storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S)
    (k : K) (v : V) (ctx : Ctx) (w : World S X E) :
    run (storeMap (X := X) (E := E) (ε := ε) proj upd k v) ctx w =
      .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) }) := rfl

@[simp] theorem run_storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) (ctx : Ctx) (w : World S X E) :
    run (storeMap2 (X := X) (E := E) (ε := ε) proj upd k₁ k₂ v) ctx w =
      let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
      .ok ((), { w with self := upd w.self m }) :=
  rfl

@[simp] theorem run_require (c : Prop) [Decidable c] (e : ε) (ctx : Ctx) (w : World S X E) :
    run (require (S := S) (X := X) (E := E) c e) ctx w =
      if c then .ok ((), w) else .error (.user e) := rfl

@[simp] theorem run_revert (e : ε) (ctx : Ctx) (w : World S X E) :
    run (revert (S := S) (X := X) (E := E) (α := α) e) ctx w = .error (.user e) := rfl

@[simp] theorem run_emit (ev : E) (ctx : Ctx) (w : World S X E) :
    run (emit (S := S) (X := X) (ε := ε) ev) ctx w =
      .ok ((), { w with log := w.log ++ [ev] }) := rfl

@[simp] theorem run_sender (ctx : Ctx) (w : World S X E) :
    run (sender (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.sender, w) := rfl

@[simp] theorem run_value (ctx : Ctx) (w : World S X E) :
    run (value (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.value, w) := rfl

@[simp] theorem run_timestamp (ctx : Ctx) (w : World S X E) :
    run (timestamp (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.timestamp, w) := rfl

@[simp] theorem run_blockNumber (ctx : Ctx) (w : World S X E) :
    run (blockNumber (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.blockNumber, w) := rfl

@[simp] theorem run_selfAddress (ctx : Ctx) (w : World S X E) :
    run (selfAddress (S := S) (X := X) (E := E) (ε := ε)) ctx w = .ok (ctx.self, w) := rfl

@[simp] theorem run_addChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (addChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow) := rfl

@[simp] theorem run_subChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (subChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≤ a then .ok (a - b, w) else .error (.arith .underflow) := rfl

@[simp] theorem run_mulChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (mulChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow) := rfl

@[simp] theorem run_divChecked (a b : Nat) (ctx : Ctx) (w : World S X E) :
    run (divChecked (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero) := rfl

/-- `do emit e; pure v` elaborates to `map`. -/
@[simp] theorem run_map {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
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

/-- `simp` after a `do` block may leave `(f <$> x) ctx w` rather than `Tx.run`. -/
@[simp] theorem map_apply {β : Type} (f : α → β) (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    (f <$> x) ctx w =
      match x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e :=
  run_map f x ctx w

/-- `if` inside a program: push `run` into the branches. -/
@[simp] theorem run_ite (c : Prop) [Decidable c] (x y : Tx S X E ε α) (ctx : Ctx)
    (w : World S X E) :
    run (if c then x else y) ctx w = if c then run x ctx w else run y ctx w := by
  split <;> rfl

theorem run_ok_error {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    {a : α} {w' : World S X E} {e : Err ε}
    (hok : run x ctx w = .ok (a, w')) (herr : run x ctx w = .error e) : False :=
  nomatch hok.symm.trans herr

end RunLemmas

/-! ### Monad laws

`Tx` inherits `LawfulMonad` from `ReaderT`/`StateT`/`Except`. The specialized
equalities are what `lsc_reify` names in the certificate fallback; they are
not `@[simp]` (the inherited `bind_assoc` / `pure_bind` already are). -/

/--
`bind` is associative as an equality of `Tx` values.

`Tx` is `ReaderT`/`StateT`/`Except` and already has `LawfulMonad`; this is
that `bind_assoc`, specialized. Unfolding an `@[lsc_inline]` helper in the
middle of a `do` block yields `bind (bind call k₁) k₂`, while `Core.denote` of
the ANF is `bind call (fun x => bind (k₁ x) k₂)`. Those are not definitionally
equal, so `lsc_reify` may use this lemma in `f.core_denote`.

That is not a trust extension: the reifier is still untrusted MetaM, and the
kernel checks `Core.denote (reify f) = f`. A wrong Core term still fails to
prove the equality. The lemma only names a law the monad already satisfies.
-/
theorem bind_assoc {β γ : Type} (x : Tx S X E ε α) (f : α → Tx S X E ε β)
    (g : β → Tx S X E ε γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext ctx w
  simp only [bind, ReaderT.bind, StateT.bind]
  cases x ctx w <;> rfl

/-- `pure` is a left identity of `bind`. -/
theorem pure_bind {β : Type} (a : α) (f : α → Tx S X E ε β) :
    pure a >>= f = f a := by
  funext ctx w
  simp only [bind, pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure]
  rfl

/-- `pure` is a right identity of `bind`. -/
theorem bind_pure (x : Tx S X E ε α) : x >>= pure = x := by
  funext ctx w
  simp only [bind, pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure]
  cases x ctx w <;> rfl

/-- `do emit e; pure v` elaborates to `map`; `Core.denote` of the ANF is `bind` then `pure`. -/
theorem map_eq_pure_bind {β : Type} (f : α → β) (x : Tx S X E ε α) :
    f <$> x = x >>= fun a => pure (f a) := by
  funext ctx w
  change run (f <$> x) ctx w = run (x >>= fun a => pure (f a)) ctx w
  simp only [run_map, run_bind, run_pure]

/-- `map` slides inside `bind`. Needed when an Amount-returning function is
`ofWord <$>` a Core sequence, while the surface mapped each `balanceOf`. -/
theorem map_bind {β γ : Type} (f : β → γ) (x : Tx S X E ε α) (k : α → Tx S X E ε β) :
    f <$> (x >>= k) = x >>= fun a => f <$> k a := by
  funext ctx w
  change run (f <$> (x >>= k)) ctx w = run (x >>= fun a => f <$> k a) ctx w
  simp only [run_map, run_bind]
  cases run x ctx w <;> rfl

/-- Binding after `map` applies `k` to the mapped value. -/
theorem bind_map {β γ : Type} (f : α → β) (x : Tx S X E ε α) (k : β → Tx S X E ε γ) :
    (f <$> x) >>= k = x >>= fun a => k (f a) := by
  funext ctx w
  change run ((f <$> x) >>= k) ctx w = run (x >>= fun a => k (f a)) ctx w
  simp only [run_map, run_bind]
  cases run x ctx w <;> rfl

/-- `f <$> pure a` is `pure (f a)`. First-mint `pure (Amount.ofWord n)` vs
`ofWord <$>` Core `pure n`. -/
theorem map_pure {β : Type} (f : α → β) (a : α) :
    f <$> (pure a : Tx S X E ε α) = pure (f a) := by
  rw [map_eq_pure_bind, pure_bind]

/-- `map` distributes over `if`. -/
theorem map_ite {β : Type} (c : Prop) [Decidable c] (f : α → β)
    (t e : Tx S X E ε α) :
    f <$> (if c then t else e) = if c then (f <$> t) else (f <$> e) := by
  split <;> rfl

/-- `bind` distributes over `if`. Core.ite duplicates the continuation;
Lean `let x ← if …` is `bind` of an `ite`. -/
theorem bind_ite {β : Type} (c : Prop) [Decidable c] (t e : Tx S X E ε α)
    (k : α → Tx S X E ε β) :
    (if c then t else e) >>= k = if c then (t >>= k) else (e >>= k) := by
  split <;> rfl

end Tx

/-! Post-world of a `Tx`: success keeps the returned world, revert keeps `w`.
Lives in `Lsc.Lang` (not `Lsc`) so `open Lsc Lsc.Security` does not see two
`worldAfter`s. `lsc_contract` cites `Lsc.Lang.worldAfter` in Core-vs-Spec lemmas. -/
namespace Lang

/-- Post-world of a `Tx`: success keeps the returned world, revert keeps `w`. -/
def worldAfter {S X E ε α} (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    World S X E :=
  match Tx.run x ctx w with
  | .ok (_, w') => w'
  | .error _ => w

@[simp] theorem worldAfter_ok {S X E ε α} {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' := by
  simp [worldAfter, h]

@[simp] theorem worldAfter_error {S X E ε α} {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w := by
  simp [worldAfter, h]

/-- Mapping the result does not change the post-world. Used when `core_denote`
is `ofWord <$> Core.denote = f`. -/
theorem worldAfter_map {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter (f <$> x) ctx w = worldAfter x ctx w := by
  simp [worldAfter, Tx.run_map]
  cases Tx.run x ctx w <;> rfl

/-- Reverse `worldAfter_map` so `rw` can wrap a Core denotation (`ofWord <$>`,
pair reconstruction, `Ref.mk <$>`). -/
theorem worldAfter_wrap {S X E ε α β} (f : α → β) (x : Tx S X E ε α)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (f <$> x) ctx w :=
  (worldAfter_map f x ctx w).symm

end Lang

/-! ### Surface sugar

`+?` / `+↻` are macros over the primitives. `read` / `write` are named
syntax; their elaborators live in `Lsc.Lang.Interface` so they can wrap
`Amount` / `Ref` fields to the schema's word form (`ofWord` / `.raw`,
`{ addr := · }` / `.addr`). The reifier still matches `Tx.load` / `Tx.store`.

* `read f`, `read f[k]`, `read f[k₁, k₂]` — storage reads
* `write f v`, `write f[k] v`, `write f[k₁, k₂] v` — storage writes
* `a +? b`, `a -? b`, `a *? b`, `a /? b` — checked arithmetic (monadic, bind with `←`)
* `a +↻ b`, `a -↻ b`, `a *↻ b` — wrapping arithmetic (pure)
-/
namespace Syntax
open Lean

scoped syntax:max (name := lscRead) "read " ident ("[" term,+ "]")? : term
scoped syntax:max (name := lscWrite) "write " ident ("[" term,+ "]")? ppSpace term:max : term

def sigma : Ident := mkIdent `σ
def projOf (f : Ident) : Ident := mkIdent (`σ ++ f.getId)

scoped infixl:65 " +? " => Lsc.Tx.HAddChecked.hAdd
scoped infixl:65 " -? " => Lsc.Tx.HSubChecked.hSub
scoped infixl:70 " *? " => Lsc.Tx.HMulChecked.hMul
scoped infixl:70 " /? " => Lsc.Tx.HDivChecked.hDiv
scoped infixl:65 " +↻ " => Lsc.Tx.addWrap
scoped infixl:65 " -↻ " => Lsc.Tx.subWrap
scoped infixl:70 " *↻ " => Lsc.Tx.mulWrap

end Syntax

end Lsc
