import Mathlib.Logic.Function.Basic

/-!
# LSC v3 — the contract monad

The surface language is plain Lean: contract functions are ordinary definitions in the
`Tx S E ε` monad, written with `do` notation and a fixed set of primitives. Everything
in this file is the *semantics*; the reifier (`Lsc3.Reify`) recovers a `Core` term from
such definitions and certifies `Core.denote core = f` by `rfl`.

Design constraints that matter for the certificate:

* every primitive is a transparent function `Ctx → World → Except …`, so that the
  kernel can unfold both the user program and `Core.denote` to the same normal form;
* `Address` is a `def` newtype over `Nat` (definitionally a word) so that the untyped
  `Core` and the typed surface agree up to unfolding;
* checked arithmetic lives in the monad (`let x ← a +? b`) because it can revert;
  pure arithmetic on words is only available in its wrapping form (`a +↻ b`).
-/

namespace Lsc3

/-- EVM address. A `def` newtype: definitionally `Nat`, syntactically distinct so the
reifier and the ABI layer can tell addresses from amounts. -/
def Address : Type := Nat

namespace Address
instance : DecidableEq Address := inferInstanceAs (DecidableEq Nat)
instance : OfNat Address n := ⟨(n : Nat)⟩
instance : Repr Address := inferInstanceAs (Repr Nat)
instance : Inhabited Address := ⟨(0 : Nat)⟩
instance : ToString Address := inferInstanceAs (ToString Nat)
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

/-- The world a contract executes in: its own storage `S` and the events emitted so far.
`ext`/`oracle` (external contracts) are added in Phase D without changing the monad. -/
structure World (S E : Type) where
  self : S
  log : List E := []

/-- Reasons an arithmetic primitive reverts (Solidity `Panic` codes 0x11/0x12). -/
inductive ArithError
  | overflow
  | underflow
  | divByZero
  deriving DecidableEq, Repr

/-- A revert is either a user-declared error or an arithmetic panic. -/
inductive Err (ε : Type)
  | user (e : ε)
  | arith (a : ArithError)
  deriving DecidableEq, Repr

/-- The contract monad: read the context, thread the world, revert with `Err ε`.
A revert discards state and logs, exactly like the EVM. -/
abbrev Tx (S E ε : Type) (α : Type) : Type :=
  ReaderT Ctx (StateT (World S E) (Except (Err ε))) α

namespace Tx

variable {S E ε : Type} {α K K₁ K₂ V : Type}

/-- Run a transaction: the function view used by all simp lemmas. -/
def run (x : Tx S E ε α) (ctx : Ctx) (w : World S E) : Except (Err ε) (α × World S E) :=
  x ctx w

/-! ### Storage -/

/-- Read a scalar field. `proj` is a projection of the storage structure. -/
def load (proj : S → α) : Tx S E ε α :=
  fun _ w => .ok (proj w.self, w)

/-- Read a single-key mapping field. -/
def loadMap (proj : S → K → V) (k : K) : Tx S E ε V :=
  fun _ w => .ok (proj w.self k, w)

/-- Read a double-key mapping field. -/
def loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) : Tx S E ε V :=
  fun _ w => .ok (proj w.self k₁ k₂, w)

/-- Write a scalar field. `upd σ v` is the structure update `{ σ with f := v }`. -/
def store (upd : S → α → S) (v : α) : Tx S E ε Unit :=
  fun _ w => .ok ((), { w with self := upd w.self v })

/-- Write one key of a single-key mapping field. -/
def storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S) (k : K) (v : V) :
    Tx S E ε Unit :=
  fun _ w => .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) })

/-- Write one key pair of a double-key mapping field. -/
def storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) : Tx S E ε Unit :=
  fun _ w =>
    let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
    .ok ((), { w with self := upd w.self m })

/-! ### Control -/

/-- Revert with a user error unless `c` holds. -/
def require (c : Prop) [Decidable c] (e : ε) : Tx S E ε Unit :=
  fun _ w => if c then .ok ((), w) else .error (.user e)

/-- Revert with a user error. -/
def revert (e : ε) : Tx S E ε α :=
  fun _ _ => .error (.user e)

/-- Emit an event. -/
def emit (ev : E) : Tx S E ε Unit :=
  fun _ w => .ok ((), { w with log := w.log ++ [ev] })

/-! ### Context -/

def sender : Tx S E ε Address := fun ctx w => .ok (ctx.sender, w)
def value : Tx S E ε Nat := fun ctx w => .ok (ctx.value, w)
def timestamp : Tx S E ε Nat := fun ctx w => .ok (ctx.timestamp, w)
def blockNumber : Tx S E ε Nat := fun ctx w => .ok (ctx.blockNumber, w)
def selfAddress : Tx S E ε Address := fun ctx w => .ok (ctx.self, w)

/-! ### Checked arithmetic (reverts like Solidity ≥ 0.8) -/

def addChecked (a b : Nat) : Tx S E ε Nat :=
  fun _ w => if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow)

def subChecked (a b : Nat) : Tx S E ε Nat :=
  fun _ w => if b ≤ a then .ok (a - b, w) else .error (.arith .underflow)

def mulChecked (a b : Nat) : Tx S E ε Nat :=
  fun _ w => if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow)

def divChecked (a b : Nat) : Tx S E ε Nat :=
  fun _ w => if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero)

/-! ### Wrapping arithmetic (pure, exactly the EVM) -/

def addWrap (a b : Nat) : Nat := (a + b) % wordBound
def subWrap (a b : Nat) : Nat := (a + wordBound - b) % wordBound
def mulWrap (a b : Nat) : Nat := (a * b) % wordBound

/-! ### Run lemmas: the simp set that turns a `Tx` program into a case analysis -/

section RunLemmas

@[simp] theorem run_pure (a : α) (ctx : Ctx) (w : World S E) :
    run (pure a : Tx S E ε α) ctx w = .ok (a, w) := rfl

@[simp] theorem run_bind {β : Type} (x : Tx S E ε α) (f : α → Tx S E ε β) (ctx : Ctx)
    (w : World S E) :
    run (x >>= f) ctx w =
      match run x ctx w with
      | .ok (a, w') => run (f a) ctx w'
      | .error e => .error e := by
  simp only [run, bind, ReaderT.bind, StateT.bind]
  cases x ctx w <;> rfl

@[simp] theorem run_load (proj : S → α) (ctx : Ctx) (w : World S E) :
    run (load (E := E) (ε := ε) proj) ctx w = .ok (proj w.self, w) := rfl

@[simp] theorem run_loadMap (proj : S → K → V) (k : K) (ctx : Ctx) (w : World S E) :
    run (loadMap (E := E) (ε := ε) proj k) ctx w = .ok (proj w.self k, w) := rfl

@[simp] theorem run_loadMap2 (proj : S → K₁ → K₂ → V) (k₁ : K₁) (k₂ : K₂) (ctx : Ctx)
    (w : World S E) :
    run (loadMap2 (E := E) (ε := ε) proj k₁ k₂) ctx w = .ok (proj w.self k₁ k₂, w) := rfl

@[simp] theorem run_store (upd : S → α → S) (v : α) (ctx : Ctx) (w : World S E) :
    run (store (E := E) (ε := ε) upd v) ctx w = .ok ((), { w with self := upd w.self v }) := rfl

@[simp] theorem run_storeMap [DecidableEq K] (proj : S → K → V) (upd : S → (K → V) → S)
    (k : K) (v : V) (ctx : Ctx) (w : World S E) :
    run (storeMap (E := E) (ε := ε) proj upd k v) ctx w =
      .ok ((), { w with self := upd w.self (Function.update (proj w.self) k v) }) := rfl

@[simp] theorem run_storeMap2 [DecidableEq K₁] [DecidableEq K₂] (proj : S → K₁ → K₂ → V)
    (upd : S → (K₁ → K₂ → V) → S) (k₁ : K₁) (k₂ : K₂) (v : V) (ctx : Ctx) (w : World S E) :
    run (storeMap2 (E := E) (ε := ε) proj upd k₁ k₂ v) ctx w =
      let m := Function.update (proj w.self) k₁ (Function.update (proj w.self k₁) k₂ v)
      .ok ((), { w with self := upd w.self m }) :=
  rfl

@[simp] theorem run_require (c : Prop) [Decidable c] (e : ε) (ctx : Ctx) (w : World S E) :
    run (require (S := S) (E := E) c e) ctx w =
      if c then .ok ((), w) else .error (.user e) := rfl

@[simp] theorem run_revert (e : ε) (ctx : Ctx) (w : World S E) :
    run (revert (S := S) (E := E) (α := α) e) ctx w = .error (.user e) := rfl

@[simp] theorem run_emit (ev : E) (ctx : Ctx) (w : World S E) :
    run (emit (S := S) (ε := ε) ev) ctx w = .ok ((), { w with log := w.log ++ [ev] }) := rfl

@[simp] theorem run_sender (ctx : Ctx) (w : World S E) :
    run (sender (S := S) (E := E) (ε := ε)) ctx w = .ok (ctx.sender, w) := rfl

@[simp] theorem run_value (ctx : Ctx) (w : World S E) :
    run (value (S := S) (E := E) (ε := ε)) ctx w = .ok (ctx.value, w) := rfl

@[simp] theorem run_timestamp (ctx : Ctx) (w : World S E) :
    run (timestamp (S := S) (E := E) (ε := ε)) ctx w = .ok (ctx.timestamp, w) := rfl

@[simp] theorem run_blockNumber (ctx : Ctx) (w : World S E) :
    run (blockNumber (S := S) (E := E) (ε := ε)) ctx w = .ok (ctx.blockNumber, w) := rfl

@[simp] theorem run_selfAddress (ctx : Ctx) (w : World S E) :
    run (selfAddress (S := S) (E := E) (ε := ε)) ctx w = .ok (ctx.self, w) := rfl

@[simp] theorem run_addChecked (a b : Nat) (ctx : Ctx) (w : World S E) :
    run (addChecked (S := S) (E := E) (ε := ε) a b) ctx w =
      if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow) := rfl

@[simp] theorem run_subChecked (a b : Nat) (ctx : Ctx) (w : World S E) :
    run (subChecked (S := S) (E := E) (ε := ε) a b) ctx w =
      if b ≤ a then .ok (a - b, w) else .error (.arith .underflow) := rfl

@[simp] theorem run_mulChecked (a b : Nat) (ctx : Ctx) (w : World S E) :
    run (mulChecked (S := S) (E := E) (ε := ε) a b) ctx w =
      if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow) := rfl

@[simp] theorem run_divChecked (a b : Nat) (ctx : Ctx) (w : World S E) :
    run (divChecked (S := S) (E := E) (ε := ε) a b) ctx w =
      if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero) := rfl

/-- `do emit e; pure v` elaborates to `map`. -/
@[simp] theorem run_map {β : Type} (f : α → β) (x : Tx S E ε α) (ctx : Ctx) (w : World S E) :
    run (f <$> x) ctx w =
      match run x ctx w with
      | .ok (a, w') => .ok (f a, w')
      | .error e => .error e := by
  cases h : x ctx w with
  | error e =>
    change ((fun (p : α × World S E) => (f p.1, p.2)) <$> x ctx w) = _
    simp [run, h, Functor.map, Except.map]
  | ok p =>
    change ((fun (p : α × World S E) => (f p.1, p.2)) <$> x ctx w) = _
    simp [run, h, Functor.map, Except.map]

/-- `if` inside a program: push `run` into the branches. -/
@[simp] theorem run_ite (c : Prop) [Decidable c] (x y : Tx S E ε α) (ctx : Ctx) (w : World S E) :
    run (if c then x else y) ctx w = if c then run x ctx w else run y ctx w := by
  split <;> rfl

end RunLemmas

end Tx

/-! ### Surface sugar

Scoped macros only (no custom syntax categories, no elaborators): each expands to a plain
application of a primitive, which is what the reifier matches on.

* `read f`, `read f[k]`, `read f[k₁, k₂]` — storage reads
* `write f v`, `write f[k] v`, `write f[k₁, k₂] v` — storage writes
* `a +? b`, `a -? b`, `a *? b`, `a /? b` — checked arithmetic (monadic, bind with `←`)
* `a +↻ b`, `a -↻ b`, `a *↻ b` — wrapping arithmetic (pure)
-/
namespace Syntax
open Lean

scoped syntax:max "read " ident ("[" term,+ "]")? : term
scoped syntax:max "write " ident ("[" term,+ "]")? ppSpace term:max : term

private def sigma : Ident := mkIdent `σ
private def projOf (f : Ident) : Ident := mkIdent (`σ ++ f.getId)

macro_rules
  | `(read $f:ident) => `(Lsc3.Tx.load (fun $sigma => $(projOf f)))
  | `(read $f:ident [ $ks:term,* ]) => do
    match ks.getElems with
    | #[k] => `(Lsc3.Tx.loadMap (fun $sigma => $(projOf f)) $k)
    | #[k₁, k₂] => `(Lsc3.Tx.loadMap2 (fun $sigma => $(projOf f)) $k₁ $k₂)
    | _ => Macro.throwError "read: mappings have one or two keys"
  | `(write $f:ident $v) =>
    `(Lsc3.Tx.store (fun $sigma m => { $sigma with $f:ident := m }) $v)
  | `(write $f:ident [ $ks:term,* ] $v) => do
    match ks.getElems with
    | #[k] =>
      `(Lsc3.Tx.storeMap (fun $sigma => $(projOf f)) (fun $sigma m => { $sigma with $f:ident := m }) $k $v)
    | #[k₁, k₂] =>
      `(Lsc3.Tx.storeMap2 (fun $sigma => $(projOf f)) (fun $sigma m => { $sigma with $f:ident := m }) $k₁ $k₂ $v)
    | _ => Macro.throwError "write: mappings have one or two keys"

scoped infixl:65 " +? " => Lsc3.Tx.addChecked
scoped infixl:65 " -? " => Lsc3.Tx.subChecked
scoped infixl:70 " *? " => Lsc3.Tx.mulChecked
scoped infixl:70 " /? " => Lsc3.Tx.divChecked
scoped infixl:65 " +↻ " => Lsc3.Tx.addWrap
scoped infixl:65 " -↻ " => Lsc3.Tx.subWrap
scoped infixl:70 " *↻ " => Lsc3.Tx.mulWrap

end Syntax

end Lsc3
