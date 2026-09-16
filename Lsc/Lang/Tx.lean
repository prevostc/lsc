import Mathlib.Logic.Function.Basic
import Lsc.Lang.ExtState

/-!
# the contract monad

The surface language is plain Lean: contract functions are ordinary definitions in the
`Tx S X E ε` monad, written with `do` notation and a fixed set of primitives. Everything
in this file is the *semantics*; the reifier (`Lsc.Lang.Reify`) recovers a `Core` term from
such definitions and certifies `Core.denote core = f` by `rfl`, or by the monad laws below
when an `@[internal]` helper sits mid-`do` (`bind` is not definitionally associative).

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

/-- Deterministic, memory-blind callee oracle over opaque external state `X`.
`call` is CALL: `none` is revert. `view` is STATICCALL: total, no `ext` update.
`send` is a value-carrying CALL with empty calldata (`none` is revert).
Argument/return lists are ABI words (`Word` = `Nat`). -/
structure Oracle (X : Type) where
  call : Address → Nat → List Nat → X → Option (List Nat × X) :=
    fun _ _ _ _ => none
  view : Address → Nat → List Nat → X → List Nat :=
    fun _ _ _ _ => []
  send : Address → Nat → X → Option X :=
    fun _ _ _ => none

/-- Always-revert / empty-view oracle. `World.oracle` defaults to this so
`{ self := …, ext := … }` still elaborates. -/
def Oracle.reject (X : Type) : Oracle X := {}

/-- Read the executing account's native balance from `ext`. Default `0`
when `X` is not `ExtState`. -/
class HasSelfBalance (X : Type) where
  get : X → Nat

instance (priority := low) {X : Type} : HasSelfBalance X where
  get _ := 0

instance : HasSelfBalance ExtState where
  get x := x.env.selfBalance.toNat

/-- Add `v` wei to the executing account's native balance. Default is a
no-op when `X` is not `ExtState`. The trace call step uses this so the
body sees the EVM post-transfer world (`self`'s balance already includes
`ctx.value`). -/
class HasCreditValue (X : Type) where
  credit : X → Nat → X
  credit_zero : ∀ x, credit x 0 = x

instance (priority := low) {X : Type} : HasCreditValue X where
  credit x _ := x
  credit_zero _ := rfl

/-- Incoming CALL value, already credited when the body runs. -/
def ExtState.creditValue (x : ExtState) (v : Nat) : ExtState :=
  { x with env := { x.env with
      selfBalance := BitVec.ofNat 256 (x.env.selfBalance.toNat + v) } }

@[simp] theorem ExtState.creditValue_zero (x : ExtState) :
    ExtState.creditValue x 0 = x := by
  unfold ExtState.creditValue
  have h : BitVec.ofNat 256 (x.env.selfBalance.toNat + 0) = x.env.selfBalance := by
    apply BitVec.eq_of_toNat_eq
    have hlt : x.env.selfBalance.toNat < 2 ^ 256 := x.env.selfBalance.isLt
    rw [Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [h]

instance : HasCreditValue ExtState where
  credit := ExtState.creditValue
  credit_zero := ExtState.creditValue_zero

/-- The world a contract executes in: own storage `self`, external ghosts `ext`,
the event log, and the callee `oracle`. `X` is a parameter of `World`/`Tx`;
compiled contracts instantiate it as the fixed `Lsc.ExtState`. Call sites
that omit a ghost use `ext := default`. The oracle field is never modified
by any Tx primitive. Reentrancy during a call is not modelled in this slice
(`self` is unchanged). -/
structure World (S X E : Type) where
  self : S
  ext : X
  log : List E := []
  oracle : Oracle X := {}

/-- Oracle plus `ext`: what an external `I.Impl` view actually reads. -/
structure WorldView (X : Type) where
  ext : X
  oracle : Oracle X := {}

namespace World
variable {S X E : Type}
/-- Restrict a world to the oracle/`ext` pair `I.Impl` views of a `Ref` use. -/
def view (w : World S X E) : WorldView X where
  ext := w.ext
  oracle := w.oracle
@[simp] theorem view_ext (w : World S X E) : w.view.ext = w.ext := rfl
@[simp] theorem view_oracle (w : World S X E) : w.view.oracle = w.oracle := rfl
@[simp] theorem view_set_ext (w : World S X E) (x' : X) :
    ({ w with ext := x' } : World S X E).view =
      { ext := x', oracle := w.oracle } := rfl
/-- Native balance of the executing account (`ext.env.selfBalance`). -/
def nativeBalance {S E : Type} (w : World S ExtState E) : Nat :=
  w.ext.env.selfBalance.toNat
/-- Credit `v` wei onto `self`'s native balance (EVM CALL is post-transfer
when the body runs). No-op when `HasCreditValue` is the default. -/
def creditValue [HasCreditValue X] (w : World S X E) (v : Nat) : World S X E :=
  { w with ext := HasCreditValue.credit w.ext v }
@[simp] theorem creditValue_self [HasCreditValue X] (w : World S X E) (v : Nat) :
    (creditValue w v).self = w.self := rfl
@[simp] theorem creditValue_log [HasCreditValue X] (w : World S X E) (v : Nat) :
    (creditValue w v).log = w.log := rfl
@[simp] theorem creditValue_oracle [HasCreditValue X] (w : World S X E) (v : Nat) :
    (creditValue w v).oracle = w.oracle := rfl
@[simp] theorem creditValue_view_oracle [HasCreditValue X] (w : World S X E) (v : Nat) :
    (creditValue w v).view.oracle = w.oracle := rfl
@[simp] theorem creditValue_zero [HasCreditValue X] (w : World S X E) :
    creditValue w 0 = w := by
  simp [creditValue, HasCreditValue.credit_zero]
end World

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

/-- A storage field: getter plus in-place setter. `deriving Fields` on
`structure Storage` generates one lens per field in `Storage.Fields`
(and `open`s that namespace), so `reserve1` in contract code is the
lens. `read` / `write` take these values; `read balances[who]` is
indexing sugar on a mapping lens. -/
structure Field (S : Type) (α : Type) where
  get : S → α
  set : S → α → S

/-- Marker class: `deriving Fields` on a storage structure. -/
class Fields (S : Type) : Prop

@[simp] theorem Field.get_mk {S α} (get : S → α) (set : S → α → S) :
    Field.get ⟨get, set⟩ = get := rfl
@[simp] theorem Field.set_mk {S α} (get : S → α) (set : S → α → S) :
    Field.set ⟨get, set⟩ = set := rfl

/-- The contract monad: read the context, thread the world, revert with `Err ε`.
A revert discards state and logs, exactly like the EVM. -/
abbrev Tx (S X E ε : Type) (α : Type) : Type :=
  ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α

namespace Tx

variable {S X E ε : Type} {α K K₁ K₂ V : Type}

/-- Run a transaction: the function view used by all simp lemmas. -/
def run (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) : Except (Err ε) (α × World S X E) :=
  x ctx w

/-- A plain value in a `Tx` position is `pure`. `CoeTail` (not `Coe`) so it
applies only as the last step of a coercion chain and cannot loop as
`α → Tx α → Tx (Tx α)`. Same pattern as `Thunk`. Lean unfolds the coercion
to `pure` at elaboration, so `Tx.run` lemmas about `pure` still apply. -/
instance : CoeTail α (Tx S X E ε α) := ⟨pure⟩

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
/-- Untyped `callvalue`. Core denotes `.value` as this. Typed `Tx.value`
(`Amount`, `[Payable]`) lives in `Chain.lean`. -/
def valueRaw : Tx S X E ε Nat := fun ctx w => .ok (ctx.value, w)
def timestamp : Tx S X E ε Nat := fun ctx w => .ok (ctx.timestamp, w)
def blockNumber : Tx S X E ε Nat := fun ctx w => .ok (ctx.blockNumber, w)
def selfAddress : Tx S X E ε Address := fun ctx w => .ok (ctx.self, w)
/-- Untyped `selfbalance` of `ext`. Typed `Tx.selfBalance` lives in `Chain.lean`. -/
def selfBalanceRaw [HasSelfBalance X] : Tx S X E ε Nat :=
  fun _ctx w => .ok (HasSelfBalance.get w.ext, w)
/-- Value-carrying CALL, empty calldata. `none` is `false` and leaves `w`. -/
def sendRaw (to : Nat) (amount : Nat) : Tx S X E ε Bool :=
  fun _ctx w =>
    match w.oracle.send to amount w.ext with
    | none => .ok (false, w)
    | some x' => .ok (true, { w with ext := x' })

/-! ### Checked arithmetic (reverts like Solidity ≥ 0.8) -/

def addChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if a + b < wordBound then .ok (a + b, w) else .error (.arith .overflow)

def subChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if b ≤ a then .ok (a - b, w) else .error (.arith .underflow)

def mulChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if a * b < wordBound then .ok (a * b, w) else .error (.arith .overflow)

def divChecked (a b : Nat) : Tx S X E ε Nat :=
  fun _ w => if b ≠ 0 then .ok (a / b, w) else .error (.arith .divByZero)

/-! ### Checked arithmetic class (`Word`, `Amount a`, and `Fixed d` share `+? -? *? /?`)

Monad parameters live on the class so `Tx S X E ε α` operands share the
result monad. Pure instances stay; left/right lifts bind left-to-right. -/

/-- Checked add: same type on both sides, revert on overflow. -/
class HAddChecked (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hAdd : α → β → Tx S X E ε γ

/-- Checked subtract: same type on both sides, revert on underflow. -/
class HSubChecked (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hSub : α → β → Tx S X E ε γ

/-- Checked multiply. `Amount a *? Word` scales; `Amount a *? Amount b` is not an instance. -/
class HMulChecked (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hMul : α → β → Tx S X E ε γ

/-- Checked divide. `Amount a /? Word` scales; `Amount a /? Amount b` is not an instance. -/
class HDivChecked (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hDiv : α → β → Tx S X E ε γ

instance : HAddChecked S X E ε Nat Nat Nat where
  hAdd := addChecked
instance : HSubChecked S X E ε Nat Nat Nat where
  hSub := subChecked
instance : HMulChecked S X E ε Nat Nat Nat where
  hMul := mulChecked
instance : HDivChecked S X E ε Nat Nat Nat where
  hDiv := divChecked

/-- Fused checked `⌊a * b / c⌋`. One operation, not `*?` then `/?`.
Instances: `Nat` (`Tx.mulDivDown`) and `Amount` (`Amount.mulDivDown`),
plus `Amount b` with a `Word`/`Word` ratio (scale 0). -/
class HMulDivDown (S X E ε : Type) (α β γ : Type) (δ : outParam Type) where
  hMulDivDown : α → β → γ → Tx S X E ε δ

/-- Fused checked `⌈a * b / c⌉`. -/
class HMulDivUp (S X E ε : Type) (α β γ : Type) (δ : outParam Type) where
  hMulDivUp : α → β → γ → Tx S X E ε δ

/-- Scale by a dimensionless `Fixed d`: `⌊x * r / 10^d⌋`.
`Amount a *?↓ Fixed d` (and `Fixed d *?↓ Fixed d'`) is an instance;
`Amount a *?↓ Amount b` for a non-fixed `b` is not. -/
class HMulFixedDown (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hMulFixedDown : α → β → Tx S X E ε γ

/-- Scale by a dimensionless `Fixed d`: `⌈x * r / 10^d⌉`. -/
class HMulFixedUp (S X E ε : Type) (α β : Type) (γ : outParam Type) where
  hMulFixedUp : α → β → Tx S X E ε γ

/-! Lifted operands. Premises are the unlifted instance; they compose. -/

instance (priority := high) [HAddChecked S X E ε α β γ] :
    HAddChecked S X E ε (Tx S X E ε α) β γ where
  hAdd ma b := ma >>= fun a => HAddChecked.hAdd a b
instance (priority := high) [HAddChecked S X E ε α β γ] :
    HAddChecked S X E ε α (Tx S X E ε β) γ where
  hAdd a mb := mb >>= fun b => HAddChecked.hAdd a b

instance (priority := high) [HSubChecked S X E ε α β γ] :
    HSubChecked S X E ε (Tx S X E ε α) β γ where
  hSub ma b := ma >>= fun a => HSubChecked.hSub a b
instance (priority := high) [HSubChecked S X E ε α β γ] :
    HSubChecked S X E ε α (Tx S X E ε β) γ where
  hSub a mb := mb >>= fun b => HSubChecked.hSub a b

instance (priority := high) [HMulChecked S X E ε α β γ] :
    HMulChecked S X E ε (Tx S X E ε α) β γ where
  hMul ma b := ma >>= fun a => HMulChecked.hMul a b
instance (priority := high) [HMulChecked S X E ε α β γ] :
    HMulChecked S X E ε α (Tx S X E ε β) γ where
  hMul a mb := mb >>= fun b => HMulChecked.hMul a b

instance (priority := high) [HDivChecked S X E ε α β γ] :
    HDivChecked S X E ε (Tx S X E ε α) β γ where
  hDiv ma b := ma >>= fun a => HDivChecked.hDiv a b
instance (priority := high) [HDivChecked S X E ε α β γ] :
    HDivChecked S X E ε α (Tx S X E ε β) γ where
  hDiv a mb := mb >>= fun b => HDivChecked.hDiv a b

instance (priority := high) [HMulDivDown S X E ε α β γ δ] :
    HMulDivDown S X E ε (Tx S X E ε α) β γ δ where
  hMulDivDown ma b c := ma >>= fun a => HMulDivDown.hMulDivDown a b c
instance (priority := high) [HMulDivDown S X E ε α β γ δ] :
    HMulDivDown S X E ε α (Tx S X E ε β) γ δ where
  hMulDivDown a mb c := mb >>= fun b => HMulDivDown.hMulDivDown a b c
instance (priority := high) [HMulDivDown S X E ε α β γ δ] :
    HMulDivDown S X E ε α β (Tx S X E ε γ) δ where
  hMulDivDown a b mc := mc >>= fun c => HMulDivDown.hMulDivDown a b c

instance (priority := high) [HMulDivUp S X E ε α β γ δ] :
    HMulDivUp S X E ε (Tx S X E ε α) β γ δ where
  hMulDivUp ma b c := ma >>= fun a => HMulDivUp.hMulDivUp a b c
instance (priority := high) [HMulDivUp S X E ε α β γ δ] :
    HMulDivUp S X E ε α (Tx S X E ε β) γ δ where
  hMulDivUp a mb c := mb >>= fun b => HMulDivUp.hMulDivUp a b c
instance (priority := high) [HMulDivUp S X E ε α β γ δ] :
    HMulDivUp S X E ε α β (Tx S X E ε γ) δ where
  hMulDivUp a b mc := mc >>= fun c => HMulDivUp.hMulDivUp a b c

instance (priority := high) [HMulFixedDown S X E ε α β γ] :
    HMulFixedDown S X E ε (Tx S X E ε α) β γ where
  hMulFixedDown ma b := ma >>= fun a => HMulFixedDown.hMulFixedDown a b
instance (priority := high) [HMulFixedDown S X E ε α β γ] :
    HMulFixedDown S X E ε α (Tx S X E ε β) γ where
  hMulFixedDown a mb := mb >>= fun b => HMulFixedDown.hMulFixedDown a b

instance (priority := high) [HMulFixedUp S X E ε α β γ] :
    HMulFixedUp S X E ε (Tx S X E ε α) β γ where
  hMulFixedUp ma b := ma >>= fun a => HMulFixedUp.hMulFixedUp a b
instance (priority := high) [HMulFixedUp S X E ε α β γ] :
    HMulFixedUp S X E ε α (Tx S X E ε β) γ where
  hMulFixedUp a mb := mb >>= fun b => HMulFixedUp.hMulFixedUp a b

/-- Both operands in `Tx`. Used when a binop elaborator passes two loads. -/
instance (priority := high) [HAddChecked S X E ε α β γ] :
    HAddChecked S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hAdd ma mb := ma >>= fun a => mb >>= fun b => HAddChecked.hAdd a b
instance (priority := high) [HSubChecked S X E ε α β γ] :
    HSubChecked S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hSub ma mb := ma >>= fun a => mb >>= fun b => HSubChecked.hSub a b
instance (priority := high) [HMulChecked S X E ε α β γ] :
    HMulChecked S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hMul ma mb := ma >>= fun a => mb >>= fun b => HMulChecked.hMul a b
instance (priority := high) [HDivChecked S X E ε α β γ] :
    HDivChecked S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hDiv ma mb := ma >>= fun a => mb >>= fun b => HDivChecked.hDiv a b
instance (priority := high) [HMulDivDown S X E ε α β γ δ] :
    HMulDivDown S X E ε (Tx S X E ε α) (Tx S X E ε β) (Tx S X E ε γ) δ where
  hMulDivDown ma mb mc :=
    ma >>= fun a => mb >>= fun b => mc >>= fun c => HMulDivDown.hMulDivDown a b c
instance (priority := high) [HMulDivUp S X E ε α β γ δ] :
    HMulDivUp S X E ε (Tx S X E ε α) (Tx S X E ε β) (Tx S X E ε γ) δ where
  hMulDivUp ma mb mc :=
    ma >>= fun a => mb >>= fun b => mc >>= fun c => HMulDivUp.hMulDivUp a b c
instance (priority := high) [HMulFixedDown S X E ε α β γ] :
    HMulFixedDown S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hMulFixedDown ma mb := ma >>= fun a => mb >>= fun b => HMulFixedDown.hMulFixedDown a b
instance (priority := high) [HMulFixedUp S X E ε α β γ] :
    HMulFixedUp S X E ε (Tx S X E ε α) (Tx S X E ε β) γ where
  hMulFixedUp ma mb := ma >>= fun a => mb >>= fun b => HMulFixedUp.hMulFixedUp a b

@[simp] theorem hAdd_bind_left [HAddChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HAddChecked.hAdd ma b = (ma >>= fun a => HAddChecked.hAdd a b) := rfl
@[simp] theorem hAdd_bind_right [HAddChecked S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HAddChecked.hAdd a mb = (mb >>= fun b => HAddChecked.hAdd a b) := rfl
@[simp] theorem hSub_bind_left [HSubChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HSubChecked.hSub ma b = (ma >>= fun a => HSubChecked.hSub a b) := rfl
@[simp] theorem hSub_bind_right [HSubChecked S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HSubChecked.hSub a mb = (mb >>= fun b => HSubChecked.hSub a b) := rfl
@[simp] theorem hMul_bind_left [HMulChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HMulChecked.hMul ma b = (ma >>= fun a => HMulChecked.hMul a b) := rfl
@[simp] theorem hMul_bind_right [HMulChecked S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HMulChecked.hMul a mb = (mb >>= fun b => HMulChecked.hMul a b) := rfl
@[simp] theorem hDiv_bind_left [HDivChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HDivChecked.hDiv ma b = (ma >>= fun a => HDivChecked.hDiv a b) := rfl
@[simp] theorem hDiv_bind_right [HDivChecked S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HDivChecked.hDiv a mb = (mb >>= fun b => HDivChecked.hDiv a b) := rfl
@[simp] theorem hMulDivDown_bind_left [HMulDivDown S X E ε α β γ δ]
    (ma : Tx S X E ε α) (b : β) (c : γ) :
    HMulDivDown.hMulDivDown ma b c =
      (ma >>= fun a => HMulDivDown.hMulDivDown a b c) := rfl
@[simp] theorem hMulDivDown_bind_mid [HMulDivDown S X E ε α β γ δ]
    (a : α) (mb : Tx S X E ε β) (c : γ) :
    HMulDivDown.hMulDivDown a mb c =
      (mb >>= fun b => HMulDivDown.hMulDivDown a b c) := rfl
@[simp] theorem hMulDivDown_bind_right [HMulDivDown S X E ε α β γ δ]
    (a : α) (b : β) (mc : Tx S X E ε γ) :
    HMulDivDown.hMulDivDown a b mc =
      (mc >>= fun c => HMulDivDown.hMulDivDown a b c) := rfl
@[simp] theorem hMulDivUp_bind_left [HMulDivUp S X E ε α β γ δ]
    (ma : Tx S X E ε α) (b : β) (c : γ) :
    HMulDivUp.hMulDivUp ma b c =
      (ma >>= fun a => HMulDivUp.hMulDivUp a b c) := rfl
@[simp] theorem hMulDivUp_bind_mid [HMulDivUp S X E ε α β γ δ]
    (a : α) (mb : Tx S X E ε β) (c : γ) :
    HMulDivUp.hMulDivUp a mb c =
      (mb >>= fun b => HMulDivUp.hMulDivUp a b c) := rfl
@[simp] theorem hMulDivUp_bind_right [HMulDivUp S X E ε α β γ δ]
    (a : α) (b : β) (mc : Tx S X E ε γ) :
    HMulDivUp.hMulDivUp a b mc =
      (mc >>= fun c => HMulDivUp.hMulDivUp a b c) := rfl
@[simp] theorem hMulFixedDown_bind_left [HMulFixedDown S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HMulFixedDown.hMulFixedDown ma b =
      (ma >>= fun a => HMulFixedDown.hMulFixedDown a b) := rfl
@[simp] theorem hMulFixedDown_bind_right [HMulFixedDown S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HMulFixedDown.hMulFixedDown a mb =
      (mb >>= fun b => HMulFixedDown.hMulFixedDown a b) := rfl
@[simp] theorem hMulFixedUp_bind_left [HMulFixedUp S X E ε α β γ]
    (ma : Tx S X E ε α) (b : β) :
    HMulFixedUp.hMulFixedUp ma b =
      (ma >>= fun a => HMulFixedUp.hMulFixedUp a b) := rfl
@[simp] theorem hMulFixedUp_bind_right [HMulFixedUp S X E ε α β γ]
    (a : α) (mb : Tx S X E ε β) :
    HMulFixedUp.hMulFixedUp a mb =
      (mb >>= fun b => HMulFixedUp.hMulFixedUp a b) := rfl
@[simp] theorem hAdd_bind_both [HAddChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HAddChecked.hAdd ma mb =
      (ma >>= fun a => mb >>= fun b => HAddChecked.hAdd a b) := rfl
@[simp] theorem hSub_bind_both [HSubChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HSubChecked.hSub ma mb =
      (ma >>= fun a => mb >>= fun b => HSubChecked.hSub a b) := rfl
@[simp] theorem hMul_bind_both [HMulChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HMulChecked.hMul ma mb =
      (ma >>= fun a => mb >>= fun b => HMulChecked.hMul a b) := rfl
@[simp] theorem hDiv_bind_both [HDivChecked S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HDivChecked.hDiv ma mb =
      (ma >>= fun a => mb >>= fun b => HDivChecked.hDiv a b) := rfl
@[simp] theorem hMulDivDown_bind_all [HMulDivDown S X E ε α β γ δ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) (mc : Tx S X E ε γ) :
    HMulDivDown.hMulDivDown ma mb mc =
      (ma >>= fun a => mb >>= fun b => mc >>= fun c =>
        HMulDivDown.hMulDivDown a b c) := rfl
@[simp] theorem hMulDivUp_bind_all [HMulDivUp S X E ε α β γ δ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) (mc : Tx S X E ε γ) :
    HMulDivUp.hMulDivUp ma mb mc =
      (ma >>= fun a => mb >>= fun b => mc >>= fun c =>
        HMulDivUp.hMulDivUp a b c) := rfl
@[simp] theorem hMulFixedDown_bind_both [HMulFixedDown S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HMulFixedDown.hMulFixedDown ma mb =
      (ma >>= fun a => mb >>= fun b => HMulFixedDown.hMulFixedDown a b) := rfl
@[simp] theorem hMulFixedUp_bind_both [HMulFixedUp S X E ε α β γ]
    (ma : Tx S X E ε α) (mb : Tx S X E ε β) :
    HMulFixedUp.hMulFixedUp ma mb =
      (ma >>= fun a => mb >>= fun b => HMulFixedUp.hMulFixedUp a b) := rfl

/-! ### Wrapping arithmetic (pure, exactly the EVM) -/

def addWrap (a b : Nat) : Nat := (a + b) % wordBound
def subWrap (a b : Nat) : Nat := (a + wordBound - b) % wordBound
def mulWrap (a b : Nat) : Nat := (a * b) % wordBound

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

end Lang

/-! ### Surface sugar

`+?` / `+↻` are macros over the primitives. `read` / `write` are named
syntax; their elaborators live in `Lsc.Lang.Interface` so they can wrap
`Amount` / `Ref` fields to the schema's word form (`ofWord` / `.raw`,
`{ addr := · }` / `.addr`). The reifier still matches `Tx.load` / `Tx.store`.
`write`'s argument is elaborated at `Tx S X E ε α` (pure values via
`CoeTail`). Checked `?` operators use a binop elaborator that elaborates
each operand at `Tx`, so `write f (read f +? x)` sees a `Tx` expected type
on `read` before instance synthesis.

* `read f`, `read f[k]`, `read f[k₁, k₂]` — storage reads (`f` is a `Field` lens)
* `read d.f`, `write d.f v` — `Field S α` (direction-indexed lenses)
* `write f v`, `write f[k] v`, `write f[k₁, k₂] v` — storage writes (`v` may be `Tx`)
* `a +? b`, `a -? b`, `a *? b`, `a /? b` — checked arithmetic (operands may be `Tx`)
* `a mulDiv↓ b / c`, `a mulDiv↑ b / c` — fused checked mulDiv (one op, not `*?` then `/?`)
* `a *?↓ r`, `a *?↑ r` — scale an amount by a `Fixed d` (`⌊a * r / 10^d⌋` / ceil)
* `a +↻ b`, `a -↻ b`, `a *↻ b` — wrapping arithmetic (pure)
-/
namespace Syntax
open Lean

scoped syntax:max (name := lscRead) "read " ident ("[" term,+ "]")? : term
scoped syntax:max (name := lscWrite) "write " ident ("[" term,+ "]")? ppSpace term:max : term

def sigma : Ident := mkIdent `σ

scoped syntax:65 (name := lscHAdd) term:65 " +? " term:66 : term
scoped syntax:65 (name := lscHSub) term:65 " -? " term:66 : term
scoped syntax:70 (name := lscHMul) term:70 " *? " term:71 : term
scoped syntax:70 (name := lscHDiv) term:70 " /? " term:71 : term
scoped syntax:70 (name := lscHMulFixedDown) term:70 " *?↓ " term:71 : term
scoped syntax:70 (name := lscHMulFixedUp) term:70 " *?↑ " term:71 : term
scoped infixl:65 " +↻ " => Lsc.Tx.addWrap
scoped infixl:65 " -↻ " => Lsc.Tx.subWrap
scoped infixl:70 " *↻ " => Lsc.Tx.mulWrap

/-- Fused `⌊a * b / c⌋`. Elaborates to `HMulDivDown` (`Nat` or `Amount`). -/
scoped syntax:70 (name := lscMulDivDown) term:71 " mulDiv↓ " term:71 " / " term:70 : term
/-- Fused `⌈a * b / c⌉`. -/
scoped syntax:70 (name := lscMulDivUp) term:71 " mulDiv↑ " term:71 " / " term:70 : term

end Syntax

end Lsc
