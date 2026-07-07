import Lsc.Lang.AST
import Lsc.Arithmetic

namespace Lsc

structure TxContext where
  caller : Address
  callvalue : UInt256
  timestamp : UInt256
  origin : Address
  deriving Repr, Inhabited

structure ContractState (S : Type) where
  storage : S
  context : TxContext
  locked : Bool := false
  deriving Repr

instance {S : Type} [Inhabited S] : Inhabited (ContractState S) where
  default := { storage := default, context := default }

inductive FrameworkError
  | Reentrant
  | Unauthorized
  | InvalidSelector
  /-- A black-box cross-contract invocation (`PairM.exec`/`PairM.read`, see their docstrings)
      failed. The caller never learns the callee's real error — only that the call did not
      succeed — which is what makes `exec`/`read` genuinely black box: a caller's own error type
      never needs to mention or convert the callee's. At today's Lean-semantics level this is the
      *only* way a black-box call fails (`exec`/`read` match the callee's `Except` result
      directly) — see `exec_never_silently_swallows_failure` below. Note: the real EVM `CALL`
      codegen path (`Lsc/Compile/Yul.lean`'s `safeExternalCall` lowering) additionally reverts on
      a callee returning an ABI-encoded `false` (the "non-compliant ERC20" pattern OpenZeppelin's
      `SafeERC20.safeTransfer` guards against), but that is not yet wired to `exec`/`read` at all
      and today produces a plain EVM revert with no distinguishable Lean-level error — see
      `docs/reference/ESCROW.md` and `TODO.md`. -/
  | ExternalCallFailed
  deriving Repr, DecidableEq

class ContractErrors (Err : Type) where
  arith : ArithError → Err
  fromFramework : FrameworkError → Err

def ContractErrors.unreachableArith [Inhabited Err] (_ae : ArithError) : Err :=
  default

def ContractM (S E Err : Type) (A : Type) : Type :=
  ContractState S → Except Err (A × ContractState S × List E)

namespace ContractM

variable {S E Err A B : Type}

instance : Monad (ContractM S E Err) where
  pure a := fun s => .ok (a, s, [])
  bind m f := fun s =>
    match m s with
    | .error e => .error e
    | .ok (a, s', log1) =>
      match f a s' with
      | .error e => .error e
      | .ok (b, s'', log2) => .ok (b, s'', log1 ++ log2)

@[simp]
theorem pure_apply (a : A) (s : ContractState S) :
    (pure a : ContractM S E Err A) s = .ok (a, s, []) := rfl

@[simp]
theorem bind_apply (m : ContractM S E Err A) (f : A → ContractM S E Err B) (s : ContractState S) :
    (m >>= f) s =
      match m s with
      | .error e => .error e
      | .ok (a, s', log1) =>
        match f a s' with
        | .error e => .error e
        | .ok (b, s'', log2) => .ok (b, s'', log1 ++ log2) := rfl

@[simp]
theorem bind_apply_ok (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s s' : ContractState S) (a : A) (log1 : List E)
    (h : m s = .ok (a, s', log1)) :
    (m >>= f) s =
      match f a s' with
      | .error e => .error e
      | .ok (b, s'', log2) => .ok (b, s'', log1 ++ log2) := by
  rw [bind_apply, h]

@[simp]
theorem bind_apply_err (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s : ContractState S) (e : Err) (h : m s = .error e) :
    (m >>= f) s = .error e := by
  rw [bind_apply, h]

def get : ContractM S E Err (ContractState S) :=
  fun s => .ok (s, s, [])

def modifyStorage (f : S → S) : ContractM S E Err Unit :=
  fun s => .ok ((), { s with storage := f s.storage }, [])

def emit (e : E) : ContractM S E Err Unit :=
  fun s => .ok ((), s, [e])

def revert [ContractErrors Err] (fe : FrameworkError) : ContractM S E Err A :=
  fun _ => .error (ContractErrors.fromFramework fe)

def revertArith [ContractErrors Err] (ae : ArithError) : ContractM S E Err A :=
  fun _ => .error (ContractErrors.arith ae)

def revertUser (err : Err) : ContractM S E Err A :=
  fun _ => .error err

@[simp]
theorem revertUser_apply (err : Err) (s : ContractState S) :
    (revertUser err : ContractM S E Err A) s = .error err := rfl

def require (cond : Bool) (err : Err) : ContractM S E Err Unit :=
  if cond then pure () else revertUser err

def caller : ContractM S E Err Address :=
  fun s => .ok (s.context.caller, s, [])

/-! ## Real cross-contract calls: `PairM` — two *different* storage types

A caller contract calling into a genuinely different callee contract, with its own storage
type `T`, its own event type `ET`, and its own error type `ErrT` — all distinct from the
caller's `S`/`E`/`Err`.

**Chosen model (deliberately narrow, not a generic N-contract registry):** rather than
building a full `WorldSpec`/address-book/ABI-encoded-calldata dispatch layer (explicitly out
of scope — see `TODO.md`), a caller contract that is specifically written to call one named
other contract type threads an explicit **pair of states**, `ContractState S × ContractState
T`, through its whole transaction. `PairM S T E Err A` is exactly `ContractM`'s shape
(`ContractState S → ContractState S → Except Err (...)`-style state-passing), generalized to
two states. `exec`/`read` are the pair-level primitives that actually invoke the callee's
`ContractM T ET ErrT A` computation — **black box**: the caller never needs to know the
callee's `ErrT`/`ET` at all (no `toErr`/`toEvent` conversion functions), only ever observing
either the callee's return value or a single opaque `FrameworkError.ExternalCallFailed`. This
is deliberate (see the plan discussion in `docs/reference/INTERFACES.md`): treating an
external call as an opaque, "could fail in unknown ways" boundary is what lets composable DeFi
contracts be written and proved without each caller needing to pin down every possible
callee's exact error/event taxonomy up front. A future, explicitly opt-in "interface" layer
(also `INTERFACES.md`) may let a caller trade some of that flexibility for a stronger, more
specific typed contract when the callee's real spec is known and trusted.

**Reentrancy, made structural rather than merely guarded:** because the callee's type
`ContractM T ET ErrT A` has no way to mention `S`, `PairM`, `exec`, or `read` at all, it is
*architecturally impossible* for a callee written this way to call back into the caller —
there is no nested `exec`/`read` it could even attempt to write down. Both still carry a
`locked`-flag guard (checked against the *caller's* `S` state), to cover the one residual
scenario this model does *not* rule out structurally: `release` being invoked *while the
caller state is already `locked`* (e.g. from some future, more general dispatch path that
reenters `Escrow` itself mid-call) — see `exec_locked` below.

**Scope limitation:** this only supports a *statically fixed pair* of specific, named
contract types (`S`/`T` are concrete types chosen by the contract author, e.g. `Escrow`
hard-codes `T := TokenStorage`), not a general address-indexed N-contract world. There is
also no real ABI-encoded calldata or EVM `CALL` codegen for this yet — see
`Lsc/Compile/Lower.lean` and `examples/escrow`'s docs for the concrete follow-up scope. -/
def PairM (S T E Err : Type) (A : Type) : Type :=
  ContractState S → ContractState T →
    Except Err (A × ContractState S × ContractState T × List E)

namespace PairM

variable {S T E Err A B : Type}

instance : Monad (PairM S T E Err) where
  pure a := fun s t => .ok (a, s, t, [])
  bind m f := fun s t =>
    match m s t with
    | .error e => .error e
    | .ok (a, s', t', log1) =>
      match f a s' t' with
      | .error e => .error e
      | .ok (b, s'', t'', log2) => .ok (b, s'', t'', log1 ++ log2)

@[simp]
theorem pure_apply (a : A) (s : ContractState S) (t : ContractState T) :
    (pure a : PairM S T E Err A) s t = .ok (a, s, t, []) := rfl

@[simp]
theorem bind_apply (m : PairM S T E Err A) (f : A → PairM S T E Err B)
    (s : ContractState S) (t : ContractState T) :
    (m >>= f) s t =
      match m s t with
      | .error e => .error e
      | .ok (a, s', t', log1) =>
        match f a s' t' with
        | .error e => .error e
        | .ok (b, s'', t'', log2) => .ok (b, s'', t'', log1 ++ log2) := rfl

/-- Lift a caller-side (`ContractM S E Err A`) computation into `PairM`, leaving the callee's
state `t` untouched. -/
def liftCaller (m : ContractM S E Err A) : PairM S T E Err A :=
  fun s t =>
    match m s with
    | .error e => .error e
    | .ok (a, s', log) => .ok (a, s', t, log)

@[simp]
theorem liftCaller_apply (m : ContractM S E Err A) (s : ContractState S) (t : ContractState T) :
    (liftCaller (T := T) (E := E) (Err := Err) m) s t =
      match m s with
      | .error e => .error e
      | .ok (a, s', log) => .ok (a, s', t, log) := rfl

/-- Lift a callee-side computation *of the caller's own event/error type* into `PairM`,
leaving the caller's state `s` untouched. Used internally by `externalCall2`; exposed too,
for the (rarer) case a callee already shares the caller's `E`/`Err`. -/
def liftCallee (m : ContractM T E Err A) : PairM S T E Err A :=
  fun s t =>
    match m t with
    | .error e => .error e
    | .ok (a, t', log) => .ok (a, s, t', log)

/-- The black-box, state-mutating cross-contract call primitive: invoke a callee contract with
its own storage `T`, event type `ET`, and error type `ErrT`, threading and actually updating
the callee's real state `T`. Unlike a whitebox conversion-based design, the caller never learns
`ErrT`/`ET` at all: on success only the callee's return value `A` survives (its events are
*not* folded into the caller's own log `E` — mirrors real EVM logs, where a callee's logs are
separate topics, not re-emitted under the caller's own ABI); on failure the caller observes a
single opaque `FrameworkError.ExternalCallFailed`, never the callee's real `ErrT`. Guarded by
the caller's `locked` flag (see the section docstring above for why real reentrancy is already
ruled out structurally by `callee`'s type, and what residual case this guard still covers). -/
def exec [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A) :
    PairM S T E Err A :=
  fun s t =>
    if s.locked then
      .error (ContractErrors.fromFramework .Reentrant)
    else
      match callee t with
      | .error _ => .error (ContractErrors.fromFramework .ExternalCallFailed)
      | .ok (a, t', _log) => .ok (a, { s with locked := false }, t', [])

@[simp]
theorem exec_locked [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = true) :
    (exec (S := S) (E := E) (Err := Err) callee) s t =
      .error (ContractErrors.fromFramework .Reentrant) := by
  simp [exec, h]

theorem exec_unlocked_ok [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = false)
    (a : A) (t' : ContractState T) (log : List ET)
    (hcall : callee t = .ok (a, t', log)) :
    (exec (S := S) (E := E) (Err := Err) callee) s t =
      .ok (a, { s with locked := false }, t', []) := by
  simp [exec, h, hcall]

theorem exec_unlocked_err [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = false) (e : ErrT)
    (hcall : callee t = .error e) :
    (exec (S := S) (E := E) (Err := Err) callee) s t =
      .error (ContractErrors.fromFramework .ExternalCallFailed) := by
  simp [exec, h, hcall]

/-- The black-box, read-only cross-contract call primitive: like `exec`, but **discards** any
state change and events `callee` would have produced — only the return value `A` survives
(when it succeeds at all). The callee's underlying `ContractM T ET ErrT A` value is not
prevented from *declaring* a mutation; `read` simply never lets it take effect from the
caller's point of view, matching real `STATICCALL`-style semantics without claiming EVM-opcode
fidelity (see `Lang/Syntax.lean`'s `lscRead` docstring for the surface-syntax naming
rationale). -/
def read [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A) :
    PairM S T E Err A :=
  fun s t =>
    if s.locked then
      .error (ContractErrors.fromFramework .Reentrant)
    else
      match callee t with
      | .error _ => .error (ContractErrors.fromFramework .ExternalCallFailed)
      | .ok (a, _t', _log) => .ok (a, { s with locked := false }, t, [])

@[simp]
theorem read_locked [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = true) :
    (read (S := S) (E := E) (Err := Err) callee) s t =
      .error (ContractErrors.fromFramework .Reentrant) := by
  simp [read, h]

theorem read_unlocked_ok [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = false)
    (a : A) (t' : ContractState T) (log : List ET)
    (hcall : callee t = .ok (a, t', log)) :
    (read (S := S) (E := E) (Err := Err) callee) s t =
      .ok (a, { s with locked := false }, t, []) := by
  simp [read, h, hcall]

theorem read_unlocked_err [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A)
    (s : ContractState S) (t : ContractState T) (h : s.locked = false) (e : ErrT)
    (hcall : callee t = .error e) :
    (read (S := S) (E := E) (Err := Err) callee) s t =
      .error (ContractErrors.fromFramework .ExternalCallFailed) := by
  simp [read, h, hcall]

/-- **Safe by default, made explicit**: `exec`/`read` never let a callee's failure pass through
unnoticed — there is no return value a caller could accidentally ignore (unlike a raw Solidity
`address.call(...)`, which returns `(bool success, bytes data)` that a careless caller really can
just not check). Every one of `exec`'s three outcomes (`Reentrant`/`ExternalCallFailed`/success,
`exec_locked`/`exec_unlocked_err`/`exec_unlocked_ok` above) is either a genuine `Except.error`
that aborts the *whole* caller `tx` right there, or the callee's real success value — there is no
fourth, silently-ignored-failure outcome to reach at all. This is a property of `exec`'s *type*,
not just its current definition: `PairM S T E Err A`'s codomain is `Except Err (..)`, a sum type
with no way to smuggle a "the call happened but nobody checked whether it worked" value through
that isn't already a case this theorem covers. Stated once, generically over both branches
(rather than duplicating `exec_locked`/`exec_unlocked_ok`/`exec_unlocked_err`'s case split), so a
reader (or the real EVM `CALL`-codegen path this is meant to survive into, see
`Lsc/Compile/Yul.lean`'s `safeExternalCall`) has one lemma to cite for "this primitive cannot
silently swallow a callee failure." -/
theorem exec_never_silently_swallows_failure [ContractErrors Err] {ET ErrT : Type}
    (callee : ContractM T ET ErrT A) (s : ContractState S) (t : ContractState T) :
    (∃ a s' t', exec (S := S) (E := E) (Err := Err) callee s t = .ok (a, s', t', [])) ∨
    (∃ fe, exec (S := S) (E := E) (Err := Err) callee s t = .error (ContractErrors.fromFramework fe)) := by
  unfold exec
  split
  · exact .inr ⟨.Reentrant, rfl⟩
  · split
    · exact .inr ⟨.ExternalCallFailed, rfl⟩
    · exact .inl ⟨_, _, _, rfl⟩

/-- `read`'s counterpart of `exec_never_silently_swallows_failure` — identical shape, since
`read` shares `exec`'s exact `locked`/callee-`Except` case split (it only differs in *discarding*
the callee's state/log on success, never in how failure is surfaced). -/
theorem read_never_silently_swallows_failure [ContractErrors Err] {ET ErrT : Type}
    (callee : ContractM T ET ErrT A) (s : ContractState S) (t : ContractState T) :
    (∃ a s', read (S := S) (E := E) (Err := Err) callee s t = .ok (a, s', t, [])) ∨
    (∃ fe, read (S := S) (E := E) (Err := Err) callee s t = .error (ContractErrors.fromFramework fe)) := by
  unfold read
  split
  · exact .inr ⟨.Reentrant, rfl⟩
  · split
    · exact .inr ⟨.ExternalCallFailed, rfl⟩
    · exact .inl ⟨_, _, rfl⟩

/-- Run a `PairM` computation on explicit caller/callee states — the two-contract analogue of
`runS`. -/
def run (m : PairM S T E Err A) (s : ContractState S) (t : ContractState T) :
    Except Err (A × ContractState S × ContractState T × List E) := m s t

@[simp] theorem run_def (m : PairM S T E Err A) (s : ContractState S) (t : ContractState T) :
    run m s t = m s t := rfl

end PairM

@[simp]
theorem runS_pure (a : A) (s : ContractState S) :
    (pure a : ContractM S E Err A) s = .ok (a, s, []) := rfl

@[simp]
theorem runS_get (s : ContractState S) :
    (get : ContractM S E Err (ContractState S)) s = .ok (s, s, []) := rfl

@[simp]
theorem runS_modifyStorage (f : S → S) (s : ContractState S) :
    (modifyStorage f : ContractM S E Err Unit) s =
    .ok ((), { s with storage := f s.storage }, []) := rfl

@[simp]
theorem runS_emit (e : E) (s : ContractState S) :
    (emit e : ContractM S E Err Unit) s = .ok ((), s, [e]) := rfl

@[simp]
theorem runS_require_true (err : Err) (s : ContractState S) :
    (require true err : ContractM S E Err Unit) s = .ok ((), s, []) := rfl

@[simp]
theorem runS_require_false (err : Err) (s : ContractState S) :
    (require false err : ContractM S E Err Unit) s = .error err := rfl

@[simp]
theorem runS_caller (s : ContractState S) :
    (caller : ContractM S E Err Address) s = .ok (s.context.caller, s, []) := rfl

end ContractM

def runS {S E Err A : Type} (m : ContractM S E Err A) (s : ContractState S) :
    Except Err (A × ContractState S × List E) :=
  m s

@[simp]
theorem runS_revertArith {S E Err A : Type} [ContractErrors Err] (ae : ArithError)
    (s : ContractState S) :
    runS (ContractM.revertArith ae : ContractM S E Err A) s =
      .error (ContractErrors.arith ae) := rfl

/-- Runtime values tagged by AST type. -/
inductive Val : Ty → Type
  | u256 : UInt256 → Val .uint256
  | bool : Bool → Val .bool
  | addr : Address → Val .address
  | wei : Wei → Val .wei
  | wad : Wad → Val .wad
  | unit : Val .unit

namespace Val

def boolOf (v : Val .bool) : Bool :=
  match v with | .bool b => b

@[simp]
theorem boolOf_bool (b : Bool) : Val.boolOf (.bool b) = b := rfl

def weiOf (v : Val .wei) : Wei :=
  match v with | .wei w => w

@[simp]
theorem weiOf_wei (w : Wei) : Val.weiOf (.wei w) = w := rfl

def wadOf (v : Val .wad) : Wad :=
  match v with | .wad w => w

@[simp]
theorem wadOf_wad (w : Wad) : Val.wadOf (.wad w) = w := rfl

def addrOf (v : Val .address) : Address :=
  match v with | .addr a => a

def u256Of (v : Val .uint256) : UInt256 :=
  match v with | .u256 n => n

def eq {t : Ty} (a b : Val t) : Bool :=
  match t, a, b with
  | .uint256, .u256 x, .u256 y => x == y
  | .bool, .bool x, .bool y => x == y
  | .address, .addr x, .addr y => x == y
  | .wei, .wei x, .wei y => x == y
  | .wad, .wad x, .wad y => x == y
  | .unit, .unit, .unit => true
  | _, _, _ => false

@[simp]
theorem eq_addr (x y : Address) : Val.eq (.addr x) (.addr y) = (x == y) := rfl

end Val

/-- Local variable environment for `tx` bodies, threaded through `Stmt.evalWith`.

Represented as a plain inductive snoc-list rather than the closure
(`Ident → Option (Sigma Val)`) it used to be: `lookup` on a closure-based env can only be
unfolded via `simp` (function extensionality / `funext`-style reasoning), never via cheap
`dsimp`/`rfl` iota-reduction — and that, compounded across nested `let`s and interacting with
other case splits (e.g. two chained checked arithmetic ops) in the same goal, is what made
`simp` explode on `tx` bodies with 2+ sequential `let`s (see `Wad/Eval.lean`'s module docstring
and `examples/interest`'s `accrueInterest` proofs for the concrete case this was diagnosed on).
`lookup` on this inductive form is ordinary structural recursion: once `env` is a concrete chain
of `.bind`s (always true at a call site, since it's built by `Stmt.evalWith` as it goes), each
step is a plain constructor match that `dsimp`/`rfl` reduces for free, leaving only the
(still-necessary) `Ident` `BEq` check per step — no closure/funext machinery involved. -/
inductive LocalEnv where
  | empty
  | bind (name : Ident) (val : Sigma Val) (env : LocalEnv)
  deriving Inhabited

namespace LocalEnv

def lookup : LocalEnv → Ident → Option (Sigma Val)
  | .empty, _ => none
  | .bind name val env, n => if n == name then some val else env.lookup n

@[simp] theorem lookup_empty (n : Ident) : (LocalEnv.empty).lookup n = none := rfl

@[simp] theorem bind_lookup_self (name : String) (v : Sigma Val) (env : LocalEnv) :
    (LocalEnv.bind name v env).lookup name = some v := by
  simp [LocalEnv.lookup]

@[simp] theorem bind_lookup_ne (name key : String) (v : Sigma Val) (env : LocalEnv)
    (h : key ≠ name) :
    (LocalEnv.bind name v env).lookup key = env.lookup key := by
  simp only [LocalEnv.lookup]
  rw [beq_false_of_ne h]
  simp

end LocalEnv

/-- `E`/`Err` are `outParam`s: each contract's storage type `S` has exactly one `derive_contract_dsl`-
registered `(E, Err)` pair (one contract = one event/error type triple), so once `S` is known,
`E`/`Err` should always be resolvable from it alone — needed so a `tx` body containing only a
black-box `exec`/`read` cross-contract call (no `toErr`/`toEvent`-typed argument to otherwise pin
`E`/`Err` via unification, unlike the whitebox `externalCall2` this replaced) can still have its
own `S`/`E`/`Err` resolved from context, e.g. via `(S := ..)`-pinned `ContractDSL` instance
search alone (see `Lang/Syntax.lean`'s `elabOrdinarySegment`). -/
class ContractDSL (S : Type) (E : outParam Type) (Err : outParam Type) [ContractErrors Err] where
  getField  : (t : Ty) → Ident → S → Option (Val t)
  setField  : (t : Ty) → Ident → Val t → S → S
  resolveErr : Ident → Option Err
  buildEvent : Ident → List (Sigma Val) → Option E
  /-- Read one entry (keyed by `Address`) of a `Lsc.Wad.WadMap`-kinded storage field, by field
      name — `none` iff `field` doesn't name a `WadMap` field at all (an out-of-range key is not
      representable here: `WadMap` is a total function, see its docstring, so every key always
      has *some* `Wad` value once `field` itself is valid). -/
  getMapField : Ident → Address → S → Option Wad.Wad
  /-- Write one entry (keyed by `Address`) of a `Lsc.Wad.WadMap`-kinded storage field, by field
      name — a no-op (`s` returned unchanged) iff `field` doesn't name a `WadMap` field. -/
  setMapField : Ident → Address → Wad.Wad → S → S

end Lsc
