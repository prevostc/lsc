# Implementation Guide

> **Read [DESIGN.md](../DESIGN.md) first.** This document covers *how* to build what DESIGN.md specifies.
> Extensions: [extensions/linear-types/](../extensions/linear-types/), [TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md), [MATH.md](../extensions/MATH.md), [CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md) (optional).
> Reference contracts: [reference/COUNTER.md](../reference/COUNTER.md), [reference/AMM.md](../reference/AMM.md).

---

## Module Structure

> **This section describes the actual file layout under `Lsc/`** at the repo root. See
> [`decisions/0001`](../decisions/0001-txm-superseded-by-syntax.md) and
> [`decisions/0008`](../decisions/0008-syntax-and-contract-macro-migrations.md) for why this differs
> from an earlier plan (two deleted custom-grammar/codegen attempts along the way).
> `Compile/` also grew several files the plan didn't anticipate, e.g. `Compile/Bytecode/*` for
> direct EVM bytecode emission alongside Yul.

```
Lsc/
  Core/
    UInt256.lean        -- checked UInt256 ops, ArithError
    ContractM.lean       -- ContractState, ContractM monad, ContractErrors, FrameworkError
  Types.lean              -- Word/UInt256/Address/Ident type aliases, Ty
  Arithmetic.lean         -- re-exports / shared arithmetic glue
  Lib/
    Wei.lean, Wei/{Eval,Optimize,Syntax}.lean   -- Wei type + AST fragment + eval/lower/checks
    Wad.lean, Ray.lean    -- fixed-point numeric types
    Linear/TokenAmount.lean -- linear-type stub
  Lang/
    AST.lean            -- Expr, Stmt, ContractDef, FunctionDef inductives  (unchanged in spirit)
    Eval.lean           -- ContractM, Stmt.eval                            (unchanged in spirit)
    TxM.lean            -- TxM := WriterT Stmt Id builder monad + combinators/notations;
                         --   underlies the `tx { ... }` grammar's desugaring (no longer the
                         --   contract-author-facing surface itself)
    TxMTest.lean        -- smoke tests for TxM combinators
    Syntax.lean         -- the live `tx { ... }` statement/expression grammar (declare_syntax_cat
                         --   lscExpr/lscStmt) + `derive_contract`/`derive_contract_def` commands
                         --   that assemble a full contract from `tx` blocks + the deriving handlers
    Derive.lean         -- deriving ContractStorage/ContractError/ContractEvent handlers
                         --   + derive_contract_dsl assembly step (used internally by Syntax.lean's
                         --   derive_contract/derive_contract_def)
    DeriveTest.lean     -- smoke tests for the deriving handlers
    Checks.lean         -- DAG/cycle check, selector check, UInt256-arithmetic check,
                         --   linearity stub, arith-error-coverage check
  TestFixtures/
    SyntaxSmoke.lean    -- smoke fixtures for the tx { ... } grammar
  Compile/
    IR.lean, IR/{Eval,EvalLemmas,FreeVars}.lean  -- flat IR + its semantics
    IR/Opt/{FoldConsts,ElimUnusedLocals,Pipeline}.lean -- IR-level optimization passes
    Lower.lean          -- AST → IR
    Yul.lean            -- IR → Yul text (via EvmYulLean's `EvmYul` types)
    Bytecode.lean, Bytecode/{Instr,Codegen,Encode,Contract}.lean
                         -- IR → flat EVM bytecode (direct opcode emission, bypassing Yul text)
    BytecodeExecTest.lean, BytecodeExecTestMain.lean -- EVM-execution smoke test (skipped in CI, see scripts/ci.sh)
    Correctness.lean    -- kernel-checked IR/lowering correctness lemmas (increment slice)
  Selectors.lean        -- ABI selector computation (String.hash stub; real keccak deferred)
  Prelude.lean          -- convenience re-export of the above for contract authors
  ChecksTest.lean       -- Checks.lean smoke tests

examples/counter/
  src/Counter.lean      -- reference contract, written with the tx { ... } grammar + derive_contract
  test/CounterTheorem.lean  -- 10 theorems against Counter.lean
```

Deleted relative to the original plan below: the first `Lang/Syntax.lean`, `Lang/Contract.lean`,
`Lang/ContractGen.lean`, `Lang/ContractTypes.lean`, and the top-level `SyntaxTest.lean` (see the
decision records linked above). The current `Lang/Syntax.lean` is an unrelated, later, second
file that reused the same name. `Lang/Delab.lean` (delaborators for a custom grammar) has still
not been implemented; ordinary Lean terms pretty-print using Lean's own pretty printer, and the
`tx { ... }` grammar itself has no delaborator either.

Each file imports only what is below it in this list (in spirit — `Lang/Derive.lean` additionally imports `Core/ContractM.lean` for the `ContractErrors`/`ContractDSL` instances it generates). No circular imports.

---

## Step 1 — Core Types (`Core/Types.lean`)

Start here. Everything else depends on this.

```lean
-- Core/Types.lean
import Mathlib.Data.Finmap

namespace Lsc

/-- The EVM's native word size. All storage values are Word. -/
abbrev Word := BitVec 256

/-- UInt256 is Word. We use UInt256 in type signatures for clarity. -/
abbrev UInt256 := Word

/-- Addresses are 160-bit values but we store them as Word for ABI simplicity. -/
abbrev Address := Word

/-- Storage slot index -/
abbrev Slot := Word

/-- Variable names in the AST -/
abbrev Ident := String

end Lsc
```

**Why BitVec 256, not Nat or Int**: `BitVec 256` gives you the exact EVM semantics for wrapping arithmetic out of the box. `Nat` has no overflow, `Int` has different division semantics. Lean 4's `BitVec` has solid Mathlib support and `omega` can close many goals about it directly.

---

## Step 2 — Arithmetic (`Core/Arithmetic.lean`)

Define all numeric operations before the AST. The AST will reference these types.

```lean
-- Core/Arithmetic.lean
import Lsc.Core.Types

namespace Lsc

/-- Arithmetic errors are part of the framework error hierarchy.
    They are embedded into user error types via ContractErrors. -/
inductive ArithError
  | Overflow
  | Underflow
  | DivisionByZero

namespace UInt256

/-- Framework-internal checked ops. Used by Wei/Wad/Ray wrappers — not exposed
    in contract surface syntax. Contract bodies cannot call these on bare UInt256. -/

/-- Checked add: fails on overflow. -/
def addChecked (a b : UInt256) : Except ArithError UInt256 :=
  let r := a + b
  if r < a then .error .Overflow else .ok r

/-- Checked sub: fails on underflow (a < b). -/
def subChecked (a b : UInt256) : Except ArithError UInt256 :=
  if a < b then .error .Underflow else .ok (a - b)

/-- Checked mul: fails on overflow. -/
def mulChecked (a b : UInt256) : Except ArithError UInt256 :=
  let r := a * b
  if a != 0 && r / a != b then .error .Overflow else .ok r

/-- Floor division (EVM semantics: truncates toward zero).
    Fails on division by zero. -/
def divChecked (a b : UInt256) : Except ArithError UInt256 :=
  if b == 0 then .error .DivisionByZero else .ok (a / b)

/-- Full-precision multiply-divide: computes (a * b) / c using
    a 512-bit intermediate to avoid precision loss.
    Critical for AMM math. -/
def mulDiv (a b c : UInt256) : Except ArithError UInt256 :=
  if c == 0 then .error .DivisionByZero
  else
    -- TODO: implement via Nat, then convert back
    -- interim: use Nat arithmetic (no overflow at this width)
    let r : Nat := (a.toNat * b.toNat) / c.toNat
    if r > (BitVec.allOnes 256).toNat
    then .error .Overflow
    else .ok (BitVec.ofNat 256 r)

def addCheckedNat (a : UInt256) (n : Nat) : Except ArithError UInt256 :=
  if a.val + n < 2^256 then .ok ⟨a.val + n, by omega⟩ else .error .Overflow

-- Key simp lemmas (add one per operation)
@[simp]
theorem addChecked_ok_comm (a b r : UInt256)
    (h : addChecked a b = .ok r) : addChecked b a = .ok r := by
  simp [addChecked] at h ⊢
  omega

end UInt256

-- Fixed-point types

def WAD : UInt256 := BitVec.ofNat 256 1_000_000_000_000_000_000
def RAY : UInt256 := BitVec.ofNat 256 1_000_000_000_000_000_000_000_000_000

/-- 0-decimal numeric type: 1 Wei = 1 raw unit (identity encoding). -/
structure Wei where
  raw : UInt256
  deriving Repr, DecidableEq

namespace Wei

def addChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.addChecked a.raw b.raw).map Wei.mk
def subChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.subChecked a.raw b.raw).map Wei.mk
def mulChecked (a b : Wei) : Except ArithError Wei :=
  (UInt256.mulChecked a.raw b.raw).map Wei.mk
def divFloor (a b : Wei) : Except ArithError Wei :=
  (UInt256.divChecked a.raw b.raw).map Wei.mk

def addCheckedNat (a : Wei) (n : Nat) : Except ArithError Wei :=
  (UInt256.addCheckedNat a.raw n).map Wei.mk

end Wei

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

structure Ray where
  raw : UInt256
  deriving Repr, DecidableEq

namespace Wad

def mulDown (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw b.raw WAD).map Wad.mk  -- floor bias
def mulUp (a b : Wad) : Except ArithError Wad := sorry
def mulHalfUp (a b : Wad) : Except ArithError Wad := sorry
def divDown (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw WAD b.raw).map Wad.mk
def divUp (a b : Wad) : Except ArithError Wad := sorry
def divHalfUp (a b : Wad) : Except ArithError Wad := sorry

def addChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.addChecked a.raw b.raw).map Wad.mk
def subChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.subChecked a.raw b.raw).map Wad.mk

def add (a b : Wad) : Except ArithError Wad := addChecked a b

def toRay (w : Wad) : Except ArithError Ray :=
  (UInt256.mulChecked w.raw (BitVec.ofNat 256 1_000_000_000)).map Ray.mk

-- Proof: mul is commutative (prove once, reuse everywhere)
theorem mul_comm (a b : Wad) : Wad.mul a b = Wad.mul b a := by
  simp [mul, UInt256.mulDiv]
  ring

-- Proof: multiplying by something ≤ 1 WAD does not increase value
theorem mul_le_left (a b : Wad) (hb : b.raw ≤ WAD) (r : Wad)
    (h : Wad.mul a b = .ok r) : r.raw ≤ a.raw := by
  simp [mul, UInt256.mulDiv] at h
  sorry -- TODO: complete proof using Nat arithmetic bounds

end Wad

end Lsc
```

**Note on `mulDiv`**: The interim `Nat`-based implementation is correct but allocates. Replace it with a proper 512-bit intermediate (using two `UInt256` values as hi/lo) for the production version. The proofs do not change — only the implementation.

---

## Step 3 — Mapping (`Core/Mapping.lean`)

Opaque type. Users can `get` and `set` but cannot iterate.

```lean
-- Core/Mapping.lean
import Mathlib.Data.Finmap
import Lsc.Core.Types

namespace Lsc

/-- Opaque mapping type. Backed by Finmap but iteration is not exposed.
    This prevents gas-griefing bugs and simplifies proofs. Contract authors see only
    `get`/`set`/`empty`; the Finmap stays framework-internal (see `docs/DESIGN.md` §9). -/
opaque Mapping (K V : Type) [DecidableEq K] : Type

namespace Mapping

variable {K V : Type} [DecidableEq K] [Inhabited V]

private def toFinmap : Mapping K V → Finmap (fun _ : K => V)
private def fromFinmap : Finmap (fun _ : K => V) → Mapping K V

axiom to_from (m : Finmap (fun _ : K => V)) : toFinmap (fromFinmap m) = m
axiom from_to (m : Mapping K V) : fromFinmap (toFinmap m) = m

def empty : Mapping K V := fromFinmap ∅

def get (m : Mapping K V) (k : K) : V :=
  (toFinmap m |>.lookup k).getD default

def set (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  fromFinmap (toFinmap m |>.insert k v)

-- Separation: setting one key does not affect another
@[simp]
theorem get_set_same (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v := by
  simp [get, set, Finmap.lookup_insert]

@[simp]
theorem get_set_different (m : Mapping K V) (k1 k2 : K) (v : V)
    (h : k1 ≠ k2) : (m.set k1 v).get k2 = m.get k2 := by
  simp [get, set, Finmap.lookup_insert_of_ne h]

-- No toList, no fold, no filter — intentionally omitted.
-- If you need a sum invariant, prove conservation instead (see DESIGN §10).

end Mapping

end Lsc
```

---

## Step 4 — The AST (`Lang/AST.lean`)

This is the heart of the system. Follow the dss2024 pattern exactly: separate `Expr` and `Stmt` inductives, no embedded functions, pure data.

```lean
-- Lang/AST.lean
import Lsc.Core.Types
import Lsc.Core.Arithmetic
import Lsc.Core.Mapping

namespace Lsc

/-- Type tags for the typed AST.
    These are used in Expr's index to prevent type errors at macro expansion time. -/
inductive Ty
  | uint256
  | bool
  | address
  | wei
  | wad
  | ray
  | tokenAmount        -- linear type: must be used exactly once
  | allowance          -- linear type
  | flashReceipt       -- linear type
  | lock               -- linear type
  | capability         -- linear type
  | mapping (k v : Ty) -- opaque, no iteration
  | unit

/-- Typed expression AST. Index is the return type. -/
inductive Expr : Ty → Type
  -- Literals
  | litU256   : UInt256 → Expr .uint256
  | litWei    : Nat → Expr .wei
  | litBool   : Bool    → Expr .bool
  | litAddr   : Address → Expr .address
  -- Variables (by name; scope is checked during elaboration)
  | var       : Ident → Expr t
  -- Storage reads (resolved to slot during compilation)
  | storageGet : Ident → Expr t
  -- Arithmetic — typed numerics only (Wei / Wad / Ray); no bare UInt256 ops
  | weiAddChecked | weiSubChecked | weiMulChecked | weiDivFloor
  | wadAddChecked | wadSubChecked
  | wadMulDown | wadMulUp | wadMulHalfUp
  | wadDivDown | wadDivUp | wadDivHalfUp
  | rayAddChecked | raySubChecked
  | rayMulDown | rayMulUp | rayMulHalfUp
  | rayDivDown | rayDivUp | rayDivHalfUp
  -- Comparisons
  | eq   : Expr t → Expr t → Expr .bool
  | lt   : Expr .uint256 → Expr .uint256 → Expr .bool
  | le   : Expr .uint256 → Expr .uint256 → Expr .bool
  | not  : Expr .bool → Expr .bool
  | and  : Expr .bool → Expr .bool → Expr .bool
  | or   : Expr .bool → Expr .bool → Expr .bool
  -- Transaction context (read-only, populated by dispatcher)
  | caller    : Expr .address
  | callvalue : Expr .uint256
  | timestamp : Expr .uint256
  -- Mapping operations (no iteration)
  | mappingGet : Expr (.mapping k v) → Expr k → Expr v
  -- Linear type constructors/destructors (restricted by linearity pass)
  | tokenMint   : Expr .wei → Expr .tokenAmount   -- canMint permission required
  | tokenBurn   : Expr .tokenAmount → Expr .wei   -- canBurn permission required
  | tokenSplit  : Expr .tokenAmount → Expr .wei   -- returns pair via letBind2
  | tokenMerge  : Expr .tokenAmount → Expr .tokenAmount → Expr .tokenAmount

/-- Statement AST. -/
inductive Stmt
  | skip
  | seq         : Stmt → Stmt → Stmt
  -- Bind expression result to a local variable
  | letBind     : Ident → Expr t → Stmt
  -- Bind two results (for split, etc.)
  | letBind2    : Ident → Ident → Expr t → Stmt
  -- Write to a storage field
  | storageSet  : Ident → Expr t → Stmt
  -- Write to a mapping field: storageMapSet field key value
  | storageMapSet : Ident → Expr k → Expr v → Stmt
  -- Require: if expr is false, revert with errName from user error type
  | require     : Expr .bool → Ident → Stmt
  | ifThenElse  : Expr .bool → Stmt → Stmt → Stmt
  -- Internal function call by name (call graph must be DAG)
  | call        : Ident → List (Sigma Expr) → Stmt
  -- External call through a declared interface
  | externalCall : Ident → Ident → List (Sigma Expr) → Stmt
  -- Emit a typed event (event name + argument expressions)
  | emit        : Ident → List (Sigma Expr) → Stmt
  -- Explicit revert with error value
  | revert      : Ident → Stmt
  -- Linear type operations that are statements (consume a value)
  | lockAcquire : Ident → Stmt   -- bind acquired lock to name
  | lockRelease : Expr .lock → Stmt

/-- A single function definition inside a contract. -/
structure FunctionDef where
  name    : Ident
  kind    : FunctionKind
  params  : List (Ident × Ty)
  retTy   : Ty
  body    : Stmt
  permits : List LinearPermission

inductive FunctionKind
  | external
  | internal
  | view
  | constructor

inductive LinearPermission
  | canMint (tokenType : Ident)
  | canBurn  (tokenType : Ident)
  | canFlashBorrow

/-- A complete contract definition produced by the `contract` macro. -/
structure ContractDef where
  name      : Ident
  storage   : List (Ident × Ty × Option (Sigma Expr))  -- name, type, default
  errors    : List Ident
  events    : List (Ident × List (Ident × Ty))
  functions : List FunctionDef
  interfaces: List (Ident × Ident)  -- (varName, interfaceName) for external contracts
```

---

## Step 5 — The Semantics (`Lang/Eval.lean`)

This is `Eval.lean` from dss2024, extended for the contract domain. The key addition is `ContractM` as the execution monad and `Stmt.eval` as the big-step interpreter.

```lean
-- Lang/Eval.lean
import Lsc.Lang.AST
import Lsc.Core.Types

namespace Lsc

-- ─────────────────────────────────────────────
-- Execution State
-- ─────────────────────────────────────────────

structure TxContext where
  caller    : Address
  callvalue : UInt256
  timestamp : UInt256
  origin    : Address
  deriving Repr

/-- S is the contract-specific storage struct.
    Framework does not know its shape — it is a type parameter. -/
structure ContractState (S : Type) where
  storage : S
  context : TxContext
  locked  : Bool := false   -- reentrancy guard, framework-managed
  deriving Repr

-- ─────────────────────────────────────────────
-- Framework Error Hierarchy
-- ─────────────────────────────────────────────

inductive FrameworkError
  | Reentrant
  | Unauthorized
  | InvalidSelector
  deriving Repr, DecidableEq

/-- Every user error type gets a generated instance mapping ArithError and
    FrameworkError variants declared in the contract errors: block. -/
class ContractErrors (Err : Type) where
  arith         : ArithError → Err
  fromFramework : FrameworkError → Err

/-- Panic arm for ArithError cases statically unreachable in a validated contract.
    Codegen emits this for undeclared cases; the validator proves the arms are dead. -/
def ContractErrors.unreachableArith [ContractErrors Err] (ae : ArithError) : Err :=
  panic s!"unreachable ArithError {repr ae}"

-- ─────────────────────────────────────────────
-- The ContractM Monad
-- ─────────────────────────────────────────────

/-- The contract execution monad.
    S   = storage type (contract-specific struct)
    E   = event type   (contract-specific inductive)
    Err = error type   (contract-specific inductive, embeds FrameworkError)
    A   = return value type

    Returns: error | (value, new state, emitted events)
    Events are implicit in source syntax, explicit in Lean proofs. -/
def ContractM (S E Err : Type) (A : Type) : Type :=
  ContractState S → Except Err (A × ContractState S × List E)

namespace ContractM

-- ── Monad instances ──────────────────────────

instance : Monad (ContractM S E Err) where
  pure a := fun s => .ok (a, s, [])
  bind m f := fun s =>
    match m s with
    | .error e => .error e
    | .ok (a, s', log1) =>
      match f a s' with
      | .error e => .error e
      | .ok (b, s'', log2) => .ok (b, s'', log1 ++ log2)

-- ── Primitives ───────────────────────────────

def get : ContractM S E Err (ContractState S) :=
  fun s => .ok (s, s, [])

def set (s' : ContractState S) : ContractM S E Err Unit :=
  fun _ => .ok ((), s', [])

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

/-- Lift `Except ArithError` into `ContractM` at @math call boundaries.
    Uses the same `ContractErrors.arith` map as `+?`. Surface syntax: `|>.orRevert`. -/
def Except.orRevertArith [ContractErrors Err] {A} (x : Except ArithError A) : ContractM S E Err A :=
  match x with
  | .ok a => pure a
  | .error ae => revertArith ae

def require [ContractErrors Err] (cond : Bool) (err : Err)
    : ContractM S E Err Unit :=
  if cond then pure () else revertUser err

def caller : ContractM S E Err Address :=
  fun s => .ok (s.context.caller, s, [])

def callvalue : ContractM S E Err UInt256 :=
  fun s => .ok (s.context.callvalue, s, [])

def timestamp : ContractM S E Err UInt256 :=
  fun s => .ok (s.context.timestamp, s, [])

-- ── simp lemmas ──────────────────────────────
-- These are REQUIRED. Without them, proofs cannot be closed by simp.
-- Every primitive above must have a corresponding @[simp] lemma.

@[simp]
theorem runS_pure (a : A) (s : ContractState S) :
    (pure a : ContractM S E Err A) s = .ok (a, s, []) := rfl

@[simp]
theorem runS_bind_ok (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s : ContractState S) (a : A) (s' : ContractState S) (log : List E)
    (h : m s = .ok (a, s', log)) :
    (m >>= f) s = (f a s').map fun (b, s'', log2) => (b, s'', log ++ log2) := by
  simp [bind, h]

@[simp]
theorem runS_bind_err (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s : ContractState S) (e : Err) (h : m s = .error e) :
    (m >>= f) s = .error e := by
  simp [bind, h]

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
theorem runS_require_true [ContractErrors Err] (err : Err) (s : ContractState S) :
    (require true err : ContractM S E Err Unit) s = .ok ((), s, []) := rfl

@[simp]
theorem runS_require_false [ContractErrors Err] (err : Err) (s : ContractState S) :
    (require false err : ContractM S E Err Unit) s = .error err := rfl

@[simp]
theorem runS_caller (s : ContractState S) :
    (caller : ContractM S E Err Address) s = .ok (s.context.caller, s, []) := rfl

end ContractM

-- ─────────────────────────────────────────────
-- runS: top-level execution helper for proofs
-- ─────────────────────────────────────────────

/-- Run a ContractM action from an initial state.
    All user theorems use runS in their hypotheses. -/
def runS (m : ContractM S E Err A) (s : ContractState S) :
    Except Err (A × ContractState S × List E) :=
  m s

-- ─────────────────────────────────────────────
-- Expr evaluation
-- ─────────────────────────────────────────────

/-- Environment for local variables (analogous to dss2024's Env). -/
structure LocalEnv where
  get : Ident → Option (Sigma (fun _ : Ty => UInt256))  -- simplified: all values as UInt256
deriving Inhabited

/-- Evaluate a typed expression in a local environment and contract state.
    Requires [ContractErrors Err] — satisfied by the per-contract generated instance. -/
def Expr.eval {t : Ty} [ContractErrors Err] (e : Expr t) (env : LocalEnv) : ContractM S E Err UInt256 :=
  match e with
  | .litU256 n => pure n
  | .litBool b => pure (if b then 1 else 0)
  | .litAddr a => pure a
  | .var name  => match env.get name with
    | some ⟨_, v⟩ => pure v
    | none => ContractM.revert .Unauthorized  -- unbound variable: compiler bug
  | .caller    => ContractM.caller
  | .callvalue => ContractM.callvalue
  | .timestamp => ContractM.timestamp
  | .weiAddChecked a b => do
    let va ← a.eval env; let vb ← b.eval env
    match Wei.addChecked ⟨va⟩ ⟨vb⟩ with
    | .error ae => ContractM.revertArith ae
    | .ok r    => pure r.raw
  | .wadAddChecked a b => do
    let va ← a.eval env; let vb ← b.eval env
    match Wad.addChecked ⟨va⟩ ⟨vb⟩ with
    | .error ae => ContractM.revertArith ae
    | .ok r    => pure r.raw
  | .wadMulHalfUp a b => do
    let va ← a.eval env; let vb ← b.eval env
    match Wad.mulHalfUp ⟨va⟩ ⟨vb⟩ with
    | .error ae => ContractM.revertArith ae
    | .ok r    => pure r.raw
  -- ... (other cases follow the same pattern)
  | _ => ContractM.revert .Unauthorized

-- ─────────────────────────────────────────────
-- Stmt evaluation  (the key function)
-- ─────────────────────────────────────────────

/-- Evaluate a statement. This is the semantic core.
    It is definitionally equal to what macro-expanded contract functions produce.
    Pattern directly mirrors dss2024's BigStep / Eval structure. -/
def Stmt.eval (stmt : Stmt) (env : LocalEnv)
    : ContractM S E Err LocalEnv :=
  match stmt with
  | .skip => pure env
  | .seq s1 s2 => do
    let env' ← s1.eval env
    s2.eval env'
  | .letBind name expr => do
    let v ← expr.eval env
    pure { env with get := fun n => if n == name then some ⟨.uint256, v⟩ else env.get n }
  | .storageSet field expr => do
    -- field access is done via a generated projection function
    -- this is resolved during elaboration; here we record it symbolically
    let v ← expr.eval env
    ContractM.modifyStorage (fun s => s)  -- TODO: resolve field write via reflection
    pure env
  | .require condExpr errName => do
    let v ← condExpr.eval env
    if v != 0 then pure env
    else ContractM.revertUser (sorry)  -- errName resolved during elaboration
  | .ifThenElse cond thn els => do
    let v ← cond.eval env
    if v != 0 then thn.eval env else els.eval env
  | .emit eventName args => do
    -- event construction resolved during elaboration
    pure env  -- TODO: emit the typed event
  | .revert errName =>
    ContractM.revertUser sorry  -- errName resolved during elaboration
  | _ => pure env  -- TODO: remaining cases
```

**Important note on `storageSet` and `revert` with `sorry`**: the `Stmt.eval` function as written is parametric over `S` and `Err`, so it cannot directly write `$.reserve0 := v` — it doesn't know the shape of `S`. The resolution is that the `contract` macro generates a **specialized `eval`** for each contract where `S`, `E`, and `Err` are known concrete types. The generic `Stmt.eval` above is a specification; the macro generates the concrete version. See Step 7.

### `@[simp]` bridge lemmas (required for proof ergonomics)

```lean
-- UInt256.addCheckedNat — framework-internal; used by Wei.addCheckedNat only
@[simp] theorem UInt256.addCheckedNat_ok ...

-- Wei checked (+? on Wei-typed storage/vars)
@[simp] theorem Wei.addCheckedNat_ok (a : Wei) (n : Nat) (h : a.raw.val + n < 2^256) :
    Wei.addCheckedNat a n = .ok ⟨a.raw.val + n, h⟩ := ...
@[simp] theorem Wei.addCheckedNat_error (a : Wei) (n : Nat) (h : ¬ a.raw.val + n < 2^256) :
    Wei.addCheckedNat a n = ContractM.revertArith .Overflow := ...

-- Storage ($.field)
@[simp] theorem storageGet_val (field : Ident) (s : ContractState S) :
    runS (storageGet field) s = .ok (s.storage.field, s, []) := ...
@[simp] theorem storageSet_val (field : Ident) (v : _) (s : ContractState S) :
    runS (storageSet field v) s = .ok ((), { s with storage := s.storage.setField field v }, []) := ...

-- Wad bracket-pair ops (proofs unfold ⸢*⸣? to wadMulHalfUp)
@[simp] theorem Wad.wadMulHalfUp_ok ...
@[simp] theorem Wad.wadDivDown_ok ...
```

---

## Step 6 — The `TxM` Builder Monad (`Lang/TxM.lean`) — historical intermediate step

`TxM` was itself later superseded as the contract-author surface by the current `tx { ... }`
grammar (§3.4 of DESIGN.md) — `TxM.lean` remains as the builder/combinator layer that grammar
desugars into. See
[`decisions/0001-txm-superseded-by-syntax.md`](../decisions/0001-txm-superseded-by-syntax.md) and
[`decisions/0008-syntax-and-contract-macro-migrations.md`](../decisions/0008-syntax-and-contract-macro-migrations.md)
for the full history of what was tried before this, including a deleted custom-grammar attempt.

The `TxM` implementation (`Lsc/Lang/TxM.lean`) gives `Stmt` `Append`/`EmptyCollection` instances (`Stmt.seq`/`Stmt.skip`) and defines:

```lean
abbrev TxM (α : Type) : Type := WriterT Stmt Id α
```

reusing Mathlib's `WriterT` (plain `WriterT` is no longer bundled in Lean core) rather than a hand-rolled free monad — `Monad`/`Bind`/`Pure` come for free from the `Append`/`EmptyCollection Stmt` instances, with zero effect on `Compile/Lower.lean`/`Yul.lean`/`Bytecode/*` (which only ever see the final `Stmt` value, never the monad that built it).

`TxM.run : TxM Unit → Stmt` (`Id.run (WriterT.run m) |>.2`) is the bridge back to the unchanged `Stmt`/`Compile.*` pipeline — a `do`-block written against `TxM` becomes a plain `Stmt` value exactly like a hand-written AST.

Key combinators/notations actually implemented (all in `Lang/TxM.lean`; see that file's module docstring for the full rationale, condensed here):

- **Storage reads — type-tagged, not fully generic**: `wei σ.field` / `bool σ.field` / `addr σ.field` / `u256 σ.field`, implemented as `term`-level `syntax`/`macro_rules` that pattern-match the `σ.field` dotted identifier and dispatch to `weiField`/`boolField`/`addrField`/`u256Field`. A single fully-generic `σ.field` (inferring the tag from the field's declared storage type) would need either a per-contract field-type map populated by `deriving ContractStorage`, or expected-type-directed elaboration distinguishing `Wei.Expr` from `CoreExpr .bool/.address/.uint256` — neither exists yet, so the type tag is written explicitly instead.
- **Storage writes — plain function calls, not `:=` sugar**: `setWei "field" e`, `setBool`, `setAddr`, `setU256`, each a plain `TxM Unit` value usable directly as a `do`-statement. A `<tytag> σ.field := expr` `doElem` sugar mirroring the read notation was attempted and dropped: a `doElem` syntax sharing a leading-token prefix with the *term*-level read notation produces an ambiguous `choice` parse node (since a do-element can always also be a bare term), which broke `macro_rules` pattern matching with an "unexpected do-element of kind choice" error.
- **Evaluate-once bindings — `letWei`/`letBool`/`letAddr`/`letU256`**: `let n ← letWei "n" e` emits a real `Stmt.letBind name ⟨ty, e⟩` (evaluated exactly once, at that point in the statement sequence) and returns a `var` reference safe to reuse even after later writes to fields `e` reads. This exists to avoid a real correctness bug: a *plain* Lean `let n := wei σ.number +? 1` only binds an AST *term*; if `n` is referenced again after a subsequent write to `number`, evaluation re-runs `σ.number +? 1` against the *new* (already-updated) storage, silently double-counting. `letWei`/etc. sidestep this by emitting an actual `Stmt.letBind`, evaluated once. See `TxM.lean`'s module docstring ("Plain `let` vs. `letWei`/...") for the full example.
- **`require <cond> else revert <err>` / `revert <err>`**: `doElem`-level macros expanding to `requireE`/`revertE` (`Stmt.require`/`Stmt.revert`), taking a bare error-constructor identifier (e.g. `revert Paused`) — the plan's `revert .Paused` anonymous-constructor-extraction sugar is not implemented; the bare name is used directly.
- **`emit <name> <args>`**: a plain function (`Stmt.emit`) taking the event name and a `List ExprAny` of typed argument values — auto-extracting name/args from a real event-constructor application (as the plan envisioned) is not implemented; arguments are passed explicitly.
- **`ifE (cond : CoreExpr .bool) (thn els : TxM Unit) : TxM Unit`**: contract-level branching, since a real Lean `if` needs a `Bool` known at elaboration time but the branch condition is `CoreExpr .bool` *data* evaluated later. `ifE` runs both branches through `TxM.run` (pure, since the base monad is `Id`) and wraps the result in `Stmt.ifThenElse`.
- **Checked arithmetic**: `+?`/`-?` on `Wei.Expr` (`WeiAddChecked` typeclass lets `σ.number +? 1` accept a bare `Nat`). `*?`/`/?` are **not implemented** — `Wei.Expr` has no checked-multiply/divide AST constructors yet; this is a follow-up, not a design gap.
- **Comparisons/booleans**: `===` (`CoreExpr.eqAuto`, type inferred from operands), `!` (`CoreExpr.not`).
- **`msg.sender`**: `notation "msg.sender" => CoreExpr.txField TxField.caller`.

## Step 7 — The `deriving` Handlers and `derive_contract_dsl` (`Lang/Derive.lean`)

> An earlier `contract … where` command (`Lang/Contract.lean`/`Lang/ContractGen.lean`) tried to
> synthesize a storage struct, error/event inductives, AST defs, and `ContractM` defs all from
> one parsed custom-syntax body, using hand-built raw `Syntax.node` trees. It was deleted — see
> [`decisions/0008-syntax-and-contract-macro-migrations.md`](../decisions/0008-syntax-and-contract-macro-migrations.md).
> **What was actually built**: three independent `deriving` handlers attached directly to plain
> `structure`/`inductive` declarations, plus one small assembly command — no `contract` umbrella
> command at all; a contract is just a sequence of ordinary top-level commands.

The real implementation lives in `Lsc/Lang/Derive.lean` and registers three handlers via `Lean.Elab.registerDerivingHandler`:

```lean
-- marker classes — carry no data; deriving just needs *some* declaration to resolve to
class ContractStorage where
class ContractEvent where
class ContractError where

initialize registerDerivingHandler ``ContractStorage mkContractStorageHandler
initialize registerDerivingHandler ``ContractEvent mkContractEventHandler
initialize registerDerivingHandler ``ContractError mkContractErrorHandler
```

- **`mkContractStorageHandler`**: for a storage `structure S` (rejecting parametric structures), classifies each field's type via `fieldKindOfExpr` (one of `Wei`/`Bool`/`Address`/`UInt256`, distinguished from the *unreduced* projection type — see §3.3 of `DESIGN.md` for why this works without `whnf`), then emits `S.getField (t : Ty) (field : String) (s : S) : Option (Val t)` and `S.setField (t : Ty) (field : String) (v : Val t) (s : S) : S`, each a `match` with one arm per field plus a `none`/identity default arm. Both are generated as plain top-level `command`s via `elabCommand`, run at the root namespace (`atRootNamespace`) so fully-qualified names like `S.getField` land exactly where expected even if `deriving` runs inside a user `namespace`.
- **`mkContractEventHandler`**: for an event `inductive E` (rejecting parametric/recursive inductives), classifies each constructor's 0-or-1 parameter (rejecting >1-parameter constructors — multi-param events aren't supported downstream yet) and emits `E.buildEvent (name : String) (vals : List (Sigma Val)) : Option E`.
- **`mkContractErrorHandler`**: for an error `inductive Err` (rejecting parametric inductives and any constructor with parameters — error constructors must be nullary), emits `instance : Inhabited Err` (defaulting to the first declared constructor, needed by `ContractErrors.unreachableArith`), `Err.resolveError (name : String) : Option Err`, and `instance : ContractErrors Err` whose `arith` arm name-matches against `arithErrorCtorNames := #["Overflow", "Underflow", "DivisionByZero"]` (falling back to `ContractErrors.unreachableArith` for unmatched cases) and whose `fromFramework` arm maps every case to one fixed fallback constructor (preferring a same-named match against `frameworkErrorCtorNames := #["Reentrant", "Unauthorized", "InvalidSelector"]`, else the first declared `Err` constructor) — mirroring exactly what `Counter.lean`'s hand-written instance already does.

```lean
elab "derive_contract_dsl " storageId:ident errId:ident eventId:ident : command => do
  ...
  -- resolves each ident to its fully-qualified Name, builds `S.getField`/`S.setField`/
  -- `Err.resolveError`/`E.buildEvent` as single fully-qualified identifiers, and emits:
  @[reducible] instance : Lsc.ContractDSL S E Err where
    getField   := S.getField
    setField   := S.setField
    resolveErr := Err.resolveError
    buildEvent := E.buildEvent
```

(`derive_contract_dsl` resolves each identifier via `Lean.Elab.realizeGlobalConstNoOverloadWithInfo` rather than naively splicing `$storageId.getField`, since the latter either parses as one wrong dotted antiquotation, or — if parenthesized — as a value-level field projection on the *type* `S` denotes, neither of which is the intended namespaced-constant reference.)

What is **not** implemented relative to the original plan: there is no source-position-attached error reporting (`Lean.logErrorAt`) for `deriving`-time failures — they're plain `throwError` calls, which Lean still attaches to the `deriving` clause's position by default, but there's no bespoke positioning logic. There is also no generic, declaration-agnostic codegen path (`generateStorageStruct`, etc., from the historical plan below) — the storage/error/event *declarations themselves* are written directly by the contract author as plain Lean, never generated; only the glue (`getField`/`setField`/`resolveError`/`buildEvent`/`ContractDSL` instance) is generated.

One idea from that deleted approach is worth keeping in mind even though the command itself is
gone: the **definitional equality trick** — defining a function like `Counter.increment` as
literally `Stmt.eval Counter.increment.ast` makes `Counter.increment = Stmt.eval
Counter.increment.ast` hold by `rfl`, so proofs about the function and proofs about its AST are
interchangeable without extra proof effort. The current `deriving`/`tx` pipeline preserves this
property.

## Step 8 — Validation Passes (`Lang/Checks.lean`)

> **Update**: the real `Lsc/Lang/Checks.lean` implements these checks (the sketch below was largely accurate in spirit) but returns `Option String`/`Except String ContractDef`, not `List (Syntax × String)` — there is no source-position attribution yet, since there's no parser producing `Syntax` positions to attribute to (contract bodies are plain elaborated Lean terms). `checkArithErrorCoverage` in particular is fully implemented (not a `sorry`): `arithErrorsByFunction` walks every function body and storage initializer via `visitStmt`/`visitExpr`/`visitWeiExpr`, collects reachable `ArithError`s per function, and `checkArithErrorCoverage` cross-checks each against `c.errors` (the error-constructor-name list), matching the `arithErrorName`/`arithErrorCtorNames` convention `Lang/Derive.lean` uses. `validateAll` runs `checkNoCycles → checkLinear → checkSelectorCollisions → checkNoUInt256Arithmetic → checkArithErrorCoverage` in sequence and is wired into `Compile.contractToBytecode`/`deployToBytecode` (`Lsc/Compile/Bytecode/Contract.lean`). `checkLinear` remains a no-op stub, as originally planned. `checkNoCycles`'s premise (a call graph built from `Stmt.call` nodes) is itself stale relative to the current AST, which has no `call`/`externalCall` `Stmt` constructor yet (see DESIGN.md §6) — so this pass currently has no real graph to check. The sketch below documents the original per-pass design (mostly still accurate for the other passes); only the return-type/position-reporting details and the `checkNoCycles` premise above changed.

Three passes, run in order, plus typed-arithmetic and arith-error coverage. Each returns `List (Syntax × String)` (position, message) for error reporting.

```lean
-- Lang/Checks.lean
import Lsc.Lang.AST

namespace Lsc.Checks

-- ── Pass 1: DAG check (no recursion) ─────────

/-- Build the call graph from all function bodies.
    Returns .error if any cycle is found. -/
def buildCallGraph (fns : List FunctionDef) : Except (List String) (Finmap Ident (List Ident)) :=
  sorry -- standard DFS cycle detection over Stmt.call nodes

/-- Validate: the call graph is a DAG. -/
def checkNoCycles (c : ContractDef) : Option String :=
  match buildCallGraph c.functions with
  | .error cycle => some s!"Recursive call cycle detected: {cycle}"
  | .ok _ => none

-- ── Pass 2: Linearity check ───────────────────

/-- For each function, verify that every linear-typed variable is
    used exactly once on every execution path.
    Algorithm: track a set of "outstanding" linear vars.
    At every branch, both branches must consume the same set.
    At return, outstanding must be empty. -/
structure LinearCtx where
  outstanding : Finset Ident   -- linear vars that must still be consumed
  consumed    : Finset Ident   -- linear vars already consumed

inductive LinearError
  | DroppedVar   (name : Ident)  -- linear var not consumed on some path
  | DuplicateUse (name : Ident)  -- linear var consumed more than once
  | UnpermittedMint (fn : Ident) -- mint called without canMint permission
  | UnpermittedBurn (fn : Ident)

def checkLinear (fn : FunctionDef) : List LinearError :=
  sorry -- walk Stmt, track LinearCtx

-- ── Pass 3: Selector collision check ─────────

/-- ABI selector = first 4 bytes of keccak256(signature).
    Computed from function name and parameter types. -/
def computeSelector (fn : FunctionDef) : UInt32 :=
  sorry -- keccak256 of "name(type1,type2,...)[0:4]"

def checkSelectorCollisions (fns : List FunctionDef) : Option String :=
  let selectors := fns.filter (·.kind == .external) |>.map computeSelector
  let unique := selectors.eraseDups
  if unique.length < selectors.length
  then some "Selector collision detected between external functions"
  else none

-- ── Pass 4: No bare UInt256 arithmetic ────────

/-- Reject weiAddChecked/wadAddChecked/… nodes where either operand is typed
    as UInt256. UInt256 may be compared (`<`, `≤`, `==`) but never added,
    subtracted, multiplied, or divided in contract bodies. -/
def checkNoUInt256Arithmetic (c : ContractDef) : List (Syntax × String) :=
  sorry

-- ── Pass 5: Arith error coverage (strict 1:1) ─

/-- For each ArithError case reachable from checked ops in the contract body,
    require a same-named variant in errors: (Overflow, Underflow, DivByZero).
    Reject collapsing maps. Reject -? if Underflow not declared, etc. -/
def checkArithErrorCoverage (c : ContractDef) : List (Syntax × String) :=
  sorry

-- ── Combined validator ────────────────────────

def validateAll (c : ContractDef) : Except (List (Syntax × String)) ContractDef :=
  let errors : List (Syntax × String) := []
  -- Pass 1: checkNoCycles
  -- Pass 2: checkLinear (per function)
  -- Pass 3: checkSelectorCollisions
  -- Pass 4: checkNoUInt256Arithmetic
  -- Pass 5: checkArithErrorCoverage — reachable ArithError case must have
  --         same-named variant in errors:; reject collapsing maps
  -- collect all errors, report with positions
  -- return .ok c if no errors
  sorry

end Lsc.Checks
```

---

## Step 9 — Delaborators (`Lang/Delab.lean`) — NOT IMPLEMENTED

`Lang/Delab.lean` was never written, and is not currently planned. There **is** a live custom grammar again today (the `tx { ... }` `lscExpr`/`lscStmt` categories in the current `Lang/Syntax.lean`, §3.4 of DESIGN.md), but no delaborator exists for it: it only ever produces a plain `def name : Stmt := ...`, and once elaborated, contract bodies are ordinary `Stmt` values, which Lean's own pretty printer already displays reasonably (a `Stmt` value still prints as raw `Stmt.seq (Stmt.require ...) ...` when unfolded in a proof goal, but proofs in practice `simp` straight through to a final concrete state rather than displaying intermediate `Stmt` trees — see `CounterTheorem.lean`). The sketch below is preserved for historical context only, in case bespoke pretty-printing for `Stmt`/`Expr` values, or for `tx { ... }` syntax itself, becomes worth adding later.

```lean
-- Lang/Delab.lean
-- Pattern mirrors dss2024/Delab.lean exactly.
-- Register one delaborator per Expr/Stmt constructor.

import Lean.PrettyPrinter.Delaborator
import Lsc.Lang.AST
import Lsc.Lang.Syntax

open Lean PrettyPrinter Delaborator SubExpr

namespace Lsc

-- Helper: annotate with source info for IDE hover
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

-- Expr delaborator
partial def delabExprInner : DelabM (TSyntax `lsc_expr) := do
  let e ← getExpr
  let stx ← match_expr e with
    | Expr.litU256 n => do
      let n' ← withAppArg delab
      pure ⟨n'.raw⟩
    | Expr.litBool b =>
      if b then `(lsc_expr| true) else `(lsc_expr| false)
    | Expr.var s =>
      match s with
      | .lit (.strVal name) =>
        let i := mkIdent (.mkSimple name)
        `(lsc_expr| $i:ident)
      | _ => failure
    | Expr.caller    => `(lsc_expr| msg.sender)
    | Expr.callvalue => `(lsc_expr| msg.value)
    | Expr.weiAddChecked _ _ =>
      let a ← withAppFn <| withAppArg delabExprInner
      let b ← withAppArg delabExprInner
      `(lsc_expr| $a +? $b)
    | Expr.storageGet _ =>
      let f ← withAppArg delab
      `(lsc_expr| $. $f:ident)
    | Expr.not _ =>
      let e ← withAppArg delabExprInner
      `(lsc_expr| ! $e)
    | _ => failure
  annAsTerm stx

@[delab app.Lsc.Expr.litU256, delab app.Lsc.Expr.var,
  delab app.Lsc.Expr.caller,   delab app.Lsc.Expr.weiAddChecked,
  delab app.Lsc.Expr.not]
partial def delabExpr : Delab := do
  guard <| match_expr ← getExpr with
    | Expr.litU256 _         => true
    | Expr.var _             => true
    | Expr.caller            => true
    | Expr.weiAddChecked _ _ => true
    | Expr.not _             => true
    | _                      => false
  `(term| lsc_expr { $(⟨← delabExprInner⟩) })

-- Stmt delaborator (same pattern, omitted for brevity — follow dss2024 exactly)

end Lsc
```

---

## Step 10 — IR and Yul Emission (`Compile/`)

```lean
-- Compile/IR.lean

namespace Lsc.IR

/-- Flat IR. Linear types erased. Storage accesses resolved to slots.
    One IR constructor per lowered operation. -/
inductive Expr
  | lit    : UInt256 → Expr
  | slot   : UInt256 → Expr          -- sload(slot)
  | mapSlot: UInt256 → Expr → Expr   -- keccak256(key ++ baseSlot)
  | add    : Expr → Expr → Expr
  | sub    : Expr → Expr → Expr
  | mul    : Expr → Expr → Expr
  | div    : Expr → Expr → Expr
  | lt     : Expr → Expr → Expr
  | eq     : Expr → Expr → Expr
  | caller : Expr
  | value  : Expr

inductive Stmt
  | sstore  : UInt256 → Expr → Stmt       -- slot, value
  | msstore : UInt256 → Expr → Expr → Stmt -- mapping base slot, key, value
  | if_     : Expr → Stmt → Stmt → Stmt
  | seq     : Stmt → Stmt → Stmt
  | revert  : Expr → Expr → Stmt          -- offset, length
  | log     : List Expr → Expr → Stmt     -- topics, data
  | checkFlag : UInt256 → Stmt            -- revert if slot != 0 (reentrancy)
  | setFlag   : UInt256 → Bool → Stmt

end Lsc.IR
```

```lean
-- Compile/Yul.lean
-- Emit EvmYulLean's Yul.Program type directly (not a string).
-- This allows #eval to run EvmYulLean's interpreter on the output.
-- Import EvmYulLean here.

import EvmYulLean.Yul.AST  -- adjust to actual EvmYulLean import path
import Lsc.Compile.IR

namespace Lsc.Compile

/-- Lower IR.Stmt to a Yul.Statement (EvmYulLean type).
    One IR construct → one or more Yul constructs.
    This function is currently TRUSTED, not proved. Tested via conformance suite. -/
def IR.Stmt.toYul (s : IR.Stmt) : Yul.Statement :=
  match s with
  | .sstore slot val =>
    Yul.Statement.expression
      (Yul.Expression.functionCall "sstore"
        [Yul.Expression.literal (Yul.Literal.number slot),
         val.toYul])
  | .if_ cond thn els =>
    Yul.Statement.if_ cond.toYul [thn.toYul] -- Yul if has no else; desugar
  | .revert offset len =>
    Yul.Statement.expression
      (Yul.Expression.functionCall "revert" [offset.toYul, len.toYul])
  | .checkFlag slot =>
    -- if sload(slot) { revert(0,0) }
    Yul.Statement.if_
      (Yul.Expression.functionCall "sload"
        [Yul.Expression.literal (Yul.Literal.number slot)])
      [Yul.Statement.expression
        (Yul.Expression.functionCall "revert"
          [Yul.Expression.literal (Yul.Literal.number 0),
           Yul.Expression.literal (Yul.Literal.number 0)])]
  | _ => sorry -- complete remaining cases

/-- Top-level: lower a full contract to a Yul.Object. -/
def contractToYul (c : ContractDef) : Yul.Object :=
  sorry

end Lsc.Compile
```

---

## Step 11 — The Counter Reference Contract

> **Update**: `examples/counter/src/Counter.lean` (+ `examples/counter/test/CounterTheorem.lean`) is the real, current version of this step, written with the `tx { ... }` grammar + `derive_contract`/`deriving` as described in §3.4/§7 above, with all 10 required theorems (§13/`reference/COUNTER.md`) proved with **zero `sorry`s**. An earlier hand-written version of this contract (with `getField`/`setField`/etc. written by hand instead of `deriving`-generated) was kept alongside it for a while as a "what the framework expands to" reference — proof burden between the two was essentially identical (both closed with `simp` + `omega` in a handful of lines), confirming the redesign didn't regress provability — and was later removed once the new approach became the sole reference. The sketch below (using the old `contract Counter where` syntax) is preserved for historical context only; see `Counter.lean` for the real, current contract and `reference/COUNTER.md` for the up-to-date theorem table.

Write this before any other contract. If this contract cannot be proved, something in the framework is wrong.

```lean
-- Examples/Counter.lean
import Lsc.Lang.Contract
import Lsc.Lang.Eval

namespace Lsc.Examples

-- ── Contract definition ───────────────────────

contract Counter where
  storage:
    number : Wei := 0
    paused : Bool    := false
    owner  : Address

  errors:
    | Paused
    | NotOwner
    | Overflow

  events:
    | Incremented (n : Wei)
    | Paused
    | Unpaused

  def increment : Tx := do
    require (!$.paused) else revert Paused;
    let n ← $.number +? 1;
    $.number := n;
    emit Incremented(n);

  def pause : Tx := do
    require (msg.sender == $.owner) else revert NotOwner;
    require (!$.paused) else revert Paused;
    $.paused := true;
    emit Paused();

  def unpause : Tx := do
    require (msg.sender == $.owner) else revert NotOwner;
    require ($.paused) else revert Paused;
    $.paused := false;
    emit Unpaused();

-- ── Proofs ────────────────────────────────────
-- These theorems are the acceptance test for the framework.
-- Every one must be provable by simp + omega + at most 5 lines.
-- If any requires more, fix the simp lemma set first.

-- Success case: number increases by 1
theorem Counter.increment_increases_number
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : s.storage.paused = false)
    (h : runS Counter.increment s = .ok ((), s', log)) :
    s'.storage.number.raw = s.storage.number.raw + 1 := by
  simp [Counter.increment, runS, Stmt.eval, storageGet, storageSet,
        Wei.addCheckedNat, ContractM.require,
        ContractM.modifyStorage, hpaused] at h
  omega

-- Failure case: reverts when paused
theorem Counter.increment_reverts_when_paused
    (s : ContractState CounterStorage)
    (hpaused : s.storage.paused = true) :
    (runS Counter.increment s).isError := by
  simp [Counter.increment, runS, Stmt.eval, ContractM.require, hpaused]

-- Field independence: increment does not change paused
theorem Counter.increment_preserves_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (h : runS Counter.increment s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused := by
  simp [Counter.increment, runS, Stmt.eval, ContractM.modifyStorage] at h
  -- follows from struct update only touching `number`
  rfl

-- Event: emits exactly Incremented with new value
theorem Counter.increment_emits_incremented
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : s.storage.paused = false)
    (h : runS Counter.increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := by
  simp [Counter.increment, runS, Stmt.eval, ContractM.emit, hpaused] at h
  exact h.2

-- Access control: pause reverts for non-owner
theorem Counter.pause_reverts_for_non_owner
    (s : ContractState CounterStorage)
    (howner : s.context.caller ≠ s.storage.owner) :
    (runS Counter.pause s).isError := by
  simp [Counter.pause, runS, Stmt.eval, ContractM.require,
        ContractM.caller, howner]

end Lsc.Examples
```

---

## Step 12 — Key Implementation Decisions

> **Update**: both sub-sections below describe the *originally planned* mechanism (a `contract` macro generating a per-contract `setField`/specialized `Stmt.eval`, and macro-time resolution of error names to concrete constructors). The actual mechanism is `deriving ContractStorage`/`deriving ContractError` generating `S.getField`/`S.setField`/`Err.resolveError` (§7 above), referenced generically through the `ContractDSL S E Err` typeclass that `Lang/Eval.lean`'s `Stmt.eval`/`Expr.eval` are written against (so `Stmt.eval` itself stays fully generic over `S`/`E`/`Err` — it does not need a per-contract specialized version at all, since `getField`/`setField`/`resolveErr`/`buildEvent` are resolved via `[ContractDSL S E Err]` instance lookup, satisfied by whatever `derive_contract_dsl` generated). Error names remain plain `String` values resolved at `Stmt.eval` time via `Err.resolveError`, not pre-resolved to concrete constructors at macro-expansion time as originally sketched. The historical sketches below are preserved for context only.

### How `storageSet` works without knowing `S`

The generic `Stmt.eval` cannot write `s.reserve0 := v` because it doesn't know `S`. Resolution: the `contract` macro generates a **storage accessor table** for each contract:

```lean
-- generated by macro for Counter:
def CounterStorage.setField (field : Ident) (v : Wei)
    (s : CounterStorage) : CounterStorage :=
  match field with
  | "number" => { s with number := v }
  | "paused" => { s with paused := v != 0 }
  | _        => s  -- unreachable; validated at elab time

-- then Stmt.eval for Counter is specialized:
def Counter.Stmt.eval (stmt : Stmt) (env : LocalEnv)
    : ContractM CounterStorage CounterEvent CounterError LocalEnv :=
  match stmt with
  | .storageSet field expr => do
    let v ← Expr.eval expr env
    ContractM.modifyStorage (CounterStorage.setField field v)
    pure env
  | _ => Stmt.eval stmt env  -- delegate to generic for other cases
```

The macro generates `setField` for every contract. This is boilerplate but it is **definitionally transparent** — Lean unfolds it automatically, so proofs still close by `rfl` or `simp`.

### How error names are resolved

`Stmt.revert "Paused"` stores the error as a string. During macro expansion, the contract's error inductive is known, so the macro can substitute the actual constructor:

```lean
-- in macro_rules, when inside a `contract Counter` body:
| `(lsc_stmt| revert $err;) =>
    -- err is known to be a CounterError constructor
    `(Stmt.revertUser CounterError.$(mkIdent err.getId))
```

This means by the time `Stmt.eval` runs, all error names are resolved to concrete inductive constructors — no string lookup at runtime.

### Yul emission via `#eval`

```lean
-- User writes this to generate Yul:
#eval Counter.toYul.render  -- prints Yul source string

-- Or to get the structured Yul.Program for EvmYulLean:
#eval Counter.toYul  -- prints the Yul.Program value

-- To generate ABI:
#eval Counter.toABI  -- prints ABI JSON string
```

`Counter.toYul` is generated by the macro as `Compile.contractToYul Counter.contractDef`. No separate build step.

### Proof strategy for LLM assistance

When asking an LLM to write proofs:
1. Always provide the full definitions of the relevant functions
2. Always provide the relevant `@[simp]` lemmas
3. State clearly whether you want a `simp`-based proof or a structured proof
4. If the LLM's proof uses `sorry`, ask it to complete those cases explicitly

The typical proof shape for a success theorem:

```lean
theorem foo_does_X (s s' : ContractState FooStorage) (log) (h : runS foo s = .ok (...)) :
    postcondition s' := by
  -- unfold everything
  simp [foo, runS, Stmt.eval, ContractM.require, ContractM.modifyStorage,
        FooStorage.setField, ...] at h
  -- h is now a conjunction of equalities about s'
  -- close with omega for arithmetic, rfl for structural
  omega
```

---

## Dependency Order for Implementation

> **This reflects the real build order** (see `Lsc/Prelude.lean`'s import list and `examples/counter/lakefile.lean`'s dependency on the `Lsc` library) rather than the original plan's order — most notably, the syntax/codegen step is `Lang/TxM.lean` + `Lang/Derive.lean` + the current `Lang/Syntax.lean` (no `Contract.lean`/`Delab.lean`), and `Compile/` includes a `Bytecode/*` subtree (direct EVM opcode emission) alongside `Yul.lean`.

```
1.  Core/UInt256.lean, Types.lean, Arithmetic.lean   -- no dependencies
2.  Core/ContractM.lean       -- depends on Core/UInt256, Types
3.  Lib/Wei.lean (+ Wei/{Eval,Optimize,Syntax}.lean), Lib/Wad.lean, Lib/Ray.lean
                              -- depends on Core
4.  Lib/Linear/TokenAmount.lean -- depends on Core, Lib/Wei (stub)
5.  Lang/AST.lean             -- depends on Core, Lib
6.  Lang/Eval.lean            -- depends on AST
7.  Lang/Checks.lean          -- depends on AST, Selectors
8.  Lang/TxM.lean             -- depends on AST, Lib/Wei/Syntax, Lean macro system
                              --   (replaces the deleted Lang/Syntax.lean)
9.  Lang/Derive.lean          -- depends on Core/ContractM, AST, Lean deriving-handler API
                              --   (replaces the deleted Lang/Contract.lean + ContractGen.lean;
                              --   no Lang/Delab.lean — never implemented, see Step 9)
10. examples/counter/src/Counter.lean      -- depends on TxM, Derive, Prelude/Compile
    ← STOP HERE AND PROVE ALL COUNTER THEOREMS (Counter.lean) ←
11. Compile/IR.lean (+ IR/{Eval,EvalLemmas,FreeVars}.lean, IR/Opt/*)  -- depends on AST
12. Compile/Lower.lean        -- depends on IR, AST
13. Compile/Yul.lean          -- depends on IR, EvmYulLean
14. Compile/Bytecode.lean (+ Bytecode/{Instr,Codegen,Encode,Contract}.lean)
                              -- depends on IR, Checks, Selectors, EvmYul.Operations
15. Compile/Correctness.lean  -- depends on IR/Lower (kernel-checked correctness lemmas)
16. (AMM / World model)       -- not yet implemented; remains a future step
```

Do not move on from step 10 until all counter theorems pass for `Counter.lean`. The counter proofs are the acceptance test for the entire framework.

---

## Future extensions (documentation only)

These are specified in `extensions/` but not covered by implementation steps above:

| Extension | Doc | Implementation hook |
|-----------|-----|---------------------|
| Field decorators | [TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md) | `Lang/Contract.lean` elaboration |
| `@math` / ℝ specs | [MATH.md](../extensions/MATH.md) | `@math` attribute + `Spec.lean` generation |
| `contract_spec` | [CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md) | Optional macro alongside `contract` |
| Linear type details | [extensions/linear-types/](../extensions/linear-types/) | `Core/LinearTypes.lean`, `Lang/Checks.lean` |

---

## Appendix — What dss2024 Does That We Copy Directly

> **Update**: the `Syntax.lean`/`Delab.lean` rows below describe the *original* plan, which was implemented and then deleted (§6, §9). They're kept here for historical traceability, not as a description of current files.

| dss2024 file    | What it does                          | Our equivalent (original plan, since deleted) |
|-----------------|---------------------------------------|-----------------------------|
| `Syntax.lean`   | `declare_syntax_cat` + `macro_rules`  | `Lang/Syntax.lean` — deleted; superseded by `Lang/TxM.lean` (a builder monad + small notations, not a custom grammar) |
| `Eval.lean`     | `Env`, `eval`, `@[simp]` lemmas       | `Lang/Eval.lean` — unchanged, still current |
| `Delab.lean`    | `@[delab]` for pretty printing        | `Lang/Delab.lean` — never implemented (not needed without a custom grammar) |
| `Optimize.lean` | Transform + correctness theorem       | `Compile/Lower.lean`, `Compile/IR/Opt/*.lean` — current |
| `BigStep.lean`  | Relational semantics for proofs       | User theorem files — current |

The core pattern from dss2024 that we still inherit at the `AST.lean`/`Eval.lean` layer: **AST data → separate eval function → proofs about eval**. What changed is how the AST data gets built in the first place — not via a custom-grammar macro anymore, but via plain Lean `do`-notation over `TxM` (§6) plus `deriving`-generated glue (§7). The eval function (`Stmt.eval`) remains the single source of truth for semantics, and all proofs are still about `Stmt.eval`/`runS`, exactly as before.