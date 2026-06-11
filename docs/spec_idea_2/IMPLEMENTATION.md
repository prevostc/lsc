# Implementation Guide

> **Read DESIGN.md first.** This document covers *how* to build what DESIGN.md specifies.
> It is structured as an ordered sequence of implementation steps, each building on the last.
> Code samples are complete enough to compile; they are starting points, not pseudocode.
> The primary inspiration is the dss2024 Imp language by javra:
> `Syntax.lean`, `Eval.lean`, `Delab.lean`, `Optimize.lean`, `BigStep.lean`.

---

## Module Structure

```
Lsc/
  Core/
    Types.lean          -- UInt256, Address, Word, Ty
    Arithmetic.lean     -- UInt256 ops, Wad, Ray
    Mapping.lean        -- opaque Mapping k v backed by Finmap
    LinearTypes.lean    -- TokenAmount, FlashLoanReceipt, etc.
  Lang/
    AST.lean            -- Expr, Stmt inductives
    Syntax.lean         -- declare_syntax_cat + macro_rules  (← dss2024 pattern)
    Delab.lean          -- delaborators for pretty-printing   (← dss2024 pattern)
    Eval.lean           -- ContractM, Stmt.eval               (← dss2024 pattern)
    Checks.lean         -- linearity pass, DAG pass, selector check
  Compile/
    IR.lean             -- IR inductive
    Lower.lean          -- AST → IR
    Yul.lean            -- IR → Yul.Program (EvmYulLean type)
    ABI.lean            -- FunctionDef → ABI JSON string
  World/
    World.lean          -- WorldSpec typeclass, HonestWorld
    Interfaces.lean     -- IERC20, IOracle, etc.
  Contract/
    Contract.lean       -- ContractDef, elaboration entry point
  Examples/
    Counter.lean        -- pausable counter (reference)
    AMM.lean            -- constant product AMM (target)
```

Each file imports only what is below it in this list. No circular imports.

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

/-- Checked add: fails on overflow. The proof obligation at call sites is
    that on .ok, result = a + b and no overflow occurred. -/
def addChecked (a b : UInt256) : Except ArithError UInt256 :=
  -- BitVec addition wraps; detect overflow by checking result < a
  let r := a + b
  if r < a then .error .Overflow else .ok r

/-- Wrapping add: explicit modular arithmetic. Never fails. -/
def addWrapping (a b : UInt256) : UInt256 := a + b

/-- Checked sub: fails on underflow (a < b). -/
def subChecked (a b : UInt256) : Except ArithError UInt256 :=
  if a < b then .error .Underflow else .ok (a - b)

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

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

structure Ray where
  raw : UInt256
  deriving Repr, DecidableEq

namespace Wad

def mul (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw b.raw WAD).map Wad.mk

def div (a b : Wad) : Except ArithError Wad :=
  (UInt256.mulDiv a.raw WAD b.raw).map Wad.mk

def add (a b : Wad) : Except ArithError Wad :=
  (UInt256.addChecked a.raw b.raw).map Wad.mk

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
    This prevents gas-griefing bugs and simplifies proofs. -/
structure Mapping (K V : Type) [DecidableEq K] where
  inner : Finmap (fun _ : K => V)

namespace Mapping

variable {K V : Type} [DecidableEq K] [Inhabited V]

def empty : Mapping K V := ⟨Finmap.empty⟩

def get (m : Mapping K V) (k : K) : V :=
  (m.inner.lookup k).getD default

def set (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  ⟨m.inner.insert k v⟩

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
  | litBool   : Bool    → Expr .bool
  | litAddr   : Address → Expr .address
  -- Variables (by name; scope is checked during elaboration)
  | var       : Ident → Expr t
  -- Storage reads (resolved to slot during compilation)
  | storageGet : Ident → Expr t
  -- Arithmetic (all explicit about overflow behavior)
  | addChecked  : Expr .uint256 → Expr .uint256 → Expr .uint256
  | subChecked  : Expr .uint256 → Expr .uint256 → Expr .uint256
  | mulChecked  : Expr .uint256 → Expr .uint256 → Expr .uint256
  | addWrapping : Expr .uint256 → Expr .uint256 → Expr .uint256
  | mulDiv      : Expr .uint256 → Expr .uint256 → Expr .uint256 → Expr .uint256
  | wadMul      : Expr .wad    → Expr .wad    → Expr .wad
  | rayMul      : Expr .ray    → Expr .ray    → Expr .ray
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
  | tokenMint   : Expr .uint256 → Expr .tokenAmount   -- canMint permission required
  | tokenBurn   : Expr .tokenAmount → Expr .uint256   -- canBurn permission required
  | tokenSplit  : Expr .tokenAmount → Expr .uint256   -- returns pair via letBind2
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
  | ArithmeticOverflow
  | ArithmeticUnderflow
  | ArithmeticDivByZero
  | Unauthorized
  | InvalidSelector
  deriving Repr, DecidableEq

/-- Every user error type must embed framework errors.
    This ensures framework reverts are distinguishable from logic reverts. -/
class ContractErrors (Err : Type) where
  fromFramework : FrameworkError → Err

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

def revertUser (err : Err) : ContractM S E Err A :=
  fun _ => .error err

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
    Returns a value in ContractM to handle arithmetic errors. -/
def Expr.eval {t : Ty} (e : Expr t) (env : LocalEnv) : ContractM S E Err UInt256 :=
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
  | .addChecked a b => do
    let va ← a.eval env
    let vb ← b.eval env
    match UInt256.addChecked va vb with
    | .error _ => ContractM.revert .ArithmeticOverflow
    | .ok r    => pure r
  -- ... (other cases follow the same pattern)
  | _ => ContractM.revert .Unauthorized  -- TODO: complete all cases

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

**Important note on `storageSet` and `revert` with `sorry`**: the `Stmt.eval` function as written is parametric over `S` and `Err`, so it cannot directly write `s.reserve0 := v` — it doesn't know the shape of `S`. The resolution is that the `contract` macro generates a **specialized `eval`** for each contract where `S`, `E`, and `Err` are known concrete types. The generic `Stmt.eval` above is a specification; the macro generates the concrete version. See Step 7.

---

## Step 6 — Syntax Extension (`Lang/Syntax.lean`)

Follow dss2024 **exactly**: `declare_syntax_cat`, then `syntax` rules, then `macro_rules`. The macro only translates syntax to AST data — no logic, no validation.

```lean
-- Lang/Syntax.lean
import Lsc.Lang.AST
import Lean

open Lean

namespace Lsc

-- ─────────────────────────────────────────────
-- Declare syntax categories
-- ─────────────────────────────────────────────

declare_syntax_cat lsc_ty
declare_syntax_cat lsc_expr
declare_syntax_cat lsc_stmt
declare_syntax_cat lsc_field_decl
declare_syntax_cat lsc_error_decl
declare_syntax_cat lsc_event_decl
declare_syntax_cat lsc_func_decl
declare_syntax_cat lsc_contract_body

-- ─────────────────────────────────────────────
-- Type syntax
-- ─────────────────────────────────────────────

syntax "UInt256"  : lsc_ty
syntax "Bool"     : lsc_ty
syntax "Address"  : lsc_ty
syntax "Wad"      : lsc_ty
syntax "Ray"      : lsc_ty
syntax "Mapping" "(" lsc_ty "=>" lsc_ty ")" : lsc_ty

-- ─────────────────────────────────────────────
-- Expression syntax
-- ─────────────────────────────────────────────

syntax num                               : lsc_expr
syntax ident                             : lsc_expr
syntax "true"                            : lsc_expr
syntax "false"                           : lsc_expr
syntax "msg.sender"                      : lsc_expr
syntax "msg.value"                       : lsc_expr
syntax "block.timestamp"                 : lsc_expr
syntax:65 lsc_expr:65 "+" lsc_expr:66   : lsc_expr
syntax:65 lsc_expr:65 "-" lsc_expr:66   : lsc_expr
syntax:65 lsc_expr:65 "*" lsc_expr:66   : lsc_expr
syntax:45 lsc_expr:45 "==" lsc_expr:46  : lsc_expr
syntax:45 lsc_expr:45 "!=" lsc_expr:46  : lsc_expr
syntax:45 lsc_expr:45 "<"  lsc_expr:46  : lsc_expr
syntax:45 lsc_expr:45 "<=" lsc_expr:46  : lsc_expr
syntax:40 "!" lsc_expr                   : lsc_expr
syntax:35 lsc_expr:35 "&&" lsc_expr:36  : lsc_expr
syntax:30 lsc_expr:30 "||" lsc_expr:31  : lsc_expr
-- Mapping read
syntax lsc_expr "[" lsc_expr "]"         : lsc_expr

-- ─────────────────────────────────────────────
-- Statement syntax
-- ─────────────────────────────────────────────

-- skip (rarely written explicitly but needed for completeness)
syntax "skip" ";"                                              : lsc_stmt
-- sequence via juxtaposition (same as dss2024)
syntax lsc_stmt lsc_stmt                                       : lsc_stmt
-- local variable binding
syntax "let" ident ":=" lsc_expr ";"                           : lsc_stmt
-- storage write
syntax "storage" "." ident ":=" lsc_expr ";"                   : lsc_stmt
-- mapping write
syntax "storage" "." ident "[" lsc_expr "]" ":=" lsc_expr ";"  : lsc_stmt
-- require
syntax "require" "(" lsc_expr ")" "else" "revert" ident ";"   : lsc_stmt
-- if/else
syntax "if" "(" lsc_expr ")" "{" lsc_stmt "}"
       "else" "{" lsc_stmt "}"                                 : lsc_stmt
-- if without else (desugars to if/skip)
syntax "if" "(" lsc_expr ")" "{" lsc_stmt "}"                  : lsc_stmt
-- emit event
syntax "emit" ident "(" lsc_expr,* ")" ";"                    : lsc_stmt
-- revert
syntax "revert" ident ";"                                      : lsc_stmt
-- internal call
syntax "call" ident "(" lsc_expr,* ")" ";"                    : lsc_stmt
-- do-notation sugar (desugars to seq)
syntax "do" lsc_stmt                                           : lsc_stmt

-- ─────────────────────────────────────────────
-- Contract-level declarations
-- ─────────────────────────────────────────────

syntax ident ":" lsc_ty (":=" lsc_expr)?                       : lsc_field_decl
syntax "|" ident ("(" ident ":" lsc_ty ")")*                  : lsc_error_decl
syntax "|" ident ("(" ident ":" lsc_ty ")")*                  : lsc_event_decl

syntax "def" ident ":" "Tx" ":=" "do" lsc_stmt                : lsc_func_decl
syntax "def" ident ":" "View" ":=" "do" lsc_stmt               : lsc_func_decl

syntax "storage" ":" lsc_field_decl+
       "errors"  ":" lsc_error_decl+
       "events"  ":" lsc_event_decl+
       lsc_func_decl+                                          : lsc_contract_body

syntax "contract" ident "where" lsc_contract_body              : command

-- ─────────────────────────────────────────────
-- macro_rules: syntax → AST data
-- NO validation here. Pure structural translation.
-- Mirrors dss2024's macro_rules exactly.
-- ─────────────────────────────────────────────

macro_rules
  | `(lsc_ty| UInt256)  => `(Ty.uint256)
  | `(lsc_ty| Bool)     => `(Ty.bool)
  | `(lsc_ty| Address)  => `(Ty.address)
  | `(lsc_ty| Wad)      => `(Ty.wad)
  | `(lsc_ty| Ray)      => `(Ty.ray)

macro_rules
  | `(lsc_expr| $n:num)         => `(Expr.litU256 $(quote n.getNat))
  | `(lsc_expr| true)           => `(Expr.litBool true)
  | `(lsc_expr| false)          => `(Expr.litBool false)
  | `(lsc_expr| $i:ident)       => `(Expr.var $(quote i.getId.toString))
  | `(lsc_expr| msg.sender)     => `(Expr.caller)
  | `(lsc_expr| msg.value)      => `(Expr.callvalue)
  | `(lsc_expr| block.timestamp) => `(Expr.timestamp)
  | `(lsc_expr| $a + $b)        => `(Expr.addChecked (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $a - $b)        => `(Expr.subChecked (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $a == $b)       => `(Expr.eq (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $a < $b)        => `(Expr.lt (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $a <= $b)       => `(Expr.le (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| ! $e)           => `(Expr.not (lsc_expr| $e))
  | `(lsc_expr| $a && $b)       => `(Expr.and (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $a || $b)       => `(Expr.or  (lsc_expr| $a) (lsc_expr| $b))
  | `(lsc_expr| $m[$k])         => `(Expr.mappingGet (lsc_expr| $m) (lsc_expr| $k))

macro_rules
  | `(lsc_stmt| skip;)          => `(Stmt.skip)
  | `(lsc_stmt| $s1:lsc_stmt $s2:lsc_stmt) =>
      `(Stmt.seq (lsc_stmt| $s1) (lsc_stmt| $s2))
  | `(lsc_stmt| let $i := $e;)  =>
      `(Stmt.letBind $(quote i.getId.toString) (lsc_expr| $e))
  | `(lsc_stmt| storage.$f := $e;) =>
      `(Stmt.storageSet $(quote f.getId.toString) (lsc_expr| $e))
  | `(lsc_stmt| storage.$f[$k] := $v;) =>
      `(Stmt.storageMapSet $(quote f.getId.toString) (lsc_expr| $k) (lsc_expr| $v))
  | `(lsc_stmt| require ($e) else revert $err;) =>
      `(Stmt.require (lsc_expr| $e) $(quote err.getId.toString))
  | `(lsc_stmt| if ($e) { $s1 } else { $s2 }) =>
      `(Stmt.ifThenElse (lsc_expr| $e) (lsc_stmt| $s1) (lsc_stmt| $s2))
  | `(lsc_stmt| if ($e) { $s }) =>
      `(Stmt.ifThenElse (lsc_expr| $e) (lsc_stmt| $s) Stmt.skip)
  | `(lsc_stmt| emit $name($args,*);) =>
      `(Stmt.emit $(quote name.getId.toString) [$[((lsc_expr| $args))],*])
  | `(lsc_stmt| revert $err;) =>
      `(Stmt.revert $(quote err.getId.toString))
```

---

## Step 7 — Elaboration and Code Generation (`Lang/Contract.lean`)

This is where the `contract` macro expands to actual Lean definitions. It uses `elab_rules` (not `macro_rules`) so it can call `Lean.logErrorAt` for positioned error messages.

```lean
-- Lang/Contract.lean
import Lsc.Lang.AST
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lean

open Lean Elab Command

namespace Lsc

/-- Elaborate the `contract` command.
    1. Parse the body into a ContractDef (done by macro_rules)
    2. Run validation passes (DAG, linearity, selector collision)
    3. Generate: storage struct, error inductive, event inductive,
                 AST definitions, ContractM definitions
    All validation errors are reported with source positions. -/
elab_rules : command
  | `(command| contract $name where $body) => do
    -- Step 1: body was already macro-expanded to ContractDef fields
    -- Step 2: validate
    let contractDef ← parseContractBody name body
    match Checks.validateAll contractDef with
    | .error errors =>
      for (pos, msg) in errors do
        Lean.logErrorAt pos msg
      return
    | .ok validated =>
    -- Step 3: generate definitions
    generateStorageStruct validated
    generateErrorInductive validated
    generateEventInductive validated
    generateASTDefs validated
    generateContractMDefs validated
    generateDispatcher validated

/-- Generate the storage struct.
    `contract Counter where storage: number : UInt256 := 0`
    produces:
    `structure CounterStorage where number : UInt256 := 0` -/
def generateStorageStruct (c : ContractDef) : CommandElabM Unit := do
  let fields ← c.storage.mapM fun (name, ty, default) => do
    let leanTy ← tyToLean ty
    match default with
    | none     => `(Lean.Parser.Command.structExplicitBinder|
                    ($name : $leanTy))
    | some def => `(Lean.Parser.Command.structExplicitBinder|
                    ($name : $leanTy := $def))
  let structName := mkIdent (c.name ++ "Storage")
  elabCommand (← `(structure $structName where $[$fields]* deriving Repr))

/-- Generate the ContractM function for each FunctionDef.
    The generated function is the semantic ground truth for proofs.
    It is NOT the AST — it calls the AST eval. -/
def generateContractMDefs (c : ContractDef) : CommandElabM Unit := do
  let storageTy := mkIdent (c.name ++ "Storage")
  let eventTy   := mkIdent (c.name ++ "Event")
  let errorTy   := mkIdent (c.name ++ "Error")
  for fn in c.functions do
    let fnName    := mkIdent (c.name ++ "." ++ fn.name)
    let astName   := mkIdent (c.name ++ "." ++ fn.name ++ ".ast")
    -- The ContractM def is just Stmt.eval applied to the AST
    -- This makes Counter.increment = Stmt.eval Counter.increment.ast
    -- which holds by rfl — the key definitional equality for proofs
    elabCommand (← `(
      def $fnName : ContractM $storageTy $eventTy $errorTy Unit :=
        Stmt.eval $astName LocalEnv.empty
    ))
```

**The definitional equality trick**: by defining `Counter.increment` as literally `Stmt.eval Counter.increment.ast`, the theorem `Counter.increment = Stmt.eval Counter.increment.ast` holds by `rfl`. This means proofs about `Counter.increment` and proofs about the AST are interchangeable without any proof effort.

---

## Step 8 — Validation Passes (`Lang/Checks.lean`)

Three passes, run in order. Each returns `List (Syntax × String)` (position, message) for error reporting.

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

-- ── Combined validator ────────────────────────

def validateAll (c : ContractDef) : Except (List (Syntax × String)) ContractDef :=
  let errors : List (Syntax × String) := []
  -- collect all errors, report with positions
  -- return .ok c if no errors
  sorry

end Lsc.Checks
```

---

## Step 9 — Delaborators (`Lang/Delab.lean`)

Follow dss2024's `Delab.lean` exactly. Delaborators make proof goals display in source syntax rather than raw AST constructors. This is essential for readability — without them, every proof goal shows `Stmt.seq (Stmt.require ...) (Stmt.seq ...)` instead of the original source.

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
    | Expr.addChecked _ _ =>
      let a ← withAppFn <| withAppArg delabExprInner
      let b ← withAppArg delabExprInner
      `(lsc_expr| $a + $b)
    | Expr.not _ =>
      let e ← withAppArg delabExprInner
      `(lsc_expr| ! $e)
    | _ => failure
  annAsTerm stx

@[delab app.Lsc.Expr.litU256, delab app.Lsc.Expr.var,
  delab app.Lsc.Expr.caller,   delab app.Lsc.Expr.addChecked,
  delab app.Lsc.Expr.not]
partial def delabExpr : Delab := do
  guard <| match_expr ← getExpr with
    | Expr.litU256 _      => true
    | Expr.var _          => true
    | Expr.caller         => true
    | Expr.addChecked _ _ => true
    | Expr.not _          => true
    | _                   => false
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
    This function is TRUSTED in v1. Tested via conformance suite. -/
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

Write this before any other contract. If this contract cannot be proved, something in the framework is wrong.

```lean
-- Examples/Counter.lean
import Lsc.Lang.Contract
import Lsc.Lang.Eval

namespace Lsc.Examples

-- ── Contract definition ───────────────────────

contract Counter where
  storage:
    number : UInt256 := 0
    paused : Bool    := false
    owner  : Address

  errors:
    | Paused
    | NotOwner
    | Overflow

  events:
    | Incremented (n : UInt256)
    | WasPaused
    | WasUnpaused

  def increment : Tx := do
    require (!storage.paused) else revert Paused;
    let n := storage.number + 1;
    storage.number := n;
    emit Incremented(n);

  def pause : Tx := do
    require (msg.sender == storage.owner) else revert NotOwner;
    require (!storage.paused) else revert Paused;
    storage.paused := true;
    emit WasPaused();

  def unpause : Tx := do
    require (msg.sender == storage.owner) else revert NotOwner;
    require (storage.paused) else revert Paused;
    storage.paused := false;
    emit WasUnpaused();

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
    s'.storage.number = s.storage.number + 1 := by
  simp [Counter.increment, runS, Stmt.eval, ContractM.require,
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

### How `storageSet` works without knowing `S`

The generic `Stmt.eval` cannot write `s.reserve0 := v` because it doesn't know `S`. Resolution: the `contract` macro generates a **storage accessor table** for each contract:

```lean
-- generated by macro for Counter:
def CounterStorage.setField (field : Ident) (v : UInt256)
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

Implement in this exact order. Each step must compile before starting the next.

```
1.  Core/Types.lean           -- no dependencies
2.  Core/Arithmetic.lean      -- depends on Types
3.  Core/Mapping.lean         -- depends on Types, Mathlib.Finmap
4.  Core/LinearTypes.lean     -- depends on Types, Arithmetic
5.  Lang/AST.lean             -- depends on all Core
6.  Lang/Eval.lean            -- depends on AST
7.  Lang/Checks.lean          -- depends on AST
8.  Lang/Syntax.lean          -- depends on AST, Lean macro system
9.  Lang/Delab.lean           -- depends on Syntax
10. Lang/Contract.lean        -- depends on Eval, Checks, Syntax
11. Examples/Counter.lean     -- depends on Contract
    ← STOP HERE AND PROVE ALL COUNTER THEOREMS ←
12. Compile/IR.lean           -- depends on AST
13. Compile/Lower.lean        -- depends on IR, AST
14. Compile/Yul.lean          -- depends on IR, EvmYulLean
15. Compile/ABI.lean          -- depends on AST
16. Examples/AMM.lean         -- depends on Contract, World
```

Do not start step 12 until all counter theorems in step 11 pass. The counter proofs are the acceptance test for the entire framework.

---

## Appendix — What dss2024 Does That We Copy Directly

| dss2024 file    | What it does                          | Our equivalent              |
|-----------------|---------------------------------------|-----------------------------|
| `Syntax.lean`   | `declare_syntax_cat` + `macro_rules`  | `Lang/Syntax.lean`          |
| `Eval.lean`     | `Env`, `eval`, `@[simp]` lemmas       | `Lang/Eval.lean`            |
| `Delab.lean`    | `@[delab]` for pretty printing        | `Lang/Delab.lean`           |
| `Optimize.lean` | Transform + correctness theorem       | `Compile/Lower.lean`        |
| `BigStep.lean`  | Relational semantics for proofs       | User theorem files          |

The core pattern from dss2024 that we inherit: **syntax → pure AST data → separate eval function → proofs about eval**. The macro never contains logic. The eval function is the single source of truth for semantics. All proofs are about eval. This separation is what makes the system tractable.