import LscV2.Lang.AST
import LscV2.Arithmetic

namespace LscV2

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
  | .unit, .unit, .unit => true
  | _, _, _ => false

@[simp]
theorem eq_addr (x y : Address) : Val.eq (.addr x) (.addr y) = (x == y) := rfl

end Val

structure LocalEnv where
  lookup : Ident → Option (Sigma Val)
  deriving Inhabited

namespace LocalEnv

def empty : LocalEnv := { lookup := fun _ => none }

@[simp] theorem empty_eq : empty = { lookup := fun _ => none } := rfl

def bind (name : Ident) (val : Sigma Val) (env : LocalEnv) : LocalEnv :=
  { lookup := fun n => if n == name then some val else env.lookup n }

@[simp] theorem bind_lookup_self (name : String) (v : Sigma Val) (env : LocalEnv) :
    (LocalEnv.bind name v env).lookup name = some v := by
  simp [LocalEnv.bind]

@[simp] theorem bind_lookup_ne (name key : String) (v : Sigma Val) (env : LocalEnv)
    (h : key ≠ name) :
    (LocalEnv.bind name v env).lookup key = env.lookup key := by
  simp only [LocalEnv.bind]
  rw [beq_false_of_ne h]
  simp

end LocalEnv

class ContractDSL (S : Type) (E : Type) (Err : Type) [ContractErrors Err] where
  getField  : (t : Ty) → Ident → S → Option (Val t)
  setField  : (t : Ty) → Ident → Val t → S → S
  resolveErr : Ident → Option Err
  buildEvent : Ident → List (Sigma Val) → Option E

end LscV2
