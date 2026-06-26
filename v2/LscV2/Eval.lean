import LscV2.AST

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

@[simp]
theorem revertUser_apply (err : Err) (s : ContractState S) :
    (revertUser err : ContractM S E Err A) s = .error err := rfl

def Except.orRevertArith [ContractErrors Err] {A} (x : Except ArithError A) : ContractM S E Err A :=
  match x with
  | .ok a => pure a
  | .error ae => revertArith ae

def require [ContractErrors Err] (cond : Bool) (err : Err) : ContractM S E Err Unit :=
  if cond then pure () else revertUser err

def caller : ContractM S E Err Address :=
  fun s => .ok (s.context.caller, s, [])

def callvalue : ContractM S E Err UInt256 :=
  fun s => .ok (s.context.callvalue, s, [])

def timestamp : ContractM S E Err UInt256 :=
  fun s => .ok (s.context.timestamp, s, [])

@[simp]
theorem runS_pure (a : A) (s : ContractState S) :
    (pure a : ContractM S E Err A) s = .ok (a, s, []) := rfl

@[simp]
theorem runS_bind_ok (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s : ContractState S) (a : A) (s' : ContractState S) (log : List E)
    (h : m s = .ok (a, s', log)) :
    (m >>= f) s =
      match f a s' with
      | .error e => .error e
      | .ok (b, s'', log2) => .ok (b, s'', log ++ log2) := by
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

@[simp]
theorem runS_bind_pure (m : ContractM S E Err A) (f : A → ContractM S E Err B)
    (s s' : ContractState S) (a : A) (b : B) (log : List E)
    (hm : m s = .ok (a, s', log)) (hf : f a s' = .ok (b, s', [])) :
    (m >>= f) s = .ok (b, s', log) := by
  simp [bind, hm, hf]

end ContractM

def runS {S E Err A : Type} (m : ContractM S E Err A) (s : ContractState S) :
    Except Err (A × ContractState S × List E) :=
  m s

@[simp]
theorem runS_revertArith {S E Err A : Type} [ContractErrors Err] (ae : ArithError)
    (s : ContractState S) :
    runS (ContractM.revertArith ae : ContractM S E Err A) s =
      .error (ContractErrors.arith ae) := rfl

@[simp]
theorem runS_get' {S E Err : Type} (s : ContractState S) :
    runS (ContractM.get : ContractM S E Err (ContractState S)) s = .ok (s, s, []) := rfl

@[simp]
theorem runS_modifyStorage' {S E Err : Type} (f : S → S) (s : ContractState S) :
    runS (ContractM.modifyStorage f : ContractM S E Err Unit) s =
      .ok ((), { s with storage := f s.storage }, []) := rfl

@[simp]
theorem runS_emit' {S E Err : Type} (e : E) (s : ContractState S) :
    runS (ContractM.emit e : ContractM S E Err Unit) s = .ok ((), s, [e]) := rfl

/-- Runtime values tagged by AST type. -/
inductive Val : Ty → Type
  | u256 : UInt256 → Val .uint256
  | bool : Bool → Val .bool
  | addr : Address → Val .address
  | wei : Wei → Val .wei
  | wad : Wad → Val .wad
  | ray : Ray → Val .ray
  | tokenAmount : TokenAmount → Val .tokenAmount
  | allowance : Allowance → Val .allowance
  | flashReceipt : FlashLoanReceipt → Val .flashReceipt
  | lock : Lock → Val .lock
  | capability : Capability → Val .capability
  | positionTicket : PositionTicket → Val .positionTicket
  | mapping : {k v : Ty} → Mapping Ident UInt256 → Val (.mapping k v)
  | unit : Val .unit

namespace Val

def boolOf (v : Val .bool) : Bool :=
  match v with | .bool b => b

@[simp]
theorem boolOf_bool (b : Bool) : Val.boolOf (.bool b) = b := rfl

@[simp]
theorem bool_val_boolOf (b : Bool) : (Val.bool b).boolOf = b := rfl

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
  | .wad, .wad x, .wad y => x == y
  | .ray, .ray x, .ray y => x == y
  | .tokenAmount, .tokenAmount x, .tokenAmount y => x == y
  | .allowance, .allowance x, .allowance y => x == y
  | .flashReceipt, .flashReceipt x, .flashReceipt y => x == y
  | .lock, .lock x, .lock y => x == y
  | .capability, .capability x, .capability y => x == y
  | .positionTicket, .positionTicket x, .positionTicket y => x == y
  | Ty.mapping _ _, .mapping x, .mapping y => x.inner == y.inner
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

def bind (name : Ident) (val : Sigma Val) (env : LocalEnv) : LocalEnv :=
  { lookup := fun n => if n == name then some val else env.lookup n }

end LocalEnv

/-- Read and write typed storage fields by name. -/
class StorageOps (S : Type) where
  storageGet : (t : Ty) → Ident → S → Option (Val t)
  storageSet : (t : Ty) → Ident → Val t → S → S

/-- Resolve user error names from the AST. -/
class ErrorResolver (Err : Type) where
  resolve : Ident → Option Err

/-- Build typed events from AST emit nodes. -/
class EventBuilder (E : Type) where
  build : Ident → List (Sigma Val) → Option E

namespace Expr

variable {S E Err : Type} [ContractErrors Err] [StorageOps S]

def eval {t : Ty} (e : Expr t) (env : LocalEnv) : ContractM S E Err (Val t) :=
  match e with
  | .litU256 n => pure (.u256 n)
  | .litWei n => pure (.wei (Wei.mkNat n))
  | .litBool b => pure (.bool b)
  | .litAddr a => pure (.addr a)
  | .var name =>
    match env.lookup name with
    | some ⟨t', v⟩ =>
      if ht : t = t' then
        pure (cast (by simp [ht]) v)
      else
        ContractM.revert .Unauthorized
    | none => ContractM.revert .Unauthorized
  | .storageGet name => do
    let st ← ContractM.get
    match StorageOps.storageGet t name st.storage with
    | some v => pure v
    | none => ContractM.revert .Unauthorized
  | .caller => do
    let a ← ContractM.caller
    pure (.addr a)
  | .callvalue => do
    let v ← ContractM.callvalue
    pure (.u256 v)
  | .timestamp => do
    let v ← ContractM.timestamp
    pure (.u256 v)
  | .weiAddChecked a b => do
    let va ← a.eval env
    let vb ← b.eval env
    match Wei.addChecked (Val.weiOf va) (Val.weiOf vb) with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure (.wei r)
  | .weiSubChecked a b => do
    let va ← a.eval env
    let vb ← b.eval env
    match Wei.subChecked (Val.weiOf va) (Val.weiOf vb) with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure (.wei r)
  | .weiMulChecked a b => do
    let va ← a.eval env
    let vb ← b.eval env
    match Wei.mulChecked (Val.weiOf va) (Val.weiOf vb) with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure (.wei r)
  | .weiDivFloor a b => do
    let va ← a.eval env
    let vb ← b.eval env
    match Wei.divFloor (Val.weiOf va) (Val.weiOf vb) with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure (.wei r)
  | .weiAddCheckedNat a n => do
    let va ← a.eval env
    match Wei.addCheckedNat (Val.weiOf va) n with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure (.wei r)
  | .eq a b => do
    let va ← a.eval env
    let vb ← b.eval env
    pure (.bool (Val.eq va vb))
  | .not a => do
    let va ← a.eval env
    pure (.bool (!Val.boolOf va))
  | .and a b => do
    let va ← a.eval env
    let vb ← b.eval env
    pure (.bool (Val.boolOf va && Val.boolOf vb))
  | .or a b => do
    let va ← a.eval env
    let vb ← b.eval env
    pure (.bool (Val.boolOf va || Val.boolOf vb))
  | .lt a b => do
    let va ← a.eval env
    let vb ← b.eval env
    pure (.bool (Val.u256Of va < Val.u256Of vb))
  | .le a b => do
    let va ← a.eval env
    let vb ← b.eval env
    pure (.bool (Val.u256Of va ≤ Val.u256Of vb))
  | _ => ContractM.revert .Unauthorized

attribute [reducible] eval

end Expr

namespace Stmt

variable {S E Err : Type} [ContractErrors Err] [StorageOps S] [ErrorResolver Err] [EventBuilder E]

def eval (stmt : Stmt) (env : LocalEnv) : ContractM S E Err LocalEnv :=
  match stmt with
  | .skip => pure env
  | .seq s1 s2 => do
    let env' ← s1.eval env
    s2.eval env'
  | .letBind name ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    pure (LocalEnv.bind name ⟨t, v⟩ env)
  | .storageSet field ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    ContractM.modifyStorage (StorageOps.storageSet t field v)
    pure env
  | .require condExpr errName => do
    let v ← Expr.eval condExpr env
    if Val.boolOf v then
      pure env
    else
      match ErrorResolver.resolve errName with
      | some err => ContractM.revertUser err
      | none => ContractM.revert .Unauthorized
  | .ifThenElse cond thn els => do
    let v ← Expr.eval cond env
    if Val.boolOf v then thn.eval env else els.eval env
  | .emit eventName args => do
    let vals ← args.mapM fun ⟨t, e⟩ => do
      let v ← Expr.eval e env
      pure ⟨t, v⟩
    match EventBuilder.build eventName vals with
    | some ev => do
      ContractM.emit ev
      pure env
    | none => ContractM.revert .Unauthorized
  | .revert errName =>
    match ErrorResolver.resolve errName with
    | some err => ContractM.revertUser err
    | none => ContractM.revert .Unauthorized
  | _ => pure env

attribute [reducible] eval

end Stmt

end LscV2
