import LscV2.Lang.Eval
import LscV2.Compile.Yul
import LscV2.Compile.Bytecode

/-!
Counter example — target DSL shape is in docs/spec_idea_2/reference/COUNTER.md.
Hand-written until contract elaboration (IMPLEMENTATION.md Step 7).
-/

open LscV2 LscV2.Compile

namespace Counter

set_option linter.unusedSimpArgs false

structure CounterStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner : Address := 0
  deriving Repr

instance : Inhabited CounterStorage where
  default := {}

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq

instance : Inhabited CounterError where
  default := .Paused

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq

instance : ContractErrors CounterError where
  arith := fun
    | .Overflow => .Overflow
    | ae => ContractErrors.unreachableArith ae
  fromFramework := fun _ => .Overflow

def getField (t : Ty) (field : String) (s : CounterStorage) : Option (Val t) :=
  match t, field with
  | .wei, "number" => some (.wei s.number)
  | .bool, "paused" => some (.bool s.paused)
  | .address, "owner" => some (.addr s.owner)
  | _, _ => none

def setField (t : Ty) (field : String) (v : Val t) (s : CounterStorage) : CounterStorage :=
  match t, field, v with
  | .wei, "number", .wei w => { s with number := w }
  | .bool, "paused", .bool b => { s with paused := b }
  | .address, "owner", .addr a => { s with owner := a }
  | _, _, _ => s

@[simp] theorem getField_number (s : CounterStorage) :
    getField Ty.wei "number" s = some (.wei s.number) := rfl

@[simp] theorem getField_paused (s : CounterStorage) :
    getField Ty.bool "paused" s = some (.bool s.paused) := rfl

@[simp] theorem getField_owner (s : CounterStorage) :
    getField Ty.address "owner" s = some (.addr s.owner) := rfl

@[simp] theorem setField_number (v : Wei) (s : CounterStorage) :
    setField Ty.wei "number" (.wei v) s = { s with number := v } := rfl

@[simp] theorem setField_paused (v : Bool) (s : CounterStorage) :
    setField Ty.bool "paused" (.bool v) s = { s with paused := v } := rfl

@[simp] theorem setField_owner (v : Address) (s : CounterStorage) :
    setField Ty.address "owner" (.addr v) s = { s with owner := v } := rfl

def incrementAst : Stmt :=
  Stmt.seq
    (Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused")
    (Stmt.seq
      (Stmt.letBind "n" ⟨Ty.wei, Wei.addCheckedNatStorage "number" 1⟩)
      (Stmt.seq
        (Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩)
        (Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩])))

def pauseAst : Stmt :=
  Stmt.seq
    (Stmt.require
      (CoreExpr.eq Ty.address (CoreExpr.txField .caller) (CoreExpr.storageGet Ty.address "owner"))
      "NotOwner")
    (Stmt.seq
      (Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused")
      (Stmt.seq
        (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool true)⟩)
        (Stmt.emit "Paused" [])))

def unpauseAst : Stmt :=
  Stmt.seq
    (Stmt.require
      (CoreExpr.eq Ty.address (CoreExpr.txField .caller) (CoreExpr.storageGet Ty.address "owner"))
      "NotOwner")
    (Stmt.seq
      (Stmt.require (CoreExpr.storageGet Ty.bool "paused") "Paused")
      (Stmt.seq
        (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool false)⟩)
        (Stmt.emit "Unpaused" [])))

def resolveError (name : String) : Option CounterError :=
  match name with
  | "Paused" => some .Paused
  | "NotOwner" => some .NotOwner
  | "Overflow" => some .Overflow
  | _ => none

def buildEvent (name : String) (vals : List (Sigma Val)) : Option CounterEvent :=
  match name, vals with
  | "Incremented", [⟨.wei, (.wei n)⟩] => some (.Incremented n)
  | "Paused", [] => some .Paused
  | "Unpaused", [] => some .Unpaused
  | _, _ => none

@[simp] theorem resolveError_paused :
    resolveError "Paused" = some .Paused := rfl

@[simp] theorem resolveError_notOwner :
    resolveError "NotOwner" = some .NotOwner := rfl

@[simp] theorem resolveError_overflow :
    resolveError "Overflow" = some .Overflow := rfl

@[simp] theorem buildEvent_incremented (n : Wei) :
    buildEvent "Incremented" [⟨Ty.wei, (.wei n)⟩] = some (.Incremented n) := rfl

@[simp] theorem buildEvent_paused :
    buildEvent "Paused" [] = some .Paused := rfl

@[simp] theorem buildEvent_unpaused :
    buildEvent "Unpaused" [] = some .Unpaused := rfl

@[reducible] instance : ContractDSL CounterStorage CounterEvent CounterError where
  getField  := Counter.getField
  setField  := Counter.setField
  resolveErr := Counter.resolveError
  buildEvent := Counter.buildEvent

@[simp] theorem counter_dsl_getField (t : Ty) (f : Ident) (s : CounterStorage) :
    @ContractDSL.getField CounterStorage CounterEvent CounterError _ _ t f s = Counter.getField t f s := rfl

@[simp] theorem counter_dsl_setField (t : Ty) (f : Ident) (v : Val t) (s : CounterStorage) :
    @ContractDSL.setField CounterStorage CounterEvent CounterError _ _ t f v s = Counter.setField t f v s := rfl

@[simp] theorem counter_dsl_resolveErr (name : Ident) :
    @ContractDSL.resolveErr CounterStorage CounterEvent CounterError _ _ name = Counter.resolveError name := rfl

@[simp] theorem counter_dsl_buildEvent (name : Ident) (vals : List (Sigma Val)) :
    @ContractDSL.buildEvent CounterStorage CounterEvent CounterError _ _ name vals = Counter.buildEvent name vals := rfl

@[simp] theorem counterError_arith_overflow :
    @ContractErrors.arith CounterError _ ArithError.Overflow = CounterError.Overflow := rfl

abbrev CounterM := ContractM CounterStorage CounterEvent CounterError

def increment : CounterM Unit :=
  Stmt.eval incrementAst

def pause : CounterM Unit :=
  Stmt.eval pauseAst

def unpause : CounterM Unit :=
  Stmt.eval unpauseAst

def counterFn (name : Ident) (body : Stmt) : FunctionDef where
  name := name
  kind := .external
  params := []
  retTy := .unit
  body := body

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, none), ("paused", .bool, some ⟨.bool, CoreExpr.lit Ty.bool (.bool false)⟩),
     ("owner", .address, none)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [counterFn "increment" incrementAst, counterFn "pause" pauseAst,
     counterFn "unpause" unpauseAst]
  interfaces := []
  -- Set owner = msg.sender (deployer) at construction time so pause/unpause work.
  constructor := some (Stmt.storageSet "owner" ⟨Ty.address, CoreExpr.txField .caller⟩)

/-- Compile layout for Yul / bytecode emission. -/
def stubEventTopic0 : Ident → Option Nat
  | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
  | name => some name.hash.toNat

def compileConfig : Config :=
  Compile.configFromContract counterDef stubEventTopic0

def incrementYul : String :=
  match Compile.stmtToYul compileConfig incrementAst with
  | .ok yul => yul
  | .error _ => ""

def counterBytecodeHex : String :=
  match Compile.contractToBytecodeHex counterDef stubEventTopic0 with
  | .ok hex => hex
  | .error _ => ""

/-- Full deploy transaction payload (constructor sets owner = deployer, then
    returns runtime bytecode via CODECOPY + RETURN). -/
def counterDeployHex : String :=
  match Compile.deployToBytecodeHex counterDef stubEventTopic0 with
  | .ok hex => hex
  | .error _ => ""

/-- Convert `¬ b` (where `b : Bool`) to `b = false`. -/
private theorem bool_not_to_false {b : Bool} (h : ¬ b) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

private theorem runIncrementOk
    (s : ContractState CounterStorage)
    (hp : s.storage.paused = false)
    (hno : s.storage.number.canAddNat 1) :
    runS increment s = .ok ((),
      { s with storage := { s.storage with
          number := ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ } },
      [CounterEvent.Incremented ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩]) := by
  have hok : Wei.addCheckedNat s.storage.number 1 =
      .ok ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ :=
    Wei.addCheckedNat_ok s.storage.number 1 hno
  simp [runS, increment, incrementAst, hp, hok,
    List.mapM, List.mapM.loop, List.reverseAux]

private theorem runPauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = false) :
    runS pause s = .ok ((),
      { s with storage := { s.storage with paused := true } },
      [CounterEvent.Paused]) := by
  simp [runS, pause, pauseAst, howner, hp, List.mapM, List.mapM.loop, List.reverseAux]

private theorem runUnpauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = true) :
    runS unpause s = .ok ((),
      { s with storage := { s.storage with paused := false } },
      [CounterEvent.Unpaused]) := by
  simp [runS, unpause, unpauseAst, howner, hp, List.mapM, List.mapM.loop, List.reverseAux]

theorem increment_increases_number_when_not_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.number.raw.toNat = s.storage.number.raw.toNat + 1 := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h
  simp only [BitVec.toNat_ofNat]
  omega

theorem increment_errors_when_paused
    (s : ContractState CounterStorage)
    (hp : s.storage.paused) :
    runS increment s = .error CounterError.Paused := by
  simp [runS, increment, incrementAst, show s.storage.paused = true from hp]

theorem increment_does_not_change_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_does_not_change_owner
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.owner = s.storage.owner := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_emits_incremented
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_reverts_on_overflow
    (s : ContractState CounterStorage)
    (hpaused : ¬ s.storage.paused)
    (hov : ¬ s.storage.number.canAddNat 1) :
    runS increment s = .error CounterError.Overflow := by
  have hp' := bool_not_to_false hpaused
  have herr : Wei.addCheckedNat s.storage.number 1 = .error ArithError.Overflow :=
    Wei.addCheckedNat_error s.storage.number 1 hov
  simp [runS, increment, incrementAst, hp', herr, ContractM.revertArith]

theorem pause_sets_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hpaused : ¬ s.storage.paused)
    (h : runS pause s = .ok ((), s', log)) :
    s'.storage.paused = true := by
  have hp' := bool_not_to_false hpaused
  rw [runPauseOk s howner hp'] at h
  cases h; rfl

theorem pause_errors_when_not_owner
    (s : ContractState CounterStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS pause s = .error CounterError.NotOwner := by
  simp [runS, pause, pauseAst, show (s.context.caller == s.storage.owner) = false from
    bool_not_to_false h]

theorem pause_errors_when_already_paused
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused) :
    runS pause s = .error CounterError.Paused := by
  simp [runS, pause, pauseAst, howner, show s.storage.paused = true from hp]

theorem unpause_clears_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused)
    (h : runS unpause s = .ok ((), s', log)) :
    s'.storage.paused = false := by
  have heq : s.storage.paused = true := hp
  rw [runUnpauseOk s howner heq] at h
  cases h; rfl

end Counter
