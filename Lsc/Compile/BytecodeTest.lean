import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.Contract
import Lsc.Compile.Bytecode.CodegenInvariant
import Lsc.Compile.Lower
import Lsc.Compile.IR.Opt.Pipeline
import Lsc.TestFixtures.SyntaxSmoke
import Lsc.Selectors

open Lsc Lsc.Compile Lsc.Compile.Bytecode Lsc.TestFixtures

def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

/-- **Property:** `computeEventTopic0` matches the pinned `Incremented` topic. -/
example : computeEventTopic0 "Incremented" [("n", .wei)] = incrementedTopic := by native_decide

def stubEventTopic0 : Ident → Option Nat
  | "Incremented" => some incrementedTopic
  | name => some name.hash.toNat

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, some ⟨.wei, Wei.Expr.lit 0⟩),
     ("paused", .bool, some ⟨.bool, CoreExpr.lit Ty.bool (.bool false)⟩),
     ("owner", .address, some ⟨.address, CoreExpr.lit Ty.address (.addr 0)⟩)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [{ name := "increment", kind := .external, params := [], retTy := .unit, body := incrementAst },
     { name := "pause", kind := .external, params := [], retTy := .unit, body := pauseAst },
     { name := "unpause", kind := .external, params := [], retTy := .unit, body := unpauseAst }]
  interfaces := []

def counterConfig : Config :=
  configFromContract counterDef stubEventTopic0

namespace Lsc.BytecodeTest

/-- Lower increment body only (bytecode slice test). -/
def incrementBodyAst : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementBytecode : ByteArray :=
  match Compile.stmtToBytecode counterConfig incrementBodyAst with
  | .ok bytes => bytes
  | .error e => panic! e

private def incrementInstrs : List Instr :=
  match Lower.stmt counterConfig incrementBodyAst with
  | .ok ir =>
    match Bytecode.Codegen.stmtFresh (IR.Opt.optimizeStmt ir) with
    | .ok instrs => instrs
    | .error e => panic! e
  | .error e => panic! e

def counterInstrs : List Instr :=
  match Bytecode.Contract.contract counterConfig counterDef with
  | .ok instrs => instrs
  | .error e => panic! e

/-- **Property:** Counter contract bytecode lowers without error. -/
example : (contractToBytecode counterDef stubEventTopic0).isOk := by
  native_decide

/-- **Property:** Counter bytecode includes a calldata selector dispatcher. -/
theorem counter_bytecode_has_selector_dispatch :
    hasSelectorDispatch counterInstrs = true := by native_decide

/-- **Property:** All jump destination labels in counter bytecode are unique. -/
theorem counter_jumpdest_labels_unique :
    jumpDestsUnique counterInstrs = true := by native_decide

/-- **Property:** Counter bytecode has enough dispatch targets for three external functions. -/
theorem counter_jumpdest_count_sufficient :
    (jumpDestLabelList counterInstrs).length ≥ 4 := by native_decide

/-- **Property:** Increment body slice reads storage slot 0 (`number`). -/
theorem increment_body_reads_storage_slot_zero :
    readsStorageSlot incrementInstrs 0 = true := by native_decide

/-- **Property:** Increment body slice writes storage slot 0 (`number`). -/
theorem increment_body_writes_storage_slot_zero :
    writesStorageSlot incrementInstrs 0 = true := by native_decide

/-- **Property:** Increment bytecode slice is non-empty. -/
theorem increment_bytecode_nonempty :
    incrementBytecode.size > 0 := by native_decide

/-- Constructor with one `address` param loads calldata word 0 (no selector prefix). -/
def ctorDeployDef : ContractDef where
  name := "CtorDeploy"
  storage := [("token", .address, none)]
  errors := []
  events := []
  functions := []
  interfaces := []
  deployFn := some {
    name := "deploy", kind := .constructor, params := [("token_", .address)],
    retTy := .unit,
    body := Stmt.storageSet "token" ⟨.address, CoreExpr.var .address "token_"⟩,
    nonReentrant := false }

def ctorDeployCfg : Config := configFromContract ctorDeployDef stubEventTopic0

def ctorParamLoadInstrs : List Instr :=
  match ctorDeployDef.deployFn with
  | some fn =>
    match Bytecode.Contract.constructorInstrs ctorDeployCfg fn with
    | .ok instrs => instrs
    | .error e => panic! e
  | none => panic! "missing deployFn"

/-- **Property:** Constructor loads the deploy parameter from calldata word offset 0. -/
theorem ctor_deploy_loads_calldata_word_zero :
    loadsCalldataWord ctorParamLoadInstrs 0 = true := by native_decide

end Lsc.BytecodeTest
