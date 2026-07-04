import Lsc.Compile.Bytecode
import Lsc.TestFixtures.SyntaxSmoke
import Lsc.Selectors
import EvmYul.EVM.Instr
import EvmYul.Operations

open Lsc Lsc.Compile Lsc.Compile.Bytecode Lsc.TestFixtures
open EvmYul EvmYul.EVM Operation

def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

/-- Regression check: `computeEventTopic0`'s real Keccak256 computation over
`"Incremented(uint256)"` must reproduce this file's (and `derive_contract_def`'s
auto-generated) pinned `incrementedTopic` literal exactly. -/
example : computeEventTopic0 "Incremented" [("n", .wei)] = incrementedTopic := by native_decide

/-- Stub topic0 for events without a pinned keccak (see `Selectors.computeSelector`). -/
def stubEventTopic0 : Ident → Option Nat
  | "Incremented" => some incrementedTopic
  | name => some name.hash.toNat

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, none), ("paused", .bool, some ⟨.bool, CoreExpr.lit Ty.bool (.bool false)⟩),
     ("owner", .address, none)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [{ name := "increment", kind := .external, params := [], retTy := .unit, body := incrementAst },
     { name := "pause", kind := .external, params := [], retTy := .unit, body := pauseAst },
     { name := "unpause", kind := .external, params := [], retTy := .unit, body := unpauseAst }]
  interfaces := []

def counterConfig : Config :=
  configFromContract counterDef stubEventTopic0

private def selectorHex (sel : Nat) : String :=
  let s := (BitVec.ofNat 32 sel).toHex
  if s.length < 8 then String.replicate (8 - s.length) '0' ++ s else s

namespace Lsc.BytecodeTest

private def stmtToBytecodeHex! (cfg : Config) (s : Stmt) : String :=
  match Compile.stmtToBytecodeHex cfg s with
  | .ok hex => hex
  | .error e => panic! e

private def contractToBytecodeHex! : String :=
  match Compile.contractToBytecodeHex counterDef stubEventTopic0 with
  | .ok hex => hex
  | .error e => panic! e

/-- Lower increment body only (bytecode slice test). -/
def incrementBodyAst : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementBytecodeHex : String :=
  stmtToBytecodeHex! counterConfig incrementBodyAst

def incrementBytecode : ByteArray :=
  match Compile.stmtToBytecode counterConfig incrementBodyAst with
  | .ok bytes => bytes
  | .error e => panic! e

def counterBytecodeHex : String :=
  contractToBytecodeHex!

def counterBytecode : ByteArray :=
  match Compile.contractToBytecode counterDef stubEventTopic0 with
  | .ok bytes => bytes
  | .error e => panic! e

private def selectorFor (name : Ident) : Nat :=
  match counterDef.functions.find? (·.name == name) with
  | some fn => computeSelector fn |>.toNat
  | none => 0

def incrementSelector : Nat := selectorFor "increment"
def pauseSelector : Nat := selectorFor "pause"
def unpauseSelector : Nat := selectorFor "unpause"

theorem counter_contract_lowers_ok :
    Compile.contractToBytecode counterDef stubEventTopic0 |>.isOk := by native_decide

theorem counter_bytecode_contains_calldataload :
    counterBytecodeHex.contains "35" = true := by native_decide

theorem counter_bytecode_contains_calldatasize :
    counterBytecodeHex.contains "36" = true := by native_decide

theorem counter_bytecode_contains_jumpi :
    counterBytecodeHex.contains "57" = true := by native_decide

theorem counter_bytecode_contains_jumpdest :
    counterBytecodeHex.contains "5b" = true := by native_decide

theorem counter_bytecode_contains_increment_selector :
    counterBytecodeHex.contains (selectorHex incrementSelector) = true := by native_decide

theorem counter_bytecode_contains_pause_selector :
    counterBytecodeHex.contains (selectorHex pauseSelector) = true := by native_decide

theorem counter_bytecode_contains_unpause_selector :
    counterBytecodeHex.contains (selectorHex unpauseSelector) = true := by native_decide

theorem counter_bytecode_longer_than_increment_body :
    counterBytecodeHex.length > incrementBytecodeHex.length := by native_decide

theorem increment_bytecode_starts_push0 :
    parseInstr (incrementBytecode.get! 0) = some PUSH0 := by native_decide

theorem increment_bytecode_has_sload :
    parseInstr (incrementBytecode.get! 1) = some SLOAD := by native_decide

theorem increment_bytecode_contains_sload :
    incrementBytecodeHex.contains "54" = true := by native_decide

theorem increment_bytecode_contains_sstore :
    incrementBytecodeHex.contains "55" = true := by native_decide

theorem increment_bytecode_contains_log1 :
    incrementBytecodeHex.contains "a1" = true := by native_decide

theorem increment_bytecode_contains_revert :
    incrementBytecodeHex.contains "fd" = true := by native_decide

theorem increment_bytecode_contains_push :
    (incrementBytecodeHex.take 2 == "0x") ∧ incrementBytecodeHex.any (fun c =>
      c == '6' ∨ c == '7') := by native_decide

theorem increment_bytecode_nonempty :
    incrementBytecodeHex.length > 2 := by native_decide

def counterInstrs : List Instr :=
  match Bytecode.Contract.contract counterConfig counterDef with
  | .ok instrs => instrs
  | .error e => panic! e

def counterJumpDestLabels : List String :=
  jumpDestLabelList counterInstrs

private def labelsAllUnique (xs : List String) : Bool :=
  xs.all fun lbl => xs.count lbl == 1

theorem counter_jumpdest_labels_unique :
    labelsAllUnique counterJumpDestLabels = true := by native_decide

theorem counter_jumpdest_count_sufficient :
    counterJumpDestLabels.length ≥ 4 := by native_decide

#eval IO.println incrementBytecodeHex
#eval IO.println counterBytecodeHex

end Lsc.BytecodeTest
