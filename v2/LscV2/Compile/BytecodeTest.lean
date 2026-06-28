import LscV2.Compile.Bytecode
import LscV2.TestFixtures.SyntaxSmoke
import EvmYul.EVM.Instr
import EvmYul.Operations

open LscV2 LscV2.Compile LscV2.TestFixtures
open EvmYul EvmYul.EVM Operation

def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

def counterConfig : Config where
  storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  events := { topic0 := fun
    | "Incremented" => some incrementedTopic
    | _ => none }

namespace LscV2.BytecodeTest

private def stmtToBytecodeHex! (cfg : Config) (s : Stmt) : String :=
  match Compile.stmtToBytecodeHex cfg s with
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

/-- First opcode is PUSH0 (slot 0) before SLOAD. -/
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

#eval IO.println incrementBytecodeHex

end LscV2.BytecodeTest
