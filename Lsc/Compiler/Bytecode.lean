import Lsc.Compiler.Yul
import YulEvmCompiler.Instr
import YulEvmCompiler.Compile
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.Pipeline

/-!
# Yul → EVM bytecode via powdr

`compileRuntime` compiles the memoryguard-erased dispatcher, or — when that
needs `DUP17+` — powdr's verified spill of the raw guarded runtime. Locals are
`{f.name}_{i}`, so `spillBlock?` `selectedWF` holds without `disambiguate`.
`compileDeploy` uses `spillObjectWithFallback` on the raw object (constructor
stays unguarded; the nested `"runtime"` object carries the guard).
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics.EVM (Op ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect

/-- Spill the raw runtime; `none` if nothing needs spilling. -/
def spillRuntime? (b : YBlock) : Option Result :=
  spillBlock? b

def compileErased (b : YBlock) : Option (List Instr) :=
  compile (eraseMemoryGuardStmts b)

def compileSpilled (b : YBlock) : Option (List Instr) :=
  match spillRuntime? b with
  | some r => compile r.block
  | none => none

/-- Erase-compile, then powdr spill when erasure is rejected (`DUP17+`). -/
abbrev compileBlock (b : YBlock) : Option (List Instr) :=
  compileErased b <|> compileSpilled b

def compileRuntime (c : ContractDef) : Option (List UInt8) := do
  let b ← runtimeBlock c
  let is ← compileBlock b
  return assembleBytes is

/-- Labelled Asm; spill fallback matches `compileRuntime`. -/
def compileAsmBlock (b : YBlock) : Option (List Asm) :=
  match compileAsm (eraseMemoryGuardStmts b) with
  | some a => some a
  | none =>
    match spillRuntime? b with
    | some r => compileAsm r.block
    | none => none

/-- Fallback when a node does not spill: verified object pipeline after erase. -/
def deployFallback (o : YObject) : YObject :=
  optimizerPipelineObject (calls := ExternalCalls.none) (creates := ExternalCreates.none)
    (gasOracle := ExternalGas.any) (eraseMemoryGuardObject o)

def compileDeploy (c : ContractDef) : Option (List UInt8) := do
  let o ← deployObject c
  let spilled ← spillObjectWithFallback o (deployFallback o)
  let L ← compileObject spilled.object
  return L.code

end Lsc.Compiler
