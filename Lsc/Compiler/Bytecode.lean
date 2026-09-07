import Lsc.Compiler.Yul
import YulEvmCompiler.Instr
import YulEvmCompiler.Compile
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate

/-!
# Yul → EVM bytecode via powdr

`compileRuntime` compiles the memoryguard-erased dispatcher, or — when that
needs `DUP17+` — powdr's verified spill of the disambiguated runtime
(inlined switch cases reuse `v_i`, and `spillBlock?` requires unique names
per frame). `compileDeploy` uses `spillObjectWithFallback` after the same
disambiguation (constructor stays unguarded; the nested `"runtime"` object
carries the guard).
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics.EVM (Op ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.Normalize

/-- Unique names so `spillBlock?` `selectedWF` can accept inlined cases. -/
def uniquifyBlock (b : YBlock) : YBlock := disambiguate b

def uniquifyObject (o : YObject) : YObject := disambiguateObject o

/-- Spill the disambiguated runtime; `none` if nothing needs spilling. -/
def spillRuntime? (b : YBlock) : Option Result :=
  spillBlock? (uniquifyBlock b)

def compileErased (b : YBlock) : Option (List Instr) :=
  compile (eraseMemoryGuardStmts b)

def compileSpilled (b : YBlock) : Option (List Instr) :=
  match spillRuntime? b with
  | some r => compile r.block
  | none => none

/-- Erase-compile. Theorems use this; `compileRuntime` also tries `compileSpilled`. -/
abbrev compileBlock (b : YBlock) : Option (List Instr) :=
  compileErased b

def compileRuntime (c : ContractDef) : Option (List UInt8) := do
  let b ← runtimeBlock c
  let is ← compileErased b <|> compileSpilled b
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
  let raw := uniquifyObject o
  let spilled ← spillObjectWithFallback raw (deployFallback raw)
  let L ← compileObject spilled.object
  return L.code

end Lsc.Compiler
