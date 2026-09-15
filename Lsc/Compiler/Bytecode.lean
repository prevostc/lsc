import Lsc.Compiler.Yul
import YulEvmCompiler.Instr
import YulEvmCompiler.Compile
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect

/-!
# Yul → EVM bytecode via powdr

`compileRuntime` compiles the memoryguard-erased dispatcher, or — when that
needs `DUP17+` — powdr's verified spill of the raw guarded runtime. Locals are
`{f.name}_{i}`, so `spillBlock?` `selectedWF` holds without `disambiguate`.
`compileDeploy` embeds those bytes as `data "runtime"` and compiles only the
constructor object (`compileObject`); the source optimizer is not run on the
runtime. CREATE therefore installs `compileRuntime` (`deploy_installs_runtime`).
-/

namespace Lsc.Compiler

open Lsc
open YulEvmCompiler
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

/-- Init bytecode: embed `compileRuntime` as `data "runtime"`, compile the
constructor object. The constructor is unguarded (`datacopy` would smash spill
scratch) and small enough for raw `compileObject`. -/
def compileDeploy (c : ContractDef) : Option (List UInt8) :=
  compileRuntime c >>= fun rt =>
    deployObject c rt >>= fun o =>
      (compileObject o).map (·.code)

end Lsc.Compiler
