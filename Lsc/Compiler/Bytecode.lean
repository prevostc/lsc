import Lsc.Compiler.Yul
import YulEvmCompiler.Instr
import YulEvmCompiler.Compile
import YulEvmCompiler.ObjectCompile

/-!
# Yul → EVM bytecode via powdr

`compileRuntime` uses `YulEvmCompiler.compile` on the dispatcher block.
`compileDeploy` uses `compileObject` on the constructor+runtime object.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics.EVM (Op)

def compileRuntime (c : ContractDef) : Option (List UInt8) := do
  let b ← runtimeBlock c
  let is ← YulEvmCompiler.compile b
  return YulEvmCompiler.assembleBytes is

def compileDeploy (c : ContractDef) : Option (List UInt8) := do
  let o ← deployObject c
  let L ← YulEvmCompiler.compileObject o
  return L.code

end Lsc.Compiler
