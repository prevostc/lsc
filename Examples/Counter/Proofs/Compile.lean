import Lsc.Compiler.Bytecode
import Examples.Counter.Contract

/-!
Counter runtime compiles (`compileRuntime`: erase, else powdr spill).
-/

open Lsc.Compiler

#guard (compileRuntime Counter.contract).isSome
