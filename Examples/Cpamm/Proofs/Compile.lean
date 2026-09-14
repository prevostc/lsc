import Lsc.Compiler.Bytecode
import Examples.Cpamm.Contract

/-!
CPAMM runtime compiles (`compileRuntime`: erase, else powdr spill).
Two external CALLs per mutating path and several live Amount locals
typically take the spill path.
-/

open Lsc.Compiler

#guard (compileRuntime Cpamm.contract).isSome
