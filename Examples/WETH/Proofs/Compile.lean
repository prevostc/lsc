import Lsc.Compiler.Bytecode
import Examples.WETH.Contract

/-!
WETH runtime compiles (`compileRuntime`: erase, else powdr spill).
-/

open Lsc.Compiler

#guard (compileRuntime WETH.contract).isSome
