import Lsc.Compiler.Bytecode
import Examples.WNative.Contract

/-!
WNative runtime compiles (`compileRuntime`: erase, else powdr spill).
-/

open Lsc.Compiler

#guard (compileRuntime WNative.contract).isSome
