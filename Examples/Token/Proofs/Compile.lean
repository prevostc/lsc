import Lsc.Compiler.Bytecode
import Examples.Token.Contract

/-!
Token runtime compiles (`compileRuntime`: erase, else powdr spill).
-/

open Lsc.Compiler

#guard (compileRuntime Token.contract).isSome
