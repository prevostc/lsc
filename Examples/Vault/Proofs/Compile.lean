import Lsc.Compiler.Bytecode
import Examples.Vault.Contract

/-!
Vault runtime compiles (`compileRuntime`: erase, else powdr spill).
External CALLs and several live Amount locals often take the spill path.
-/

open Lsc.Compiler

#guard (compileRuntime Vault.contract).isSome
