import Lsc.Compiler.Bytecode
import Examples.Cpamm.Contract

set_option linter.unusedSimpArgs false

/-!
CPAMM compile non-vacuity: the runtime block lowers through `compileBlock`
(erase or powdr spill).
-/

open Lsc.Compiler

/-- Runtime bytecode exists through `compileBlock` (erase or powdr spill). -/
def cpamm_compileBlock_some : Bool :=
  match runtimeBlock Cpamm.contract with
  | none => false
  | some rt => (compileBlock rt).isSome

#guard cpamm_compileBlock_some
