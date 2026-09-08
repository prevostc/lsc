import Lsc.Compiler.Bytecode
import Examples.FeeAmm.Contract

set_option linter.unusedSimpArgs false

/-!
FeeAmm compile non-vacuity: the runtime block lowers through `compileBlock`
(erase or powdr spill).
-/

open Lsc.Compiler

/-- Runtime bytecode exists through `compileBlock` (erase or powdr spill). -/
def feeAmm_compileBlock_some : Bool :=
  match runtimeBlock FeeAmm.contract with
  | none => false
  | some rt => (compileBlock rt).isSome

#guard feeAmm_compileBlock_some
