import Lsc.Lang.Reify
import Lsc.Compiler.Yul
import Lsc.Compiler.Bytecode
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect

/-!
Generic compiler guards that must not live under `Examples/` (the compiler
cannot import examples). Toy contract, constructor `codecopy`/`codesize`,
and `rawSelectedWF`.
-/

set_option maxHeartbeats 8000000

open Lsc
open Lsc.Syntax
open Lsc.Compiler
open YulEvmCompiler.Optimizer.MemorySpillSelect

namespace YulTestsToy

structure Storage where
  dummy : Nat

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Unused
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

/-- Write the dummy word. -/
def constructor (n : Nat) : M Unit := do
  write dummy n

/-- Read the dummy word. -/
def ping : M Nat := read dummy

end YulTestsToy

lsc_schema YulTestsToy
lsc_contract YulTestsToy constructor ping

namespace Lsc.Compiler.YulTests

open Lsc.Compiler

/-- Constructor Yul of the toy (args from the init-code suffix). -/
def toyCtorYul : Option YBlock :=
  Option.bind YulTestsToy.contract.ctor (toYulCtor YulTestsToy.contract)

def toyCtorHas (needle : String) : Bool :=
  match toyCtorYul with
  | none => false
  | some b => decide (1 < (String.splitOn (printYul b) needle).length)

/-- Names that appear more than once in any raw-runtime frame. -/
def rawDupNames (c : ContractDef) : List String :=
  match runtimeBlock c with
  | none => ["runtimeBlock none"]
  | some b =>
    (frames b).flatMap fun fr =>
      (frameNames fr).filter fun n => (frameNames fr).count n ≠ 1

/-- `selectedWF` on the raw runtime, as `spillBlock?` checks it. -/
def rawSelectedWF (c : ContractDef) : Bool :=
  match runtimeBlock c with
  | none => false
  | some b =>
    match spillRuntime? b with
    | some _ => true
    | none =>
      match selectSpills b with
      | none => selectedWF (frames b) []
      | some sel => selectedWF (frames b) sel

#guard (runtimeBlock YulTestsToy.contract).isSome
#guard (compileRuntime YulTestsToy.contract).isSome
#guard (deployObject YulTestsToy.contract).isSome
#guard (compileDeploy YulTestsToy.contract).isSome
#guard toyCtorHas "codecopy"
#guard toyCtorHas "codesize"
#guard rawSelectedWF YulTestsToy.contract

end Lsc.Compiler.YulTests
