import Lsc.Lang.Reify
import Lsc.Compiler.Yul
import Lsc.Compiler.Bytecode
import EvmSemantics.EVM.StepF
import EvmSemantics.State.Account
import EvmSemantics.State.ExecutionEnv
import EvmSemantics.State.Substate

/-!
Selector-driven CALL/STATICCALL codegen (slice 3a). Stdlib cannot import the
compiler, so the `lsc_contract` toy lives here.
-/

set_option maxHeartbeats 8000000

open Lsc
open Lsc.Compiler
open EvmSemantics

namespace ExtCallToy

structure Storage where
  dummy : Nat
  deriving Fields

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Boom
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

def ping (target : Address) : M Word :=
  Tx.view (α := Word) target 0x70a08231 []

def poke (target : Address) : M Bool :=
  Tx.call (α := Bool) target 0x23b872dd []

end ExtCallToy

lsc_schema ExtCallToy
lsc_contract ExtCallToy ping poke

namespace Lsc.Compiler.ExtCallTests

open Lsc
open Lsc.Compiler

def transferFromSel : Nat := 0x23b872dd
def balanceOfSel : Nat := 0x70a08231

def pingFn : FnDef where
  name := "ping"
  decl := `ping
  kind := .view
  params := [{ name := "to", ty := .address }]
  ret := .word
  core := .opTail (.view (.var 0) balanceOfSel [] .word)

def pokeFn : FnDef where
  name := "poke"
  decl := `poke
  kind := .tx
  params := [{ name := "to", ty := .address }]
  ret := .word
  core := .opTail (.call (.var 0) transferFromSel [] .boolOpt)

def extCallContract : ContractDef where
  name := "ExtCallHand"
  fields := []
  functions := [pingFn, pokeFn]
  ctor := none
  events := []
  errors := []

def extYul : String :=
  match runtimeBlock extCallContract with
  | some b => printYul b
  | none => ""

#guard extYul.contains "call("
#guard extYul.contains "staticcall("
#guard extYul.contains (toString extCallGas)
#guard !extYul.contains "gas()"
#guard extYul.contains (toString transferFromSel)
#guard extYul.contains (toString balanceOfSel)
#guard extYul.contains "tload"
#guard !locks pingFn
#guard locks pokeFn

/-- Token-shaped: mutating, no outgoing call/view. Must not `tstore`. -/
def bumpFn : FnDef where
  name := "bump"
  decl := `bump
  kind := .tx
  params := []
  ret := .unit
  core := .stmtTail (.store 0 (.lit 1))

def transferLike : ContractDef where
  name := "TransferLike"
  fields := [{ name := "x", kind := .scalar, ty := .uint256 }]
  functions := [bumpFn]
  ctor := none
  events := []
  errors := []

def fnYul (c : ContractDef) (f : FnDef) : String :=
  match toYulFn c f with
  | some b => printYul b
  | none => ""

#guard (fnYul extCallContract pingFn).length > 0
#guard !(fnYul extCallContract pingFn).contains "tstore"
#guard (fnYul extCallContract pokeFn).contains "tstore"
#guard (fnYul transferLike bumpFn).length > 0
#guard !(fnYul transferLike bumpFn).contains "tstore"
#guard !locks bumpFn

#guard (compileRuntime extCallContract).isSome
#guard (compileRuntime ExtCallToy.contract).isSome
#guard (compileRuntime transferLike).isSome

/-- `PUSH1 42; PUSH1 0; MSTORE; PUSH1 0x20; PUSH1 0; RETURN` -/
def return42Code : ByteArray :=
  ByteArray.mk #[0x60, 42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]

/-- `STOP` — empty success for a mutating CALL (`boolOpt` treats empty returndata as ok). -/
def stopCode : ByteArray := ByteArray.mk #[0x00]

def toBA (bs : List UInt8) : ByteArray :=
  ByteArray.mk bs.toArray

/-- High addresses: `0x01..0x11` are precompiles on Osaka. -/
def calleeAddr : Nat := 0x1000
def selfAddr : Nat := 0x2000

def evmInit (code : ByteArray) (self callee : AccountAddress)
    (calleeCode : ByteArray) (calldata : ByteArray)
    (lockHeld : Bool := false) : EVM.State :=
  let env : ExecutionEnv := Inhabited.default
  let s : EVM.State := Inhabited.default
  let tstor := if lockHeld then Storage.empty.set (0 : UInt256) (1 : UInt256)
    else Storage.empty
  let selfAcc : Account := { Account.empty with code, tstorage := tstor }
  let calleeAcc : Account := { Account.empty with code := calleeCode }
  let accounts := AccountMap.empty.set self selfAcc |>.set callee calleeAcc
  { s with
      pc := 0
      stack := []
      execLength := 0
      halt := .Running
      callStack := []
      gasAvailable := 100000000
      accountMap := accounts
      substate := { Substate.empty with originalAccountMap := accounts }
      executionEnv := { env with
          address := self
          codeAddr := self
          code
          calldata
          fork := .Osaka
          permitStateMutation := true } }

def runEvm : Nat → EVM.State → EVM.State
  | 0, s => s
  | fuel + 1, s =>
    if s.isDone then s else runEvm fuel (EVM.stepF s)

/-- Compile `ping(callee)`, install a callee that returns the word 42, run. -/
def pingReturns42 : Bool :=
  match compileRuntime extCallContract with
  | none => false
  | some bytes =>
    let callee := AccountAddress.ofNat calleeAddr
    let self := AccountAddress.ofNat selfAddr
    let cd : ByteArray := ⟨(fnCalldata pingFn [calleeAddr]).toArray⟩
    let s := runEvm 5000 (evmInit (toBA bytes) self callee return42Code cd)
    s.isDone && s.halt == .Returned && s.hReturn.toList == wordBytes 42

#guard pingReturns42

/-- Held lock (`tstorage[0] = 1`) reverts every selector, including views. -/
def lockedReverts : Bool :=
  match compileRuntime extCallContract with
  | none => false
  | some bytes =>
    let callee := AccountAddress.ofNat calleeAddr
    let self := AccountAddress.ofNat selfAddr
    let cd : ByteArray := ⟨(fnCalldata pingFn [calleeAddr]).toArray⟩
    let s := runEvm 5000 (evmInit (toBA bytes) self callee return42Code cd true)
    s.isDone && s.halt == .Reverted

#guard lockedReverts

/-- `poke` (CALL) sets then clears: after a successful commit, slot 0 is 0. -/
def pokeClearsLock : Bool :=
  match compileRuntime extCallContract with
  | none => false
  | some bytes =>
    let callee := AccountAddress.ofNat calleeAddr
    let self := AccountAddress.ofNat selfAddr
    let cd : ByteArray := ⟨(fnCalldata pokeFn [calleeAddr]).toArray⟩
    let s := runEvm 8000 (evmInit (toBA bytes) self callee stopCode cd)
    let t0 := (s.accountMap self).tstorage (0 : UInt256)
    s.isDone && s.halt == .Returned && t0 == (0 : UInt256)

#guard pokeClearsLock

end Lsc.Compiler.ExtCallTests
