import Lsc.Lang.Reify
import Lsc.Compiler.Yul

/-!
`@[reentrant]` (slice 8C-3). Stdlib cannot import the compiler, so the
`lsc_contract` toys live here. No EVM interpreter: ExtCallTests already
runs CALL/lock bytecode.
-/

open Lsc
open Lsc.Syntax
open Lsc.Compiler

namespace ReentrantToy

structure Storage where
  dummy : Nat

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Boom
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

/-- Flash-loan entry point: the callee is expected to call back into this contract. -/
@[reentrant] def flashLoan (target : Address) : M Word :=
  Tx.call (α := Word) target 0x11111111 []

/-- Mutating sibling with an outgoing CALL: still takes the lock. -/
def poke (target : Address) : M Bool :=
  Tx.call (α := Bool) target 0x23b872dd []

end ReentrantToy

lsc_schema ReentrantToy
lsc_contract ReentrantToy flashLoan poke

namespace ReentrantBad

structure Storage where
  dummy : Nat

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Boom
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

/-- Store after CALL: rejected at `lsc_contract` unless `unsafe := true`. -/
@[reentrant] def bad (target : Address) : M Unit := do
  let _ ← Tx.call (α := Word) target 0x11111111 []
  write dummy 1

end ReentrantBad

lsc_schema ReentrantBad

/--
error: lsc_contract: `ReentrantBad.bad` is `@[reentrant]` but writes storage after an external call. Checks-effects-interactions is then the only protection; move stores before the call, or use `@[reentrant (unsafe := true)]`.
-/
#guard_msgs in
lsc_contract ReentrantBad bad

namespace Lsc.Compiler.ReentrantTests

open Lsc
open Lsc.Compiler

def fnYul (c : ContractDef) (f : FnDef) : String :=
  match toYulFn c f with
  | some b => printYul b
  | none => ""

def caseYul (c : ContractDef) (f : FnDef) : String :=
  match entryCase c f with
  | some (_, b) => printYul b
  | none => ""

def runtimeYul (c : ContractDef) : String :=
  match runtimeBlock c with
  | some b => printYul b
  | none => ""

#guard (runtimeBlock ReentrantToy.contract).isSome
#guard (runtimeYul ReentrantToy.contract).contains "tload"

#guard
  (match ReentrantToy.contract.functions with
    | [flash, poke] =>
        flash.reentrant && !flash.reentrantUnsafe && !poke.reentrant &&
          !locks flash && locks poke &&
          !(fnYul ReentrantToy.contract flash).contains "tstore" &&
          (fnYul ReentrantToy.contract poke).contains "tstore" &&
          !(caseYul ReentrantToy.contract flash).contains "tstore" &&
          (caseYul ReentrantToy.contract poke).contains "tstore"
    | _ => false)

#guard Core.storeAfterCall
  (Core.seq (.call (.var 0) 1 [] .none) (Core.stmtTail (.store 0 (.lit 1))))
#guard !Core.storeAfterCall
  (Core.seq (.store 0 (.lit 1)) (Core.stmtTail (.call (.var 0) 1 [] .none)))

end Lsc.Compiler.ReentrantTests
