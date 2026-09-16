import Lsc.Lang.Core

/-!
Slice 1 internal-call unit tests: table CBV (`denoteTbl`) and callee
effect union (`effectsTbl`). `coreWF` lives in the compiler and is
tested in `Lsc.Compiler.CoreWFTests`.
-/

namespace Lsc.Lang.CoreTests

open Lsc

def dummyΓ : ContractSchema Unit Unit Unit Nat where
  st := {
    scalar := fun _ _ => 0
    scalarUpd := fun _ σ _ => σ
    map1 := fun _ _ _ => 0
    map1Upd := fun _ σ _ => σ
    map2 := fun _ _ _ _ => 0
    map2Upd := fun _ σ _ => σ
  }
  ev := ⟨fun _ _ => ()⟩
  err := ⟨fun n _ => n⟩

def idWord : Core .word := .ret (.word (.var 0))

def callId : Core .word := .callTail 0 [.var 0]

def twoEntry : List InternalDef :=
  [⟨"id", 1, .word, idWord⟩, ⟨"fwd", 1, .word, callId⟩]

def runTbl (fuel : Nat) (c : Core .word) (env : List Nat)
    (tbl : List InternalDef) : Option Nat :=
  match Tx.run (Core.denoteTbl dummyΓ fuel c env tbl) { sender := 0 }
      { self := (), ext := () } with
  | .ok (v, _) => some v
  | .error _ => none

-- Two-entry table: fwd(42) CBV-evaluates through id.
#guard runTbl 2 (.callTail 1 [.lit 42]) [] twoEntry == some 42

-- Empty fuel rejects the call.
#guard runTbl 0 (.callTail 1 [.lit 42]) [] twoEntry == none

def storeBody : Core .unit := .stmtTail (.store 0 (.lit 1))
def emitBody : Core .unit := .stmtTail (.emit 3 [])

def wrapStore : Core .unit := .letCall (t := .unit) 0 [] (.ret .unit)
def callEmit : Core .unit := .callTail (t := .unit) 0 []

-- effectsTbl unions the callee's writes into the caller.
#guard (Core.effectsTbl 1 wrapStore [⟨"w", 0, .unit, storeBody⟩]).writes == [0]

-- Callee emit is visible on the caller.
#guard (Core.effectsTbl 1 callEmit [⟨"e", 0, .unit, emitBody⟩]).emits == [3]

-- Structural effects (no table walk) ignores the callee.
#guard (Core.effects wrapStore).writes == []

def runExpand (c : Core .word) (env : List Nat)
    (tbl : List InternalDef) : Option Nat :=
  match Tx.run (Core.denote dummyΓ (Core.expand tbl c) env) { sender := 0 }
      { self := (), ext := () } with
  | .ok (v, _) => some v
  | .error _ => none

-- expand ∘ denote agrees with denoteTbl on the two-entry table.
#guard runExpand (.callTail 1 [.lit 42]) [] twoEntry == some 42
#guard runExpand (.callTail 1 [.lit 42]) [] twoEntry ==
  runTbl twoEntry.length (.callTail 1 [.lit 42]) [] twoEntry

-- No internal calls: expand leaves a call-free body call-free.
#guard Core.hasInternalCall (Core.expand twoEntry idWord) == false

end Lsc.Lang.CoreTests
