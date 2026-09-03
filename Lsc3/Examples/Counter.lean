import Lsc3.Reify

/-! # Counter — the smallest stateful contract -/

open Lsc3 Lsc3.Syntax

namespace Counter

structure Storage where
  count : Nat

inductive Event
  | Incremented (by_ : Nat)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  deriving DecidableEq, Repr

abbrev M := Tx Storage Event Error

def increment : M Unit := do
  let c ← read count
  write count (← c +? 1)
  Tx.emit (.Incremented 1)

def incrementBy (n : Nat) : M Unit := do
  Tx.require (n ≠ 0) .Zero
  let c ← read count
  write count (← c +? n)
  Tx.emit (.Incremented n)

/-- Saturating decrement, with an `if` returning a value. -/
def decrement : M Unit := do
  let c ← read count
  let c' ← if c = 0 then pure 0 else c -? 1
  write count c'

def get : M Nat := read count

end Counter

lsc_schema Counter
lsc_reify Counter.increment Counter.incrementBy Counter.decrement Counter.get
lsc_contract Counter increment incrementBy decrement get
