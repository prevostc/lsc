import Lsc.Lang.Reify

/-!
# Counter — the smallest stateful contract

One `count` word. `increment` / `incrementBy` add; `decrement` saturates at
zero; `get` is the view. No external calls.
-/

open Lsc Lsc.Syntax

namespace Counter

structure Storage where
  count : Nat

inductive Event
  | Incremented (by_ : Nat)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

/-- Add one to `count`. -/
def increment : M Unit := do
  let c ← read count
  write count (← c +? 1)
  Tx.emit (.Incremented 1)

/-- Add `n` to `count`. Reverts when `n` is zero. -/
def incrementBy (n : Nat) : M Unit := do
  Tx.require (n ≠ 0) .Zero
  let c ← read count
  write count (← c +? n)
  Tx.emit (.Incremented n)

/-- Subtract one, saturating at zero. -/
def decrement : M Unit := do
  let c ← read count
  let c' ← if c = 0 then pure 0 else c -? 1
  write count c'

/-- Current `count`. -/
def get : M Nat := read count

end Counter

lsc_schema Counter
lsc_contract Counter increment incrementBy decrement get
