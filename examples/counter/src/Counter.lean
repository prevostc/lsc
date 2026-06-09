import Lsc.Prelude

open Lsc

@[lsc.error]
inductive CounterError where
  | arith : ArithError → CounterError

instance : LscError CounterError where
  arith := .arith

state! Counter where
  number : UInt256 @public
  paused : Bool

contract! Counter CounterError

@[lsc.external]
def pause : Counter Unit := do
  set .paused true

@[lsc.external]
def unpause : Counter Unit := do
  set .paused false

@[lsc.external]
def increment : Counter Unit := do
  unless (← get .paused) do
    let n ← get .number
    let n' ← n +? 1
    set .number n'
