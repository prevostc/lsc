import Lsc.Prelude

open Lsc

error! CounterError where
  | IsPausedError
  | arith : ArithError → CounterError

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
  failWhen (← get .paused) .IsPausedError
  let n ← get .number
  let n' ← n +? 1
  set .number n'
