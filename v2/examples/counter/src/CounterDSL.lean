import LscV2.Prelude

/-!
  Counter contract written with the `contract … where` DSL macro.
  Compare with the hand-written `Counter.lean` to see the boilerplate
  that the macro generates automatically.
-/

open LscV2 LscV2.DSL LscV2.ContractElab

contract Counter where
  storage:
    number : Wei
    paused : Bool := false
    owner  : Address
  errors:
    | Paused
    | NotOwner
    | Overflow
  events:
    | Incremented(n : Wei)
    | Paused
    | Unpaused
  def increment : Tx :=
    do require (!$.paused) else revert Paused;
       let n ← $.number +? 1;
       $.number := n;
       emit Incremented(n);
  def pause : Tx :=
    do require (msg.sender == $.owner) else revert NotOwner;
       require (!$.paused) else revert Paused;
       $.paused := true;
       emit Paused();
  def unpause : Tx :=
    do require (msg.sender == $.owner) else revert NotOwner;
       require ($.paused) else revert Paused;
       $.paused := false;
       emit Unpaused();

-- Smoke-checks
#check Counter.CounterStorage
#check Counter.CounterError
#check Counter.CounterEvent
#check Counter.CounterM
#check Counter.increment
#check Counter.pause
#check Counter.unpause
