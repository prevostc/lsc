import Examples.Counter.Contract

/-!
Counter smoke tests.
-/

open Lsc Counter

def smokeCtx : Ctx := { sender := 1 }

def smokeW (n : Nat) : World :=
  { self := { count := n }, ext := default }

#guard
  (match Tx.run increment smokeCtx (smokeW 5) with
    | .ok ((), w') => w'.self.count == 6
    | _ => false)

#guard
  (match Tx.run (incrementBy 0) smokeCtx (smokeW 5) with
    | .error (.user .Zero) => true
    | _ => false)

#guard
  (match Tx.run decrement smokeCtx (smokeW 0) with
    | .ok ((), w') => w'.self.count == 0
    | _ => false)

#guard
  (match Tx.run Counter.get smokeCtx (smokeW 42) with
    | .ok (n, w') => n == 42 && w'.self.count == 42
    | _ => false)

namespace InternalReject

structure Storage where
  dummy : Nat
  deriving Fields

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Boom
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

@[internal] def hidden : M Unit := pure ()

end InternalReject

lsc_schema InternalReject

/--
error: ‘hidden’ is an internal function (no access control); expose it through an entrypoint of your own.
-/
#guard_msgs in
lsc_contract InternalReject hidden
