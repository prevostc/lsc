import Examples.Counter.Contract

/-!
Counter smoke tests.
-/

open Lsc Counter

def smokeCtx : Ctx := { sender := 1 }

def smokeW (n : Nat) : World Storage ExtState Event :=
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
