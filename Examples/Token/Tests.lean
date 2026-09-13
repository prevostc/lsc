import Examples.Token.Contract

/-!
Token smoke tests: constructor, transfer, approve, transferFrom (including
self-spend, which still requires allowance).
-/

open Lsc Token

namespace Token

def smokeOwner : Address := 1
def smokeTo : Address := 2
def smokeSpender : Address := 3

def smokeEmpty : World Storage ExtState Event where
  self := {
    owner := 0
    totalSupply := 0
    balances := fun _ => 0
    allowances := fun _ _ => 0 }
  ext := default

def smokeCtx : Ctx := { sender := smokeOwner }

end Token

open Token

#guard
  (match Tx.run (constructor smokeOwner 100) smokeCtx smokeEmpty with
    | .ok ((), w') =>
      (w'.self.totalSupply).raw == 100 &&
      (w'.self.balances smokeOwner).raw == 100 &&
      (w'.self.balances smokeTo).raw == 0
    | _ => false)

#guard
  (match Tx.run (constructor smokeOwner 100) smokeCtx smokeEmpty with
    | .ok ((), w0) =>
      (match Tx.run (transfer smokeTo 40) smokeCtx w0 with
        | .ok (true, w1) =>
          (w1.self.balances smokeOwner).raw == 60 &&
          (w1.self.balances smokeTo).raw == 40 &&
          (w1.self.totalSupply).raw == 100
        | _ => false)
    | _ => false)

#guard
  (match Tx.run (constructor smokeOwner 100) smokeCtx smokeEmpty with
    | .ok ((), w0) =>
      (match Tx.run (approve smokeSpender 25) smokeCtx w0 with
        | .ok (true, w1) =>
          (w1.self.allowances smokeOwner smokeSpender).raw == 25 &&
          (match Tx.run (transferFrom smokeOwner smokeTo 10)
              { sender := smokeSpender } w1 with
            | .ok (true, w2) =>
              (w2.self.balances smokeOwner).raw == 90 &&
              (w2.self.balances smokeTo).raw == 10 &&
              (w2.self.allowances smokeOwner smokeSpender).raw == 15
            | _ => false)
        | _ => false)
    | _ => false)

-- Self-spend still requires and decrements allowance.
#guard
  (match Tx.run (constructor smokeOwner 100) smokeCtx smokeEmpty with
    | .ok ((), w0) =>
      (match Tx.run (transferFrom smokeOwner smokeTo 1) smokeCtx w0 with
        | .error (.user .InsufficientAllowance) => true
        | _ => false)
    | _ => false)
