import Examples.WETH.Contract
import Examples.WETH.Theorems

/-!
WETH smoke tests: deposit, withdraw, transfer, and `Exact.toSpec`
as the `IERC20.Spec` Vault quantifies over.
-/

open Lsc Lsc.Stdlib WETH

namespace WETH

def smokeWho : Address := 1
def smokeTo : Address := 2

def smokeEmpty : World Storage ExtState Event where
  self := { balances := fun _ => 0, allowances := fun _ _ => 0, totalSupply := 0 }
  ext := default

def smokeCtx : Ctx := { sender := smokeWho, value := 40 }

def acceptSend : Oracle ExtState where
  send _ _ x := some x

def smokeSend : World Storage ExtState Event :=
  { smokeEmpty with oracle := acceptSend }

end WETH

open WETH

/-- `Exact.toSpec` is the `IERC20.Spec` Vault/Cpamm quantify over. -/
example : IERC20.Spec WETH.impl := weth_exact.toSpec

#guard
  (match Tx.run depositTx smokeCtx smokeEmpty with
    | .ok ((), w') =>
      (w'.self.balances smokeWho).raw == 40 &&
      (w'.self.totalSupply).raw == 40
    | _ => false)

#guard
  (match Tx.run depositTx smokeCtx smokeSend with
    | .ok ((), w0) =>
      (match Tx.run (withdraw 10) smokeCtx w0 with
        | .ok ((), w1) =>
          (w1.self.balances smokeWho).raw == 30 &&
          (w1.self.totalSupply).raw == 30
        | _ => false)
    | _ => false)

#guard
  (match Tx.run depositTx smokeCtx smokeEmpty with
    | .ok ((), w0) =>
      (match Tx.run (transfer smokeTo 15) smokeCtx w0 with
        | .ok (true, w1) =>
          (w1.self.balances smokeWho).raw == 25 &&
          (w1.self.balances smokeTo).raw == 15
        | _ => false)
    | _ => false)

#guard
  (match Tx.run (withdraw 1) smokeCtx smokeEmpty with
    | .error (.user .InsufficientBalance) => true
    | .error (.arith .underflow) => true
    | _ => false)

#guard
  (match Tx.run depositTx smokeCtx smokeEmpty with
    | .ok ((), w0) =>
      (match Tx.run (withdraw 10) smokeCtx w0 with
        | .error (.user .TransferFailed) => true
        | _ => false)
    | _ => false)
