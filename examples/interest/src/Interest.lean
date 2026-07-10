import Lsc.Prelude
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lang.Syntax

open Lsc Lsc.Compile
open Lsc.Deriving

namespace Interest

structure InterestStorage where
  principal : Wad := ⟨0⟩
  rate : Wad := ⟨0⟩
  owner : Address := 0
  deriving Repr, ContractStorage

inductive InterestError where
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, ContractError

inductive InterestEvent where
  | Deposited (amount : Wad)
  | InterestAccrued (newPrincipal : Wad)
  | RateChanged (newRate : Wad)
  deriving Repr, DecidableEq, ContractEvent

tx deposit(amount : Wad) {
  let p = σ.principal +? amount;
  σ.principal = p;
  emit Deposited(amount);
}

tx accrueInterest {
  let interest = σ.principal ⸢*⸣? σ.rate;
  let p = σ.principal +? interest;
  σ.principal = p;
  emit InterestAccrued(p);
}

tx setRate(newRate : Wad) {
  require(msg.sender == σ.owner) else revert NotOwner();
  σ.rate = newRate;
  emit RateChanged(newRate);
}

/-! ## DSL wiring + compilation: `ContractDSL` instance, `ContractDef` + Yul/bytecode emission -/

-- Public functions, event topics, deploy step, and the `InterestM` monad abbreviation are all
-- inferred from the declarations above; see `derive_contract`'s docstring for defaults.
derive_contract "Interest" InterestStorage InterestError InterestEvent

-- Smoke-checks
#check Interest.InterestStorage
#check Interest.InterestError
#check Interest.InterestEvent
#check Interest.InterestM
#check (Interest.deposit : Wad → Stmt)
#check (Interest.accrueInterest : InterestM Unit)
#check (Interest.setRate : Wad → Stmt)
#check Interest.contractDef
#check Interest.bytecodeHex
#check Interest.deployHex

/-! ## Bytecode

`derive_contract` emits `bytecodeHex` (runtime) and `deployHex` (deploy transaction payload).
After `lake build Interest`, evaluate the lines below in this file to print the hex strings.
-/

example : Interest.bytecodeHex.startsWith "0x" ∧ Interest.bytecodeHex.length > 10 := by native_decide

#eval IO.println s!"Interest.bytecodeHex ({Interest.bytecodeHex.length} chars)"
#eval IO.println Interest.bytecodeHex

end Interest
