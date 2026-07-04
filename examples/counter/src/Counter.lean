import Lsc.Prelude
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lang.Syntax

open Lsc Lsc.Compile
open Lsc.Deriving

namespace Counter

structure CounterStorage where
  number : Wei := ⟨0⟩
  paused : Bool := false
  owner : Address := 0
  deriving Repr, ContractStorage

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, ContractEvent

tx increment {
  require(!σ.paused) else revert Paused();
  let n = σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

tx pause {
  require(msg.sender == σ.owner) else revert NotOwner();
  require(!σ.paused) else revert Paused();
  σ.paused = true;
  emit Paused();
}

tx unpause {
  require(msg.sender == σ.owner) else revert NotOwner();
  require(σ.paused) else revert Paused();
  σ.paused = false;
  emit Unpaused();
}

/-! ## DSL wiring + compilation: `ContractDSL` instance, `ContractDef` + Yul/bytecode emission -/

-- Public functions, event topics, deploy step, and the `CounterM` monad abbreviation are all
-- inferred from the declarations above; see `derive_contract`'s docstring for defaults.
derive_contract "Counter" CounterStorage CounterError CounterEvent

-- Smoke-checks
#check Counter.CounterStorage
#check Counter.CounterError
#check Counter.CounterEvent
#check Counter.CounterM
#check (Counter.increment : CounterM Unit)
#check (Counter.pause : CounterM Unit)
#check (Counter.unpause : CounterM Unit)
#check Counter.contractDef
#check Counter.bytecodeHex
#check Counter.deployHex

end Counter
