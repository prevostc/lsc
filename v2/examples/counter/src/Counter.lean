import LscV2.Prelude
import LscV2.Compile.Yul
import LscV2.Compile.Bytecode
import LscV2.Lang.Syntax

open LscV2 LscV2.Compile

namespace Counter

structure CounterStorage where
  number : Wei := ⟨0⟩
  paused : Bool := false
  owner : Address := 0
  deriving Repr, LscV2.Deriving.ContractStorage

-- Required by `ContractM`'s default-storage handling.
instance : Inhabited CounterStorage where
  default := {}

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, LscV2.Deriving.ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, LscV2.Deriving.ContractEvent

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
