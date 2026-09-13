import YulSemantics.Dialect.EVMExec

/-!
# Fixed external-state type

`World.ext` for compiled contracts is this memory-blind projection: every
`EvmState` field except byte memory and `msize`. It is not a per-contract
user structure. The compiler's `ExtView` is this type.
-/

namespace Lsc

open YulSemantics.EVM

/-- Memory-blind observable state of the world a callee can see: persistent
and transient storage of the executing account, the frame/`ExecEnv` world
maps (balances, code, storage of every account, …), returndata, logs, the
self-destruct schedule, and the halt marker. Byte memory and `msize` are
omitted. -/
structure ExtState where
  storage : U256 → U256 := fun _ => 0
  transient : U256 → U256 := fun _ => 0
  env : ExecEnv := default
  returndata : List UInt8 := []
  logs : List LogEntry := []
  selfdestructs : List (U256 × Bool) := []
  halted : Option (HaltKind × List UInt8) := none

instance : Inhabited ExtState where
  default := {}

/-- Drop memory / `msize` from a Yul machine state. -/
def ExtState.ofState (st : EvmState) : ExtState where
  storage := st.storage
  transient := st.transient
  env := st.env
  returndata := st.returndata
  logs := st.logs
  selfdestructs := st.selfdestructs
  halted := st.halted

end Lsc
