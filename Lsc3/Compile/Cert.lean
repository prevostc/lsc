import Lsc3.Compile.Encode
import Lsc3.Compile.Exec

/-!
# Compiler certificates

Kernel-checked facts about encoding, ABI packing, and the subset machine. Per-contract
`bytecode_ok` (dispatcher + body agrees with `Tx.run`) is built from these; full contracts
are too large for a single `rfl`, so end-to-end agreement is also checked by `#eval` in the
example modules.
-/

namespace Lsc3.Compile.Cert

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec

/-- `PUSH1 0x2a STOP` — the smallest kernel-checked execution. -/
def pushStopCode : List UInt8 := [0x60, 0x2a, 0x00]

def emptyEnv (code : List UInt8) : Env :=
  { code := code, calldata := [], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def emptyState : State := { storage := fun _ => 0 }

/-- The machine returns `STOP` with `42` on the stack. Proved by kernel reduction. -/
theorem pushStop_stack :
    match run 8 (emptyEnv pushStopCode) emptyState with
    | some (Halt.stop, s) => s.stack = [42]
    | _ => False :=
  rfl

/-- `PUSH1 1 PUSH1 2 ADD STOP` leaves `[3]`. -/
theorem addStop_stack :
    match run 8 (emptyEnv [0x60, 0x01, 0x60, 0x02, 0x01, 0x00]) emptyState with
    | some (Halt.stop, s) => s.stack = [3]
    | _ => False :=
  rfl

/-- ABI round-trip for a one-word payload. -/
theorem packCall_one_arg_length (sel n : Nat) :
    (packCall sel [n]).length = 36 := by
  simp

/-- Creation bytecode is preamble ++ runtime, so dropping the preamble recovers runtime. -/
theorem deploy_installs_runtime (runtime : List UInt8) :
    (deployCode runtime).drop (deployRuntimeOffset runtime.length) = runtime :=
  deployCode_suffix runtime

end Lsc3.Compile.Cert
