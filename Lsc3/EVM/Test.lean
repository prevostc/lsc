import Lsc3.EVM.Step

/-!
# Smoke tests for `Lsc3.EVM`
-/

namespace Lsc3.EVM.Test

open Lsc3.EVM

/-- `PUSH1 0x2a PUSH1 0 STOP` — push 42 and halt. -/
def pushStopCode : List UInt8 :=
  [0x60, 0x2a, 0x60, 0x00, 0x00]

def emptyEnv (code : List UInt8) : Env :=
  { code := code, calldata := [], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def emptyState : State :=
  { storage := fun _ => 0 }

#eval do
  let env := emptyEnv pushStopCode
  let s := emptyState
  match run 1000 env s with
  | none => IO.println "run: fuel exhausted"
  | some (Halt.stop, s') => IO.println s!"run: stop, stack top = {s'.stack.head?}"
  | some (h, _) => IO.println s!"run: halt {repr h}"

/-- `PUSH1 1 PUSH1 2 ADD STOP` — stack top should be 3. -/
def addCode : List UInt8 :=
  [0x60, 0x01, 0x60, 0x02, 0x01, 0x00]

#eval do
  let env := emptyEnv addCode
  let s := emptyState
  match run 1000 env s with
  | none => IO.println "add: fuel exhausted"
  | some (Halt.stop, s') => IO.println s!"add: stop, stack = {s'.stack}"
  | some (h, _) => IO.println s!"add: halt {repr h}"

end Lsc3.EVM.Test
