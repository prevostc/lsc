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

/-- `PUSH1 5 PUSH1 3 SWAP1 SUB STOP` — Yellow Paper SUB is top − second, so 5 − 3. -/
def subCode : List UInt8 :=
  [0x60, 0x05, 0x60, 0x03, 0x90, 0x03, 0x00]

#eval do
  let env := emptyEnv subCode
  match run 1000 env emptyState with
  | some (Halt.stop, s') => IO.println s!"sub: stop, stack = {s'.stack}"
  | none => IO.println "sub: fuel exhausted"
  | some (h, _) => IO.println s!"sub: halt {repr h}"

/-- `PUSH1 42 PUSH1 0 MSTORE PUSH1 32 PUSH1 0 RETURN` — return word 42. -/
def returnCode : List UInt8 :=
  [0x60, 0x2a, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]

#eval do
  let env := emptyEnv returnCode
  match run 1000 env emptyState with
  | some (Halt.ret data, _) =>
    let word : Nat := (List.range (min 32 data.length)).foldl (fun acc i =>
      acc * 256 + UInt8.toNat data[i]!) 0
    IO.println s!"return: word = {word}"
  | none => IO.println "return: fuel exhausted"
  | some (h, _) => IO.println s!"return: halt {repr h}"
