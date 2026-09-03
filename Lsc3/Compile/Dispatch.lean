import Lsc3.EVM.Lemmas
import Lsc3.Compile.Exec

/-!
# Dispatcher prefix certificate

`PUSH0 CALLDATALOAD PUSH1 0xE0 SHR STOP` is the selector-load sequence every
`lsc_contract` dispatcher starts a branch with. This file checks it against
`packCall`, compositionally.
-/

namespace Lsc3.Compile.Dispatch

open Lsc3 Lsc3.EVM Lsc3.Compile.Exec

/-- Selector load, then `STOP` so `run` has a halt to inspect. -/
def code : List UInt8 := [0x5f, 0x35, 0x60, 0xE0, 0x1c, 0x00]

def env (sel : Nat) (args : List Nat) : Env :=
  { code := code, calldata := packCall sel args, address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 : State := { storage := fun _ => 0 }

private theorem length_lt_1024 {α} {xs : List α} {k : Nat}
    (hk : xs.length = k) (hbound : k < 1024 := by decide) : xs.length < 1024 :=
  hk ▸ hbound

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) :=
  decodeAt_push0_head _

theorem decode_pc1 :
    decodeAt code 1 = some ({ op := .CALLDATALOAD }, 2) :=
  decodeAt_of_drop rfl (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 4) := by
  have hdrop : code.drop 2 = 0x60 :: 0xE0 :: code.drop 4 := rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) (code.drop 4))
  simpa [wrap] using h

theorem decode_pc4 :
    decodeAt code 4 = some ({ op := .SHR }, 5) :=
  decodeAt_of_drop rfl (decodeAt_op_head .SHR _ rfl)

theorem decode_pc5 :
    decodeAt code 5 = some ({ op := .STOP }, 6) :=
  decodeAt_of_drop rfl (decodeAt_op_head .STOP _ rfl)

/-- Running the dispatcher prefix leaves `sel % 2^32` on the stack. -/
theorem loadSel_ok (sel : Nat) (args : List Nat) :
    match run 8 (env sel args) st0 with
    | some (Halt.stop, s) => s.stack = [sel % 2 ^ 32]
    | _ => False := by
  have s0 : step (env sel args) st0 =
      StepResult.next { st0 with stack := [0], pc := 1 } := by
    have h := step_push (env sel args) st0 0 decode_pc0
      (length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 7 (env sel args) st0 _ s0]
  have s1 : step (env sel args) { st0 with stack := [0], pc := 1 } =
      StepResult.next { st0 with stack := [calldataLoad (packCall sel args) 0], pc := 2 } := by
    have h := step_calldataload (env sel args) { st0 with stack := [0], pc := 1 } 0 []
      decode_pc1 rfl (length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using h
  rw [run_of_next 6 (env sel args) _ _ s1]
  have s2 :
      step (env sel args)
        { st0 with stack := [calldataLoad (packCall sel args) 0], pc := 2 } =
        StepResult.next
          { st0 with stack := [0xE0, calldataLoad (packCall sel args) 0], pc := 4 } := by
    have h := step_push (env sel args)
      { st0 with stack := [calldataLoad (packCall sel args) 0], pc := 2 } 0xE0 decode_pc2
      (length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 5 (env sel args) _ _ s2]
  have s4 :
      step (env sel args)
        { st0 with stack := [0xE0, calldataLoad (packCall sel args) 0], pc := 4 } =
        StepResult.next
          { st0 with stack := [shrW 0xE0 (calldataLoad (packCall sel args) 0)], pc := 5 } := by
    have h := step_shr (env sel args)
      { st0 with stack := [0xE0, calldataLoad (packCall sel args) 0], pc := 4 }
      0xE0 (calldataLoad (packCall sel args) 0) [] decode_pc4 rfl
      (length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 4 (env sel args) _ _ s4]
  have s5 :
      step (env sel args)
        { st0 with stack := [shrW 0xE0 (calldataLoad (packCall sel args) 0)], pc := 5 } =
        StepResult.halt .stop
          { st0 with stack := [shrW 0xE0 (calldataLoad (packCall sel args) 0)], pc := 5 } :=
    step_stop (env sel args)
      { st0 with stack := [shrW 0xE0 (calldataLoad (packCall sel args) 0)], pc := 5 }
      decode_pc5
  rw [run_of_halt 3 (env sel args) _ _ _ s5]
  simp [shrW_calldataLoad_packCall]

end Lsc3.Compile.Dispatch
