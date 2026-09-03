import Lsc3.EVM.Lemmas
import Lsc3.Compile.Exec

/-!
# Calldata-size check

Every `lsc_contract` dispatcher starts with `PUSH 4 / CALLDATASIZE / LT / JUMPI revert`.
This file certifies a PUSH1 encoding of that prefix: short calldata jumps; `packCall`
(always ≥ 4 bytes) falls through.
-/

namespace Lsc3.Compile.CalldataCheck

open Lsc3 Lsc3.EVM Lsc3.Compile.Exec

/-- `PUSH1 4 CALLDATASIZE LT PUSH1 8 JUMPI STOP JUMPDEST STOP` -/
def dest : Nat := 8

def code : List UInt8 := [0x60, 4, 0x36, 0x10, 0x60, 8, 0x57, 0x00, 0x5b, 0x00]

def env (data : List UInt8) : Env :=
  { code := code, calldata := data, address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 : State := { storage := fun _ => 0 }

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 2) := by
  have h := decodeAt_push1_head (4 : UInt8) (code.drop 2)
  simpa [wrap] using h

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .CALLDATASIZE }, 3) := by
  have h : code.drop 2 = Opcode.toByte .CALLDATASIZE :: code.drop 3 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATASIZE _ rfl)

theorem decode_pc3 :
    decodeAt code 3 = some ({ op := .LT }, 4) := by
  have h : code.drop 3 = Opcode.toByte .LT :: code.drop 4 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .LT _ rfl)

theorem decode_pc4 :
    decodeAt code 4 = some ({ op := .PUSH ⟨1, by decide⟩, imm := dest }, 6) := by
  have hdrop : code.drop 4 = 0x60 :: 8 :: code.drop 6 := rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (8 : UInt8) (code.drop 6))
  simpa [wrap, dest] using h

theorem decode_pc6 :
    decodeAt code 6 = some ({ op := .JUMPI }, 7) := by
  have h : code.drop 6 = Opcode.toByte .JUMPI :: code.drop 7 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc7 :
    decodeAt code 7 = some ({ op := .STOP }, 8) := by
  have h : code.drop 7 = Opcode.toByte .STOP :: code.drop 8 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .STOP _ rfl)

theorem decode_pc8 :
    decodeAt code 8 = some ({ op := .JUMPDEST }, 9) := by
  have h : code.drop 8 = Opcode.toByte .JUMPDEST :: code.drop 9 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem decode_pc9 :
    decodeAt code 9 = some ({ op := .STOP }, 10) := by
  have h : code.drop 9 = Opcode.toByte .STOP :: code.drop 10 := rfl
  exact decodeAt_of_drop h (decodeAt_op_head .STOP _ rfl)

theorem isJumpDest_8 : isJumpDest code dest = true :=
  isJumpDest_of_decode decode_pc8

theorem ltW_ge_four {n : Nat} (h : 4 ≤ n) : ltW n 4 = 0 := by
  simp [ltW, Nat.not_lt.mpr h]

theorem ltW_lt_four {n : Nat} (h : n < 4) : ltW n 4 = 1 := by
  simp [ltW, h]

/-- Calldata of at least 4 bytes falls through to `STOP` at PC 7. -/
theorem calldataCheck_ok {data : List UInt8} (hge : 4 ≤ data.length) :
    match run 16 (env data) st0 with
    | some (Halt.stop, s) => s.pc = 7
    | _ => False := by
  let e := env data
  have s0 : step e st0 =
      StepResult.next { st0 with stack := [4], pc := 2 } := by
    have h := step_push e st0 4 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 15 e st0 _ s0]
  have s2 : step e { st0 with stack := [4], pc := 2 } =
      StepResult.next { st0 with stack := [data.length, 4], pc := 3 } := by
    have h := step_calldatasize e { st0 with stack := [4], pc := 2 } decode_pc2
      (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using h
  rw [run_of_next 14 e _ _ s2]
  have s3 : step e { st0 with stack := [data.length, 4], pc := 3 } =
      StepResult.next { st0 with stack := [0], pc := 4 } := by
    have h := step_lt e { st0 with stack := [data.length, 4], pc := 3 }
      data.length 4 [] decode_pc3 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [ltW_ge_four hge] using h
  rw [run_of_next 13 e _ _ s3]
  have s4 : step e { st0 with stack := [0], pc := 4 } =
      StepResult.next { st0 with stack := [dest, 0], pc := 6 } := by
    have h := step_push e { st0 with stack := [0], pc := 4 } dest decode_pc4
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 12 e _ _ s4]
  have s6 : step e { st0 with stack := [dest, 0], pc := 6 } =
      StepResult.next { st0 with stack := [], pc := 7 } := by
    have h := step_jumpi_zero e { st0 with stack := [dest, 0], pc := 6 } dest []
      decode_pc6 rfl
    simpa using h
  rw [run_of_next 11 e _ _ s6]
  have s7 : step e { st0 with stack := [], pc := 7 } =
      StepResult.halt .stop { st0 with stack := [], pc := 7 } :=
    step_stop e { st0 with stack := [], pc := 7 } decode_pc7
  rw [run_of_halt 10 e _ _ _ s7]

/-- Fewer than 4 calldata bytes jump to the revert `JUMPDEST` and `STOP` (PC 9). -/
theorem calldataCheck_short {data : List UInt8} (hlt : data.length < 4) :
    match run 16 (env data) st0 with
    | some (Halt.stop, s) => s.pc = 9
    | _ => False := by
  let e := env data
  have s0 : step e st0 =
      StepResult.next { st0 with stack := [4], pc := 2 } := by
    have h := step_push e st0 4 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 15 e st0 _ s0]
  have s2 : step e { st0 with stack := [4], pc := 2 } =
      StepResult.next { st0 with stack := [data.length, 4], pc := 3 } := by
    have h := step_calldatasize e { st0 with stack := [4], pc := 2 } decode_pc2
      (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using h
  rw [run_of_next 14 e _ _ s2]
  have s3 : step e { st0 with stack := [data.length, 4], pc := 3 } =
      StepResult.next { st0 with stack := [1], pc := 4 } := by
    have h := step_lt e { st0 with stack := [data.length, 4], pc := 3 }
      data.length 4 [] decode_pc3 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [ltW_lt_four hlt] using h
  rw [run_of_next 13 e _ _ s3]
  have s4 : step e { st0 with stack := [1], pc := 4 } =
      StepResult.next { st0 with stack := [dest, 1], pc := 6 } := by
    have h := step_push e { st0 with stack := [1], pc := 4 } dest decode_pc4
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 12 e _ _ s4]
  have s6 : step e { st0 with stack := [dest, 1], pc := 6 } =
      StepResult.next { st0 with stack := [], pc := dest } := by
    have h := step_jumpi_nz e { st0 with stack := [dest, 1], pc := 6 } dest 1 []
      decode_pc6 rfl (by decide) (by simpa [env] using isJumpDest_8)
    simpa using h
  rw [run_of_next 11 e _ _ s6]
  have s8 : step e { st0 with stack := [], pc := dest } =
      StepResult.next { st0 with stack := [], pc := 9 } := by
    have hdec : decodeAt e.code dest = some ({ op := .JUMPDEST }, 9) := by
      simpa [env, dest] using decode_pc8
    exact step_jumpdest e { st0 with stack := [], pc := dest } hdec
  rw [run_of_next 10 e _ _ s8]
  have s9 : step e { st0 with stack := [], pc := 9 } =
      StepResult.halt .stop { st0 with stack := [], pc := 9 } :=
    step_stop e { st0 with stack := [], pc := 9 } decode_pc9
  rw [run_of_halt 9 e _ _ _ s9]

end Lsc3.Compile.CalldataCheck
