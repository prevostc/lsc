import Lsc3.EVM.Lemmas
import Lsc3.Compile.Exec
import Lsc3.Compile.Encode
import Lsc3.Compile.Codegen

/-!
# `bytecode_ok` for the `get` body

`PUSH0 SLOAD PUSH0 MSTORE PUSH1 32 PUSH0 RETURN` is exactly what codegen emits for
`read count` returning a word. The dispatcher is separate; this file certifies the body
against storage slot 0, compositionally (no `rfl` through `MSTORE`).
-/

namespace Lsc3.Compile.GetBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Codegen

/-- Codegen of `Core.opTail (.load 0)` with a word return. -/
def code : List UInt8 := [0x5f, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]

def env : Env :=
  { code := code, calldata := [], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

/-- The body is the encoding of the assembly codegen emits for a word-valued `load 0`. -/
theorem code_eq_encode :
    encode [Asm.push 0, Asm.op .SLOAD, Asm.push 0, Asm.op .MSTORE,
            Asm.push 32, Asm.push 0, Asm.op .RETURN] = .ok code :=
  rfl

theorem memStore_packWord (m : Mem) (v : Nat) :
    (List.range 32).map (fun i => memGet (memStore m 0 v) (0 + i)) = packWord (wrap v) := by
  apply List.ext_getElem
  · simp [packWord_length]
  · intro i hi hi'
    have hi32 : i < 32 := by simpa [packWord_length] using hi'
    simp only [List.getElem_map, List.getElem_range]
    rw [memGet_memStore m 0 v i hi32, packWord_getElem (wrap v) i hi32]

private theorem length_lt_1024 {α} {xs : List α} {k : Nat}
    (hk : xs.length = k) (hbound : k < 1024 := by decide) : xs.length < 1024 :=
  hk ▸ hbound

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) :=
  decodeAt_push0_head _

theorem decode_pc1 :
    decodeAt code 1 = some ({ op := .SLOAD }, 2) :=
  decodeAt_of_drop rfl (decodeAt_sload_head _)

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 3) :=
  decodeAt_of_drop rfl (decodeAt_push0_head _)

theorem decode_pc3 :
    decodeAt code 3 = some ({ op := .MSTORE }, 4) :=
  decodeAt_of_drop rfl (decodeAt_mstore_head _)

theorem decode_pc4 :
    decodeAt code 4 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 6) := by
  have hdrop : code.drop 4 = 0x60 :: 0x20 :: code.drop 6 := rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x20 : UInt8) (code.drop 6))
  simpa [wrap] using h

theorem decode_pc6 :
    decodeAt code 6 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 7) :=
  decodeAt_of_drop rfl (decodeAt_push0_head _)

theorem decode_pc7 :
    decodeAt code 7 = some ({ op := .RETURN }, 8) :=
  decodeAt_of_drop rfl (decodeAt_return_head _)

theorem decode_suffix (pre : List UInt8) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt code pc = some (instr, next0)) :
    decodeAt (pre ++ code) (pre.length + pc) = some (instr, pre.length + next0) := by
  rw [decodeAt_append, hd]
  simp [Nat.add_comm]

/-- The `get` body, starting at `pre.length` in `pre ++ code`, returns storage slot 0
(modulo `2^256`). `pre = []` is the standalone program. -/
theorem getBody_ok_at (pre : List UInt8) (n : Nat) (env : Env) (s : State)
    (hcode : env.code = pre ++ code) (hpc : s.pc = pre.length)
    (hstack : s.stack = []) (hstor : s.storage 0 = n) :
    match run 16 env s with
    | some (Halt.ret data, _) => decodeWord data = wrap n
    | _ => False := by
  have d0 : decodeAt env.code s.pc =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, pre.length + 1) := by
    rw [hcode, hpc]
    simpa using decode_suffix pre decode_pc0
  have d1 : decodeAt env.code (pre.length + 1) =
      some ({ op := .SLOAD }, pre.length + 2) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc1
  have d2 : decodeAt env.code (pre.length + 2) =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, pre.length + 3) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc2
  have d3 : decodeAt env.code (pre.length + 3) =
      some ({ op := .MSTORE }, pre.length + 4) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc3
  have d4 : decodeAt env.code (pre.length + 4) =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, pre.length + 6) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc4
  have d6 : decodeAt env.code (pre.length + 6) =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, pre.length + 7) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc6
  have d7 : decodeAt env.code (pre.length + 7) =
      some ({ op := .RETURN }, pre.length + 8) := by
    rw [hcode]; simpa using decode_suffix pre decode_pc7
  have s0 : step env s =
      StepResult.next { s with stack := [0], pc := pre.length + 1 } := by
    have h := step_push env s 0 d0 (length_lt_1024 (k := 0) (by simp [hstack]))
    simpa [hstack] using h
  rw [run_of_next 15 env s _ s0]
  have s1 : step env { s with stack := [0], pc := pre.length + 1 } =
      StepResult.next { s with stack := [n], pc := pre.length + 2 } := by
    have h := step_sload env { s with stack := [0], pc := pre.length + 1 } 0 [] d1 rfl
      (length_lt_1024 (k := 0) rfl)
    simpa [hstor] using h
  rw [run_of_next 14 env _ _ s1]
  have s2 : step env { s with stack := [n], pc := pre.length + 2 } =
      StepResult.next { s with stack := [0, n], pc := pre.length + 3 } := by
    have h := step_push env { s with stack := [n], pc := pre.length + 2 } 0 d2
      (length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 13 env _ _ s2]
  have s3 : step env { s with stack := [0, n], pc := pre.length + 3 } =
      StepResult.next
        { s with mem := memStore s.mem 0 n, stack := [], pc := pre.length + 4 } :=
    step_mstore env { s with stack := [0, n], pc := pre.length + 3 } 0 n [] d3 rfl
  rw [run_of_next 12 env _ _ s3]
  have s4 :
      step env { s with mem := memStore s.mem 0 n, stack := [], pc := pre.length + 4 } =
        StepResult.next
          { s with mem := memStore s.mem 0 n, stack := [32], pc := pre.length + 6 } := by
    have h := step_push env
      { s with mem := memStore s.mem 0 n, stack := [], pc := pre.length + 4 } 32 d4
      (length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 11 env _ _ s4]
  have s6 :
      step env { s with mem := memStore s.mem 0 n, stack := [32], pc := pre.length + 6 } =
        StepResult.next
          { s with mem := memStore s.mem 0 n, stack := [0, 32], pc := pre.length + 7 } := by
    have h := step_push env
      { s with mem := memStore s.mem 0 n, stack := [32], pc := pre.length + 6 } 0 d6
      (length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 10 env _ _ s6]
  have s7 :
      step env { s with mem := memStore s.mem 0 n, stack := [0, 32], pc := pre.length + 7 } =
        StepResult.halt
          (.ret ((List.range 32).map fun i =>
            memGet (memStore s.mem 0 n) (0 + i)))
          { s with mem := memStore s.mem 0 n, stack := [0, 32], pc := pre.length + 7 } := by
    have h := step_return env
      { s with mem := memStore s.mem 0 n, stack := [0, 32], pc := pre.length + 7 }
      0 32 [] d7 rfl
    simpa using h
  rw [run_of_halt 9 env _ _ _ s7]
  rw [memStore_packWord]
  simp only
  exact decodeWord_packWord_of_lt (wrap_lt n)

/-- Codegen of `opTail (.load f)` is `PUSH f / SLOAD` plus a word `RETURN`. -/
theorem genCore_opTail_load (ctx : Lsc3.Compile.Ctx) (c : ContractDef) (f : Nat) :
    genCore ctx c (.opTail (.load f)) =
      .ok ([Asm.push f, Asm.op .SLOAD, Asm.push 0, Asm.op .MSTORE,
            Asm.push 32, Asm.push 0, Asm.op .RETURN], ctx) :=
  rfl

theorem genCore_opTail_load0 (ctx : Lsc3.Compile.Ctx) (c : ContractDef) :
    genCore ctx c (.opTail (.load 0)) =
      .ok ([Asm.push 0, Asm.op .SLOAD, Asm.push 0, Asm.op .MSTORE,
            Asm.push 32, Asm.push 0, Asm.op .RETURN], ctx) :=
  genCore_opTail_load ctx c 0

/-- Those instructions are exactly `code`. -/
theorem encode_genCore_load0 (ctx : Lsc3.Compile.Ctx) (c : ContractDef) :
    match genCore ctx c (.opTail (.load 0)) with
    | .ok (instrs, _) => encode instrs = .ok code
    | .error _ => False := by
  rw [genCore_opTail_load0]
  exact code_eq_encode

@[simp] theorem loadParams_zero : loadParams 0 = [] := rfl

end Lsc3.Compile.GetBody
