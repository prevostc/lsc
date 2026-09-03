import Lsc3.Compile.GetInc
import Lsc3.Compile.GetBody
import Lsc3.Compile.Jump

/-!
# Matching-selector `get` on the two-function compiler

`getInc_get_hit` — apply it; do not instantiate at `selectorOf "get" []`.
-/

namespace Lsc3.Compile.GetInc

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Jump
open Lsc3.Compile.DispatchGet (push4Bytes decodeAt_push4)

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_spine (gSel iSel : Nat) :
    code gSel iSel =
      checkBytes ++ (branchGetBytes gSel ++ (branchIncBytes iSel ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))))) := by
  simp [code, List.append_assoc]

theorem code_drop8 (gSel iSel : Nat) :
    (code gSel iSel).drop 8 =
      branchGetBytes gSel ++ (branchIncBytes iSel ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))) := by
  rw [code_spine, List.drop_left' checkBytes_length]

theorem code_drop13 (gSel iSel : Nat) :
    (code gSel iSel).drop 13 =
      emitPush4 gSel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (branchIncBytes iSel ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
              ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))))))) := by
  rw [show 13 = 8 + 5 from rfl, drop_add, code_drop8]
  simp [branchGetBytes, List.append_assoc]
  try rw [List.drop_left' GetContract.loadSelBytes_length]

theorem code_drop18 (gSel iSel : Nat) :
    (code gSel iSel).drop 18 =
      [Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (branchIncBytes iSel ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
              ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))))) := by
  rw [show 18 = 13 + 5 from rfl, drop_add, code_drop13, List.drop_left' (emitPush4_length gSel)]

theorem code_drop19 (gSel iSel : Nat) :
    (code gSel iSel).drop 19 =
      emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (branchIncBytes iSel ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))))) := by
  rw [show 19 = 18 + 1 from rfl, drop_add, code_drop18]; rfl

theorem code_drop22 (gSel iSel : Nat) :
    (code gSel iSel).drop 22 =
      [Opcode.toByte .JUMPI] ++ (branchIncBytes iSel ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))) := by
  rw [show 22 = 19 + 3 from rfl, drop_add, code_drop19, List.drop_left' (emitPush2_length getPc)]

theorem code_drop23 (gSel iSel : Nat) :
    (code gSel iSel).drop 23 =
      branchIncBytes iSel ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))) := by
  rw [show 23 = 22 + 1 from rfl, drop_add, code_drop22]; rfl

theorem code_after4 (gSel iSel : Nat) :
    code gSel iSel =
      [0x60, 4, 0x36, 0x10] ++
        (emitPush2 revPc ++ Opcode.toByte .JUMPI :: (code gSel iSel).drop 8) := by
  rw [code_drop8]
  simp [code, checkBytes, branchGetBytes, List.append_assoc]

theorem code_drop4 (gSel iSel : Nat) :
    (code gSel iSel).drop 4 =
      emitPush2 revPc ++ (Opcode.toByte .JUMPI :: (code gSel iSel).drop 8) := by
  rw [code_after4]
  exact List.drop_left' (by decide : ([0x60, 4, 0x36, 0x10] : List UInt8).length = 4)

theorem code_drop7 (gSel iSel : Nat) :
    (code gSel iSel).drop 7 = Opcode.toByte .JUMPI :: (code gSel iSel).drop 8 := by
  rw [show 7 = 4 + 3 from rfl, drop_add, code_drop4]
  exact List.drop_left' (emitPush2_length revPc)

theorem code_drop42 (gSel iSel : Nat) :
    (code gSel iSel).drop 42 =
      [Opcode.toByte .JUMPDEST] ++ (revertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
          ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))) := by
  rw [show 42 = 8 + 34 from rfl, drop_add, code_drop8]
  rw [show 34 = 15 + 19 from rfl, drop_add]
  rw [List.drop_left' (branchGetBytes_length gSel)]
  rw [show 19 = 15 + 4 from rfl, drop_add]
  rw [List.drop_left' (branchIncBytes_length iSel)]
  rw [List.drop_left' fallBytes_length]

theorem code_drop43 (gSel iSel : Nat) :
    (code gSel iSel).drop 43 =
      revertBytes ++ ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
        ([Opcode.toByte .JUMPDEST] ++ bodyBytes))) := by
  rw [show 43 = 42 + 1 from rfl, drop_add, code_drop42]; rfl

theorem code_drop82 (gSel iSel : Nat) :
    (code gSel iSel).drop 82 =
      [Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
        ([Opcode.toByte .JUMPDEST] ++ bodyBytes)) := by
  rw [show 82 = 43 + 39 from rfl, drop_add, code_drop43, List.drop_left' GetContract.revertBytes_length]

theorem code_drop83 (gSel iSel : Nat) :
    (code gSel iSel).drop 83 = GetBody.code ++ ([Opcode.toByte .JUMPDEST] ++ bodyBytes) := by
  rw [show 83 = 82 + 1 from rfl, drop_add, code_drop82]; rfl

def getPre (gSel iSel : Nat) : List UInt8 :=
  checkBytes ++ branchGetBytes gSel ++ branchIncBytes iSel ++ fallBytes ++
    [Opcode.toByte .JUMPDEST] ++ revertBytes ++ [Opcode.toByte .JUMPDEST]

@[simp] theorem getPre_length (gSel iSel : Nat) : (getPre gSel iSel).length = 83 := by
  simp [getPre]

theorem code_getPre (gSel iSel : Nat) :
    code gSel iSel = getPre gSel iSel ++ GetBody.code ++ ([Opcode.toByte .JUMPDEST] ++ bodyBytes) := by
  simp [code, getPre, List.append_assoc]

theorem emitPush4_eq_push4 (sel : Nat) : emitPush4 sel = push4Bytes sel := rfl

theorem decode_pc0 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 0 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 2) := by
  have h : (code gSel iSel).drop 0 = 0x60 :: 4 :: (code gSel iSel).drop 2 := by
    simp [code, checkBytes]
  have h' := decodeAt_of_drop h (decodeAt_push1_head (4 : UInt8) ((code gSel iSel).drop 2))
  simpa [wrap] using h'

theorem decode_pc2 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 2 = some ({ op := .CALLDATASIZE }, 3) := by
  have h : (code gSel iSel).drop 2 = Opcode.toByte .CALLDATASIZE :: (code gSel iSel).drop 3 := by
    simp [code, checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATASIZE _ rfl)

theorem decode_pc3 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 3 = some ({ op := .LT }, 4) := by
  have h : (code gSel iSel).drop 3 = Opcode.toByte .LT :: (code gSel iSel).drop 4 := by
    simp [code, checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .LT _ rfl)

theorem decode_pc4 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 4 = some ({ op := .PUSH ⟨2, by decide⟩, imm := revPc }, 7) := by
  have hdrop : (code gSel iSel).drop 4 = emitPush2 revPc ++ (code gSel iSel).drop 7 := by
    rw [code_drop4, code_drop7]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 revPc _)
  simpa [revPc_mod] using h

theorem decode_pc7 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 7 = some ({ op := .JUMPI }, 8) := by
  have h : (code gSel iSel).drop 7 = Opcode.toByte .JUMPI :: (code gSel iSel).drop 8 :=
    code_drop7 gSel iSel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc8 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 8 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 9) := by
  have h : (code gSel iSel).drop 8 = 0x5f :: (code gSel iSel).drop 9 := by
    rw [show 9 = 8 + 1 from rfl, drop_add, code_drop8]
    simp [branchGetBytes, loadSelBytes, GetContract.loadSelBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc9 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 9 = some ({ op := .CALLDATALOAD }, 10) := by
  have h : (code gSel iSel).drop 9 = Opcode.toByte .CALLDATALOAD :: (code gSel iSel).drop 10 := by
    rw [show 9 = 8 + 1 from rfl, show 10 = 8 + 2 from rfl, drop_add, drop_add, code_drop8]
    simp [branchGetBytes, loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc10 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 10 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 12) := by
  have hdrop : (code gSel iSel).drop 10 = 0x60 :: 0xE0 :: (code gSel iSel).drop 12 := by
    rw [show 10 = 8 + 2 from rfl, show 12 = 8 + 4 from rfl, drop_add, drop_add, code_drop8]
    simp [branchGetBytes, loadSelBytes, GetContract.loadSelBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) ((code gSel iSel).drop 12))
  simpa [wrap] using h

theorem decode_pc12 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 12 = some ({ op := .SHR }, 13) := by
  have h : (code gSel iSel).drop 12 = Opcode.toByte .SHR :: (code gSel iSel).drop 13 := by
    rw [show 12 = 8 + 4 from rfl, drop_add, code_drop8, code_drop13]
    simp [branchGetBytes, loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .SHR _ rfl)

theorem decode_pc13 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 13 =
      some ({ op := .PUSH ⟨4, by decide⟩, imm := gSel % 2 ^ 32 }, 18) := by
  have hdrop : (code gSel iSel).drop 13 = emitPush4 gSel ++ (code gSel iSel).drop 18 := by
    rw [code_drop13, code_drop18]
  rw [emitPush4_eq_push4] at hdrop
  have h := decodeAt_of_drop hdrop (decodeAt_push4 gSel _)
  simpa using h

theorem decode_pc18 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 18 = some ({ op := .EQ }, 19) := by
  have h : (code gSel iSel).drop 18 = Opcode.toByte .EQ :: (code gSel iSel).drop 19 := by
    rw [code_drop18, code_drop19]; rfl
  exact decodeAt_of_drop h (decodeAt_op_head .EQ _ rfl)

theorem decode_pc19 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := getPc }, 22) := by
  have hdrop : (code gSel iSel).drop 19 = emitPush2 getPc ++ (code gSel iSel).drop 22 := by
    rw [code_drop19, code_drop22]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 getPc _)
  simpa [getPc_mod] using h

theorem decode_pc22 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 22 = some ({ op := .JUMPI }, 23) := by
  have h : (code gSel iSel).drop 22 = Opcode.toByte .JUMPI :: (code gSel iSel).drop 23 :=
    code_drop22 gSel iSel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc82 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 82 = some ({ op := .JUMPDEST }, 83) := by
  have h : (code gSel iSel).drop 82 = Opcode.toByte .JUMPDEST ::
      (GetBody.code ++ ([Opcode.toByte .JUMPDEST] ++ bodyBytes)) := by
    rw [code_drop82]; rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem decode_pc83 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 83 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 84) := by
  have h : (code gSel iSel).drop 83 = 0x5f :: (code gSel iSel).drop 84 := by
    rw [code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc84 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 84 = some ({ op := .SLOAD }, 85) := by
  have h : (code gSel iSel).drop 84 = Opcode.toByte .SLOAD :: (code gSel iSel).drop 85 := by
    rw [show 84 = 83 + 1 from rfl, drop_add, code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem decode_pc85 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 85 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 86) := by
  have h : (code gSel iSel).drop 85 = 0x5f :: (code gSel iSel).drop 86 := by
    rw [show 85 = 83 + 2 from rfl, drop_add, code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc86 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 86 = some ({ op := .MSTORE }, 87) := by
  have h : (code gSel iSel).drop 86 = Opcode.toByte .MSTORE :: (code gSel iSel).drop 87 := by
    rw [show 86 = 83 + 3 from rfl, drop_add, code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc87 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 87 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 89) := by
  have hdrop : (code gSel iSel).drop 87 = 0x60 :: 0x20 :: (code gSel iSel).drop 89 := by
    rw [show 87 = 83 + 4 from rfl, drop_add, code_drop83]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x20 : UInt8) ((code gSel iSel).drop 89))
  simpa [wrap] using h

theorem decode_pc89 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 89 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 90) := by
  have h : (code gSel iSel).drop 89 = 0x5f :: (code gSel iSel).drop 90 := by
    rw [show 89 = 83 + 6 from rfl, drop_add, code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc90 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 90 = some ({ op := .RETURN }, 91) := by
  have h : (code gSel iSel).drop 90 = Opcode.toByte .RETURN :: (code gSel iSel).drop 91 := by
    rw [show 90 = 83 + 7 from rfl, drop_add, code_drop83]; rfl
  exact decodeAt_of_drop h (decodeAt_return_head _)

theorem isJumpDest_get (gSel iSel : Nat) : isJumpDest (code gSel iSel) getPc = true := by
  simpa [getPc] using isJumpDest_of_decode (decode_pc82 gSel iSel)

def env (gSel iSel : Nat) (args : List Nat) : Env :=
  { code := code gSel iSel, calldata := packCall gSel args, address := 0, caller := 0,
    callvalue := 0, timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

/-- Matching `get` selector returns storage slot 0. -/
theorem getInc_get_hit (gSel iSel n : Nat) :
    match run 32 (env gSel iSel []) (st0 n) with
    | some (Halt.ret data, _) => decodeWord data = wrap n
    | _ => False := by
  let e := env gSel iSel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have h := step_push e (st0 n) 4 (decode_pc0 gSel iSel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 31 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have h := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 30 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have h := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at h
    exact h
  rw [run_of_next 29 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [revPc, 0], pc := 7 } := by
    have h := step_push e { st0 n with stack := [0], pc := 4 } revPc (decode_pc4 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 28 e _ _ s4]
  have s7 : step e { st0 n with stack := [revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have h := step_jumpi_zero e { st0 n with stack := [revPc, 0], pc := 7 } revPc []
      (decode_pc7 gSel iSel) rfl
    simpa using h
  rw [run_of_next 27 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have h := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 gSel iSel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 26 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall gSel []) 0], pc := 10 } := by
    have h := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using h
  rw [run_of_next 25 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall gSel []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall gSel []) 0], pc := 12 } := by
    have h := step_push e
      { st0 n with stack := [calldataLoad (packCall gSel []) 0], pc := 10 } 0xE0
      (decode_pc10 gSel iSel) (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 24 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall gSel []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall gSel []) 0)], pc := 13 } := by
    have h := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall gSel []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall gSel []) 0) [] (decode_pc12 gSel iSel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 23 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall gSel []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall gSel []) 0)],
            pc := 18 } := by
    have h := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall gSel []) 0)], pc := 13 }
      (gSel % 2 ^ 32) (decode_pc13 gSel iSel) (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 22 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall gSel []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [1], pc := 19 } := by
    have h := step_eq e
      { st0 n with
        stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall gSel []) 0)], pc := 18 }
      (gSel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall gSel []) 0)) []
      (decode_pc18 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at h ⊢
    exact h
  rw [run_of_next 21 e _ _ s18]
  have s19 : step e { st0 n with stack := [1], pc := 19 } =
      StepResult.next { st0 n with stack := [getPc, 1], pc := 22 } := by
    have h := step_push e { st0 n with stack := [1], pc := 19 } getPc (decode_pc19 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 20 e _ _ s19]
  have s22 : step e { st0 n with stack := [getPc, 1], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := getPc } := by
    have h := step_jumpi_nz e { st0 n with stack := [getPc, 1], pc := 22 } getPc 1 []
      (decode_pc22 gSel iSel) rfl (by decide) (isJumpDest_get gSel iSel)
    simpa [env] using h
  rw [run_of_next 19 e _ _ s22]
  have s82 : step e { st0 n with stack := [], pc := getPc } =
      StepResult.next { st0 n with stack := [], pc := 83 } := by
    have hdec : decodeAt e.code getPc = some ({ op := .JUMPDEST }, 83) := by
      simpa [env, getPc] using decode_pc82 gSel iSel
    exact step_jumpdest e { st0 n with stack := [], pc := getPc } hdec
  rw [run_of_next 18 e _ _ s82]
  have s83 : step e { st0 n with stack := [], pc := 83 } =
      StepResult.next { st0 n with stack := [0], pc := 84 } := by
    have h := step_push e { st0 n with stack := [], pc := 83 } 0 (decode_pc83 gSel iSel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa [env] using h
  rw [run_of_next 17 e _ _ s83]
  have s84 : step e { st0 n with stack := [0], pc := 84 } =
      StepResult.next { st0 n with stack := [n], pc := 85 } := by
    have h := step_sload e { st0 n with stack := [0], pc := 84 } 0 []
      (decode_pc84 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using h
  rw [run_of_next 16 e _ _ s84]
  have s85 : step e { st0 n with stack := [n], pc := 85 } =
      StepResult.next { st0 n with stack := [0, n], pc := 86 } := by
    have h := step_push e { st0 n with stack := [n], pc := 85 } 0 (decode_pc85 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using h
  rw [run_of_next 15 e _ _ s85]
  have s86 : step e { st0 n with stack := [0, n], pc := 86 } =
      StepResult.next
        { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 87 } :=
    step_mstore e { st0 n with stack := [0, n], pc := 86 } 0 n []
      (by simpa [env] using decode_pc86 gSel iSel) rfl
  rw [run_of_next 14 e _ _ s86]
  have s87 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 87 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 89 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 87 } 32
      (decode_pc87 gSel iSel) (list_length_lt_1024 (k := 0) rfl)
    simpa [env] using h
  rw [run_of_next 13 e _ _ s87]
  have s89 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 89 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 90 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 89 } 0
      (decode_pc89 gSel iSel) (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using h
  rw [run_of_next 12 e _ _ s89]
  have s90 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 90 } =
        StepResult.halt
          (.ret ((List.range 32).map fun i =>
            memGet (memStore (st0 n).mem 0 n) (0 + i)))
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 90 } := by
    have h := step_return e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 90 }
      0 32 [] (by simpa [env] using decode_pc90 gSel iSel) rfl
    simpa using h
  rw [run_of_halt 11 e _ _ _ s90]
  rw [GetBody.memStore_packWord]
  simp only
  exact decodeWord_packWord_of_lt (wrap_lt n)

end Lsc3.Compile.GetInc
