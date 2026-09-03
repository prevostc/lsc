import Lsc3.Compile.GetContract
import Lsc3.Compile.Jump

/-!
# Wrong-selector `bytecode_ok` for the get-only compiler

Calldata whose 4-byte selector is not the contract's `PUSH4` falls through to
`InvalidSelector` and `REVERT`s. Apply `getOnly_miss`; do not instantiate at Keccak selectors.
-/

namespace Lsc3.Compile.GetContract

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Jump

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem decode_pc23 (sel : Nat) :
    decodeAt (code sel) 23 = some ({ op := .PUSH ⟨2, by decide⟩, imm := revPc }, 26) := by
  have hdrop : (code sel).drop 23 =
      emitPush2 revPc ++ (Opcode.toByte .JUMP :: (code sel).drop 27) := by
    rw [code_drop23]
    simp [fallBytes, List.append_assoc]
    rw [code_drop27]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push2 revPc _)
  simpa [revPc_mod] using h

theorem decode_pc26 (sel : Nat) :
    decodeAt (code sel) 26 = some ({ op := .JUMP }, 27) := by
  have h : (code sel).drop 26 = Opcode.toByte .JUMP :: (code sel).drop 27 := by
    rw [show 26 = 23 + 3 from rfl, drop_add, code_drop23]
    simp [fallBytes, List.append_assoc, code_drop27, emitPush2]
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem decode_pc27 (sel : Nat) :
    decodeAt (code sel) 27 = some ({ op := .JUMPDEST }, 28) := by
  have h : (code sel).drop 27 = Opcode.toByte .JUMPDEST :: (code sel).drop 28 := by
    rw [code_drop27, code_drop28]; rfl
  exact decodeAt_of_drop h (decodeAt_jumpdest_head _)

theorem isJumpDest_rev (sel : Nat) : isJumpDest (code sel) revPc = true := by
  simpa [revPc] using isJumpDest_of_decode (decode_pc27 sel)

theorem revertBytes_spine :
    revertBytes =
      emitPush32 (invalidSel * 2 ^ 224) ++ [0x5f, 0x52, 0x60, 4, 0x5f, 0xfd] :=
  rfl

theorem decode_pc28 (sel : Nat) :
    decodeAt (code sel) 28 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap (invalidSel * 2 ^ 224) }, 61) := by
  have hdrop : (code sel).drop 28 =
      emitPush32 (invalidSel * 2 ^ 224) ++
        ([0x5f, 0x52, 0x60, 4, 0x5f, 0xfd] ++ ([Opcode.toByte .JUMPDEST] ++ GetBody.code)) := by
    rw [code_drop28, revertBytes_spine, List.append_assoc]
  have h := decodeAt_of_drop hdrop (decodeAt_push32 (invalidSel * 2 ^ 224) _)
  simpa using h

theorem decode_pc61 (sel : Nat) :
    decodeAt (code sel) 61 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 62) := by
  have h : (code sel).drop 61 = 0x5f :: (code sel).drop 62 := by
    rw [show 61 = 28 + 33 from rfl, drop_add, code_drop28, revertBytes_spine, List.append_assoc]
    rw [List.drop_left' (emitPush32_length (invalidSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc62 (sel : Nat) :
    decodeAt (code sel) 62 = some ({ op := .MSTORE }, 63) := by
  have h : (code sel).drop 62 = Opcode.toByte .MSTORE :: (code sel).drop 63 := by
    rw [show 62 = 28 + 34 from rfl, drop_add, code_drop28, revertBytes_spine, List.append_assoc]
    rw [show 34 = 33 + 1 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (invalidSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc63 (sel : Nat) :
    decodeAt (code sel) 63 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 65) := by
  have hdrop : (code sel).drop 63 = 0x60 :: 4 :: (code sel).drop 65 := by
    rw [show 63 = 28 + 35 from rfl, drop_add, code_drop28, revertBytes_spine, List.append_assoc]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (invalidSel * 2 ^ 224))]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (4 : UInt8) ((code sel).drop 65))
  simpa [wrap] using h

theorem decode_pc65 (sel : Nat) :
    decodeAt (code sel) 65 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 66) := by
  have h : (code sel).drop 65 = 0x5f :: (code sel).drop 66 := by
    rw [show 65 = 28 + 37 from rfl, drop_add, code_drop28, revertBytes_spine, List.append_assoc]
    rw [show 37 = 33 + 4 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (invalidSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc66 (sel : Nat) :
    decodeAt (code sel) 66 = some ({ op := .REVERT }, 67) := by
  have h : (code sel).drop 66 = 0xfd :: (code sel).drop 67 := by
    rw [show 66 = 28 + 38 from rfl, drop_add, code_drop28, revertBytes_spine, List.append_assoc]
    rw [show 38 = 33 + 5 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (invalidSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_revert_head _)

/-- Calldata whose selector is not `sel` reverts; storage is unchanged. -/
theorem getOnly_miss (sel other : Nat) (n : Nat)
    (hne : other % 2 ^ 32 ≠ sel % 2 ^ 32) :
    (match run 40 { env sel [] with calldata := packCall other [] } (st0 n) with
    | some (Halt.revert _, s) => s.storage 0 = n
    | _ => False) := by
  let e : Env := { env sel [] with calldata := packCall other [] }
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 39 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have hs := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 38 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have hs := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at hs
    exact hs
  rw [run_of_next 37 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [revPc, 0], pc := 7 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 4 } revPc (decode_pc4 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 36 e _ _ s4]
  have s7 : step e { st0 n with stack := [revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [revPc, 0], pc := 7 } revPc []
      (decode_pc7 sel) rfl
    simpa using hs
  rw [run_of_next 35 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have hs := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 sel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 34 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 10 } := by
    have hs := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using hs
  rw [run_of_next 33 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 12 } := by
    have hs := step_push e
      { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 10 } 0xE0 (decode_pc10 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 32 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 13 } := by
    have hs := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall other []) 0) [] (decode_pc12 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 31 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)],
            pc := 18 } := by
    have hs := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 13 }
      (sel % 2 ^ 32) (decode_pc13 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 30 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [0], pc := 19 } := by
    have hs := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 18 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall other []) 0)) []
      (decode_pc18 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW] at hs ⊢
    split_ifs at hs with heq
    · exact absurd heq.symm (by simpa using hne)
    · exact hs
  rw [run_of_next 29 e _ _ s18]
  have s19 : step e { st0 n with stack := [0], pc := 19 } =
      StepResult.next { st0 n with stack := [getPc, 0], pc := 22 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 19 } getPc (decode_pc19 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 28 e _ _ s19]
  have s22 : step e { st0 n with stack := [getPc, 0], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := 23 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [getPc, 0], pc := 22 } getPc []
      (decode_pc22 sel) rfl
    simpa using hs
  rw [run_of_next 27 e _ _ s22]
  have s23 : step e { st0 n with stack := [], pc := 23 } =
      StepResult.next { st0 n with stack := [revPc], pc := 26 } := by
    have hs := step_push e { st0 n with stack := [], pc := 23 } revPc (decode_pc23 sel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s23]
  have s26 : step e { st0 n with stack := [revPc], pc := 26 } =
      StepResult.next { st0 n with stack := [], pc := revPc } := by
    have hs := step_jump e { st0 n with stack := [revPc], pc := 26 } revPc []
      (decode_pc26 sel) rfl (isJumpDest_rev sel)
    simpa [env] using hs
  rw [run_of_next 25 e _ _ s26]
  have s27 : step e { st0 n with stack := [], pc := revPc } =
      StepResult.next { st0 n with stack := [], pc := 28 } := by
    have hdec : decodeAt e.code revPc = some ({ op := .JUMPDEST }, 28) := by
      simpa [env, revPc] using decode_pc27 sel
    exact step_jumpdest e { st0 n with stack := [], pc := revPc } hdec
  rw [run_of_next 24 e _ _ s27]
  have s28 : step e { st0 n with stack := [], pc := 28 } =
      StepResult.next { st0 n with stack := [wrap (invalidSel * 2 ^ 224)], pc := 61 } := by
    have hs := step_push e { st0 n with stack := [], pc := 28 }
      (wrap (invalidSel * 2 ^ 224)) (decode_pc28 sel) (list_length_lt_1024 (k := 0) rfl)
    simpa [env] using hs
  rw [run_of_next 23 e _ _ s28]
  have s61 : step e { st0 n with stack := [wrap (invalidSel * 2 ^ 224)], pc := 61 } =
      StepResult.next { st0 n with stack := [0, wrap (invalidSel * 2 ^ 224)], pc := 62 } := by
    have hs := step_push e { st0 n with stack := [wrap (invalidSel * 2 ^ 224)], pc := 61 }
      0 (decode_pc61 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using hs
  rw [run_of_next 22 e _ _ s61]
  have s62 : step e { st0 n with stack := [0, wrap (invalidSel * 2 ^ 224)], pc := 62 } =
      StepResult.next { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [], pc := 63 } :=
    step_mstore e { st0 n with stack := [0, wrap (invalidSel * 2 ^ 224)], pc := 62 }
      0 (wrap (invalidSel * 2 ^ 224)) [] (by simpa [env] using decode_pc62 sel) rfl
  rw [run_of_next 21 e _ _ s62]
  have s63 : step e { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [], pc := 63 } =
      StepResult.next { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [4], pc := 65 } := by
    have hs := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [], pc := 63 }
      4 (decode_pc63 sel) (list_length_lt_1024 (k := 0) rfl)
    simpa [env] using hs
  rw [run_of_next 20 e _ _ s63]
  have s65 : step e { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [4], pc := 65 } =
      StepResult.next { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [0, 4], pc := 66 } := by
    have hs := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [4], pc := 65 }
      0 (decode_pc65 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa [env] using hs
  rw [run_of_next 19 e _ _ s65]
  have s66 : step e { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [0, 4], pc := 66 } =
      StepResult.halt
        (.revert ((List.range (4 : Nat)).map fun i =>
          memGet (memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224))) (0 + i)))
        { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [0, 4], pc := 66 } := by
    have hs := step_revert e
      { st0 n with mem := memStore (st0 n).mem 0 (wrap (invalidSel * 2 ^ 224)), stack := [0, 4], pc := 66 }
      0 4 [] (by simpa [env] using decode_pc66 sel) rfl
    simpa using hs
  rw [run_of_halt 18 e _ _ _ s66]
  simp [st0]

end Lsc3.Compile.GetContract
