import Lsc3.Compile.IncByHit
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# Overflow `bytecode_ok` for isolated `incrementBy`

When `n + arg ≥ 2^256` (`arg ≠ 0`), checked-add jumps into the Panic(0x11) block
and the machine `REVERT`s. Apply `incBy_overflow`; do not instantiate at a Keccak selector.
-/

namespace Lsc3.Compile.IncByBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Jump Lsc3.Compile.Codegen

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

private def panicImm : Nat :=
  selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224

theorem code_drop87 :
    code.drop 87 = IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes) := by
  rw [show 87 = 86 + 1 from rfl, drop_add, code_drop86]; rfl

theorem code_drop120 :
    code.drop 120 =
      [0x5f, 0x52, 0x60, 0x11, 0x60, 4, 0x52, 0x60, 36, 0x5f, 0xfd] ++
        (Opcode.toByte .JUMPDEST :: tailBytes) := by
  rw [show 120 = 87 + 33 from rfl, drop_add, code_drop87]
  rw [IncBody.panicBytes]
  simp only [List.append_assoc]
  rw [List.drop_left' (emitPush32_length
    (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))]

theorem decode_pc87 :
    decodeAt code 87 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap panicImm }, 120) := by
  have hdrop : code.drop 87 =
      emitPush32 (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224) ++
        ([0x5f, 0x52, 0x60, 0x11, 0x60, 4, 0x52, 0x60, 36, 0x5f, 0xfd] ++
          (Opcode.toByte .JUMPDEST :: tailBytes)) := by
    rw [code_drop87, IncBody.panicBytes]
    simp only [List.append_assoc]
  have h := decodeAt_of_drop hdrop
    (decodeAt_push32 (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224) _)
  simpa [panicImm] using h

theorem decode_pc120 :
    decodeAt code 120 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 121) := by
  have h : code.drop 120 = 0x5f :: code.drop 121 := by
    rw [code_drop120]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc121 :
    decodeAt code 121 = some ({ op := .MSTORE }, 122) := by
  have h : code.drop 121 = Opcode.toByte .MSTORE :: code.drop 122 := by
    rw [show 121 = 120 + 1 from rfl, drop_add, code_drop120]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc122 :
    decodeAt code 122 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0x11 }, 124) := by
  have hdrop : code.drop 122 = 0x60 :: 0x11 :: code.drop 124 := by
    rw [show 122 = 120 + 2 from rfl, drop_add, code_drop120]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x11 : UInt8) (code.drop 124))
  simpa [wrap] using h

theorem decode_pc124 :
    decodeAt code 124 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 126) := by
  have hdrop : code.drop 124 = 0x60 :: 4 :: code.drop 126 := by
    rw [show 124 = 120 + 4 from rfl, drop_add, code_drop120]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (4 : UInt8) (code.drop 126))
  simpa [wrap] using h

theorem decode_pc126 :
    decodeAt code 126 = some ({ op := .MSTORE }, 127) := by
  have h : code.drop 126 = Opcode.toByte .MSTORE :: code.drop 127 := by
    rw [show 126 = 120 + 6 from rfl, drop_add, code_drop120]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc127 :
    decodeAt code 127 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 36 }, 129) := by
  have hdrop : code.drop 127 = 0x60 :: 36 :: code.drop 129 := by
    rw [show 127 = 120 + 7 from rfl, drop_add, code_drop120]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (36 : UInt8) (code.drop 129))
  simpa [wrap] using h

theorem decode_pc129 :
    decodeAt code 129 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 130) := by
  have h : code.drop 129 = 0x5f :: code.drop 130 := by
    rw [show 129 = 120 + 9 from rfl, drop_add, code_drop120]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc130 :
    decodeAt code 130 = some ({ op := .REVERT }, 131) := by
  have h : code.drop 130 = Opcode.toByte .REVERT :: code.drop 131 := by
    rw [show 130 = 120 + 10 from rfl, drop_add, code_drop120]; rfl
  exact decodeAt_of_drop h (decodeAt_revert_head _)

/-- Matching `incrementBy arg` that overflows: the machine reverts (Panic block).
Slot 0 is unchanged. -/
theorem incBy_overflow (n arg : Nat) (hn : n < wordBound) (harg : arg < wordBound)
    (hnz : arg ≠ 0) (hov : wordBound ≤ n + arg) :
    (match run 55 (env arg) (st0 n) with
    | some (Halt.revert _, s) => s.storage 0 = n
    | _ => False) := by
  have hwrapn : wrap n = n := Nat.mod_eq_of_lt hn
  have hwrapa : wrap arg = arg := Nat.mod_eq_of_lt harg
  have hcd : calldataLoad (packCall 0 [arg]) 4 = wrap arg := calldataLoad_packCall_arg 0 arg
  let e := env arg
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 54 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall 0 [arg]) 4], pc := 3 } := by
    have hs := step_calldataload e { st0 n with stack := [4], pc := 2 } 4 []
      decode_pc2 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using hs
  rw [run_of_next 53 e _ _ s2]
  have s3 : step e { st0 n with stack := [calldataLoad (packCall 0 [arg]) 4], pc := 3 } =
      StepResult.next { st0 n with stack := [localBase, calldataLoad (packCall 0 [arg]) 4], pc := 5 } := by
    have hs := step_push e { st0 n with stack := [calldataLoad (packCall 0 [arg]) 4], pc := 3 }
      localBase decode_pc3 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 52 e _ _ s3]
  have s5 : step e { st0 n with stack := [localBase, calldataLoad (packCall 0 [arg]) 4], pc := 5 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [], pc := 6 } := by
    have hs := step_mstore e { st0 n with stack := [localBase, calldataLoad (packCall 0 [arg]) 4], pc := 5 }
      localBase (calldataLoad (packCall 0 [arg]) 4) [] decode_pc5 rfl
    simpa [env, memP, hcd] using hs
  rw [run_of_next 51 e _ _ s5]
  have s6 : step e { st0 n with mem := memP n arg, stack := [], pc := 6 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [localBase], pc := 8 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [], pc := 6 }
      localBase decode_pc6 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 50 e _ _ s6]
  have s8 : step e { st0 n with mem := memP n arg, stack := [localBase], pc := 8 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [wrap arg], pc := 9 } := by
    have hs := step_mload e { st0 n with mem := memP n arg, stack := [localBase], pc := 8 }
      localBase [] decode_pc8 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 49 e _ _ s8]
  have s9 : step e { st0 n with mem := memP n arg, stack := [wrap arg], pc := 9 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [0, wrap arg], pc := 10 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [wrap arg], pc := 9 }
      0 decode_pc9 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 48 e _ _ s9]
  have s10 : step e { st0 n with mem := memP n arg, stack := [0, wrap arg], pc := 10 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [0], pc := 11 } := by
    have hs := step_eq e { st0 n with mem := memP n arg, stack := [0, wrap arg], pc := 10 }
      0 (wrap arg) [] decode_pc10 rfl (list_length_lt_1024 (k := 0) rfl)
    have hne : wrap arg ≠ 0 := by
      rw [hwrapa]; exact hnz
    simp only [eqW_ne (Ne.symm hne)] at hs
    exact hs
  rw [run_of_next 47 e _ _ s10]
  have s11 : step e { st0 n with mem := memP n arg, stack := [0], pc := 11 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [1], pc := 12 } := by
    have hs := step_iszero e { st0 n with mem := memP n arg, stack := [0], pc := 11 }
      0 [] decode_pc11 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 46 e _ _ s11]
  have s12 : step e { st0 n with mem := memP n arg, stack := [1], pc := 12 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [0], pc := 13 } := by
    have hs := step_iszero e { st0 n with mem := memP n arg, stack := [1], pc := 12 }
      1 [] decode_pc12 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 45 e _ _ s12]
  have s13 : step e { st0 n with mem := memP n arg, stack := [0], pc := 13 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [reqRPc, 0], pc := 16 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [0], pc := 13 }
      reqRPc decode_pc13 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 44 e _ _ s13]
  have s16 : step e { st0 n with mem := memP n arg, stack := [reqRPc, 0], pc := 16 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [], pc := 17 } := by
    have hs := step_jumpi_zero e { st0 n with mem := memP n arg, stack := [reqRPc, 0], pc := 16 }
      reqRPc [] decode_pc16 rfl
    simpa using hs
  rw [run_of_next 43 e _ _ s16]
  have s17 : step e { st0 n with mem := memP n arg, stack := [], pc := 17 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [reqOPc], pc := 20 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [], pc := 17 }
      reqOPc decode_pc17 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 42 e _ _ s17]
  have s20 : step e { st0 n with mem := memP n arg, stack := [reqOPc], pc := 20 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [], pc := reqOPc } := by
    have hs := step_jump e { st0 n with mem := memP n arg, stack := [reqOPc], pc := 20 }
      reqOPc [] decode_pc20 rfl isJumpDest_reqO
    simpa [env] using hs
  rw [run_of_next 41 e _ _ s20]
  have s61 : step e { st0 n with mem := memP n arg, stack := [], pc := reqOPc } =
      StepResult.next { st0 n with mem := memP n arg, stack := [], pc := 62 } :=
    step_jumpdest e { st0 n with mem := memP n arg, stack := [], pc := reqOPc }
      (by simpa [env, reqOPc] using decode_pc61)
  rw [run_of_next 40 e _ _ s61]
  have s62 : step e { st0 n with mem := memP n arg, stack := [], pc := 62 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [0], pc := 63 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [], pc := 62 }
      0 decode_pc62 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 39 e _ _ s62]
  have s63 : step e { st0 n with mem := memP n arg, stack := [0], pc := 63 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [n], pc := 64 } := by
    have hs := step_sload e { st0 n with mem := memP n arg, stack := [0], pc := 63 }
      0 [] decode_pc63 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 38 e _ _ s63]
  have s64 : step e { st0 n with mem := memP n arg, stack := [n], pc := 64 } =
      StepResult.next { st0 n with mem := memP n arg, stack := [localBase + 32, n], pc := 66 } := by
    have hs := step_push e { st0 n with mem := memP n arg, stack := [n], pc := 64 }
      (localBase + 32) decode_pc64 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 37 e _ _ s64]
  have s66 : step e { st0 n with mem := memP n arg, stack := [localBase + 32, n], pc := 66 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [], pc := 67 } :=
    step_mstore e { st0 n with mem := memP n arg, stack := [localBase + 32, n], pc := 66 }
      (localBase + 32) n [] decode_pc66 rfl
  rw [run_of_next 36 e _ _ s66]
  have s67 : step e { st0 n with mem := mem1 n arg, stack := [], pc := 67 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [localBase + 32], pc := 69 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [], pc := 67 }
      (localBase + 32) decode_pc67 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 35 e _ _ s67]
  have s69 : step e { st0 n with mem := mem1 n arg, stack := [localBase + 32], pc := 69 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [wrap n], pc := 70 } := by
    have hs := step_mload e { st0 n with mem := mem1 n arg, stack := [localBase + 32], pc := 69 }
      (localBase + 32) [] decode_pc69 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 34 e _ _ s69]
  have s70 : step e { st0 n with mem := mem1 n arg, stack := [wrap n], pc := 70 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [localBase, wrap n], pc := 72 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [wrap n], pc := 70 }
      localBase decode_pc70 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 33 e _ _ s70]
  have s72 : step e { st0 n with mem := mem1 n arg, stack := [localBase, wrap n], pc := 72 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [wrap arg, wrap n], pc := 73 } := by
    have hs := step_mload e { st0 n with mem := mem1 n arg, stack := [localBase, wrap n], pc := 72 }
      localBase [wrap n] decode_pc72 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa [memLoad_mem1_param] using hs
  rw [run_of_next 32 e _ _ s72]
  have s73 : step e { st0 n with mem := mem1 n arg, stack := [wrap arg, wrap n], pc := 73 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [wrap n, wrap arg, wrap n], pc := 74 } := by
    have hs := step_dup2 e { st0 n with mem := mem1 n arg, stack := [wrap arg, wrap n], pc := 73 }
      (wrap arg) (wrap n) [] decode_pc73 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 31 e _ _ s73]
  have s74 : step e { st0 n with mem := mem1 n arg, stack := [wrap n, wrap arg, wrap n], pc := 74 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), wrap n], pc := 75 } := by
    have hs := step_add e { st0 n with mem := mem1 n arg, stack := [wrap n, wrap arg, wrap n], pc := 74 }
      (wrap n) (wrap arg) [wrap n] decode_pc74 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 30 e _ _ s74]
  have s75 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), wrap n], pc := 75 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), addW (wrap n) (wrap arg), wrap n], pc := 76 } := by
    have hs := step_dup1 e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), wrap n], pc := 75 }
      (addW (wrap n) (wrap arg)) [wrap n] decode_pc75 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 29 e _ _ s75]
  have s76 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), addW (wrap n) (wrap arg), wrap n], pc := 76 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [wrap n, addW (wrap n) (wrap arg), addW (wrap n) (wrap arg)], pc := 77 } := by
    have hs := step_swap2 e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg), addW (wrap n) (wrap arg), wrap n], pc := 76 }
      (addW (wrap n) (wrap arg)) (addW (wrap n) (wrap arg)) (wrap n) [] decode_pc76 rfl
    simpa using hs
  rw [run_of_next 28 e _ _ s76]
  have s77 : step e { st0 n with mem := mem1 n arg, stack := [wrap n, addW (wrap n) (wrap arg), addW (wrap n) (wrap arg)], pc := 77 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [1, addW (wrap n) (wrap arg)], pc := 78 } := by
    have hs := step_gt e { st0 n with mem := mem1 n arg, stack := [wrap n, addW (wrap n) (wrap arg), addW (wrap n) (wrap arg)], pc := 77 }
      (wrap n) (addW (wrap n) (wrap arg)) [addW (wrap n) (wrap arg)] decode_pc77 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) (wrap arg)) = 1 := by
      rw [hwrapn, hwrapa]; exact gtW_add_of_ge hn harg hov
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 27 e _ _ s77]
  have s78 : step e { st0 n with mem := mem1 n arg, stack := [1, addW (wrap n) (wrap arg)], pc := 78 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addRPc, 1, addW (wrap n) (wrap arg)], pc := 81 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [1, addW (wrap n) (wrap arg)], pc := 78 }
      addRPc decode_pc78 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s78]
  have s81 : step e { st0 n with mem := mem1 n arg, stack := [addRPc, 1, addW (wrap n) (wrap arg)], pc := 81 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addRPc } := by
    have hs := step_jumpi_nz e
      { st0 n with mem := mem1 n arg, stack := [addRPc, 1, addW (wrap n) (wrap arg)], pc := 81 }
      addRPc 1 [addW (wrap n) (wrap arg)] decode_pc81 rfl (by decide) isJumpDest_addR
    simpa [env] using hs
  rw [run_of_next 25 e _ _ s81]
  have s86 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addRPc } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 87 } :=
    step_jumpdest e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addRPc }
      (by simpa [env, addRPc] using decode_pc86)
  rw [run_of_next 24 e _ _ s86]
  have s87 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 87 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [wrap panicImm, addW (wrap n) (wrap arg)], pc := 120 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 87 }
      (wrap panicImm) decode_pc87 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 23 e _ _ s87]
  have s120 : step e { st0 n with mem := mem1 n arg, stack := [wrap panicImm, addW (wrap n) (wrap arg)], pc := 120 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [0, wrap panicImm, addW (wrap n) (wrap arg)], pc := 121 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [wrap panicImm, addW (wrap n) (wrap arg)], pc := 120 }
      0 decode_pc120 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 22 e _ _ s120]
  have s121 : step e { st0 n with mem := mem1 n arg, stack := [0, wrap panicImm, addW (wrap n) (wrap arg)], pc := 121 } =
      StepResult.next { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [addW (wrap n) (wrap arg)], pc := 122 } :=
    step_mstore e { st0 n with mem := mem1 n arg, stack := [0, wrap panicImm, addW (wrap n) (wrap arg)], pc := 121 }
      0 (wrap panicImm) [addW (wrap n) (wrap arg)] decode_pc121 rfl
  rw [run_of_next 21 e _ _ s121]
  have s122 : step e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [addW (wrap n) (wrap arg)], pc := 122 } =
      StepResult.next { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [0x11, addW (wrap n) (wrap arg)], pc := 124 } := by
    have hs := step_push e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [addW (wrap n) (wrap arg)], pc := 122 }
      0x11 decode_pc122 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 20 e _ _ s122]
  have s124 : step e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [0x11, addW (wrap n) (wrap arg)], pc := 124 } =
      StepResult.next { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [4, 0x11, addW (wrap n) (wrap arg)], pc := 126 } := by
    have hs := step_push e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [0x11, addW (wrap n) (wrap arg)], pc := 124 }
      4 decode_pc124 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 19 e _ _ s124]
  have s126 : step e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [4, 0x11, addW (wrap n) (wrap arg)], pc := 126 } =
      StepResult.next { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [addW (wrap n) (wrap arg)], pc := 127 } :=
    step_mstore e { st0 n with mem := memStore (mem1 n arg) 0 (wrap panicImm), stack := [4, 0x11, addW (wrap n) (wrap arg)], pc := 126 }
      4 0x11 [addW (wrap n) (wrap arg)] decode_pc126 rfl
  rw [run_of_next 18 e _ _ s126]
  have s127 : step e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [addW (wrap n) (wrap arg)], pc := 127 } =
      StepResult.next { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [36, addW (wrap n) (wrap arg)], pc := 129 } := by
    have hs := step_push e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [addW (wrap n) (wrap arg)], pc := 127 }
      36 decode_pc127 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 17 e _ _ s127]
  have s129 : step e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [36, addW (wrap n) (wrap arg)], pc := 129 } =
      StepResult.next { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [0, 36, addW (wrap n) (wrap arg)], pc := 130 } := by
    have hs := step_push e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [36, addW (wrap n) (wrap arg)], pc := 129 }
      0 decode_pc129 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 16 e _ _ s129]
  have s130 : step e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [0, 36, addW (wrap n) (wrap arg)], pc := 130 } =
      StepResult.halt
        (.revert ((List.range (36 : Nat)).map fun i =>
          memGet (memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11) (0 + i)))
        { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [0, 36, addW (wrap n) (wrap arg)], pc := 130 } := by
    have hs := step_revert e { st0 n with mem := memStore (memStore (mem1 n arg) 0 (wrap panicImm)) 4 0x11, stack := [0, 36, addW (wrap n) (wrap arg)], pc := 130 }
      0 36 [addW (wrap n) (wrap arg)] decode_pc130 rfl
    simpa using hs
  rw [run_of_halt 15 e _ _ _ s130]
  simp [st0]

end Lsc3.Compile.IncByBody
