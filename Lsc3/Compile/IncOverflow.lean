import Lsc3.Compile.IncContract

/-!
# Overflow `bytecode_ok` for the increment-only compiler

When slot 0 holds `2^256 - 1`, checked-add jumps into the Panic(0x11) block and
the machine `REVERT`s. Apply `incOnly_overflow`; do not instantiate at a Keccak selector.
-/

namespace Lsc3.Compile.IncContract

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Codegen

/-- Matching selector + unsigned overflow: the machine reverts (Panic block). -/
theorem incOnly_overflow (sel : Nat) (n : Nat) (hov : n + 1 = wordBound) :
    (match run 50 (env sel []) (st0 n) with
    | some (Halt.revert _, s) => s.storage 0 = n
    | _ => False) := by
  have hn : n < wordBound := by omega
  have hwrap : wrap n = n := Nat.mod_eq_of_lt hn
  let e := env sel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 49 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have hs := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 48 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have hs := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at hs
    exact hs
  rw [run_of_next 47 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [GetContract.revPc, 0], pc := 7 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 4 } GetContract.revPc (decode_pc4 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 46 e _ _ s4]
  have s7 : step e { st0 n with stack := [GetContract.revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [GetContract.revPc, 0], pc := 7 }
      GetContract.revPc [] (decode_pc7 sel) rfl
    simpa using hs
  rw [run_of_next 45 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have hs := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 sel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 44 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } := by
    have hs := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using hs
  rw [run_of_next 43 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } := by
    have hs := step_push e
      { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } 0xE0 (decode_pc10 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 42 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } := by
    have hs := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall sel []) 0) [] (decode_pc12 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 41 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)],
            pc := 18 } := by
    have hs := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 }
      (sel % 2 ^ 32) (decode_pc13 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 40 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [1], pc := 19 } := by
    have hs := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall sel []) 0)) []
      (decode_pc18 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at hs ⊢
    exact hs
  rw [run_of_next 39 e _ _ s18]
  have s19 : step e { st0 n with stack := [1], pc := 19 } =
      StepResult.next { st0 n with stack := [incPc, 1], pc := 22 } := by
    have hs := step_push e { st0 n with stack := [1], pc := 19 } incPc (decode_pc19 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 38 e _ _ s19]
  have s22 : step e { st0 n with stack := [incPc, 1], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := incPc } := by
    have hs := step_jumpi_nz e { st0 n with stack := [incPc, 1], pc := 22 } incPc 1 []
      (decode_pc22 sel) rfl (by decide) (isJumpDest_inc sel)
    simpa [env] using hs
  rw [run_of_next 37 e _ _ s22]
  have s67 : step e { st0 n with stack := [], pc := incPc } =
      StepResult.next { st0 n with stack := [], pc := 68 } := by
    have hdec : decodeAt e.code incPc = some ({ op := .JUMPDEST }, 68) := by
      simpa [env, incPc] using decode_pc67 sel
    exact step_jumpdest e { st0 n with stack := [], pc := incPc } hdec
  rw [run_of_next 36 e _ _ s67]
  have d68 : decodeAt e.code 68 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 69) := by
    simpa [env] using decode_at sel bdec0
  have s68 : step e { st0 n with stack := [], pc := 68 } =
      StepResult.next { st0 n with stack := [0], pc := 69 } := by
    have hs := step_push e { st0 n with stack := [], pc := 68 } 0 d68
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 35 e _ _ s68]
  have d69 : decodeAt e.code 69 = some ({ op := .SLOAD }, 70) := by
    simpa [env] using decode_at sel bdec1
  have s69 : step e { st0 n with stack := [0], pc := 69 } =
      StepResult.next { st0 n with stack := [n], pc := 70 } := by
    have hs := step_sload e { st0 n with stack := [0], pc := 69 } 0 [] d69 rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 34 e _ _ s69]
  have d70 : decodeAt e.code 70 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 72) := by
    simpa [env] using decode_at sel bdec2
  have s70 : step e { st0 n with stack := [n], pc := 70 } =
      StepResult.next { st0 n with stack := [localBase, n], pc := 72 } := by
    have hs := step_push e { st0 n with stack := [n], pc := 70 } localBase d70
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 33 e _ _ s70]
  have d72 : decodeAt e.code 72 = some ({ op := .MSTORE }, 73) := by
    simpa [env] using decode_at sel bdec4
  have s72 : step e { st0 n with stack := [localBase, n], pc := 72 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 73 } :=
    step_mstore e { st0 n with stack := [localBase, n], pc := 72 } localBase n [] d72 rfl
  rw [run_of_next 32 e _ _ s72]
  have d73 : decodeAt e.code 73 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 75) := by
    simpa [env] using decode_at sel bdec5
  have s73 : step e { st0 n with mem := mem1 n, stack := [], pc := 73 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 75 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [], pc := 73 }
      localBase d73 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 31 e _ _ s73]
  have d75 : decodeAt e.code 75 = some ({ op := .MLOAD }, 76) := by
    simpa [env] using decode_at sel bdec7
  have s75 : step e { st0 n with mem := mem1 n, stack := [localBase], pc := 75 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 } := by
    have hs := step_mload e { st0 n with mem := mem1 n, stack := [localBase], pc := 75 }
      localBase [] d75 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 30 e _ _ s75]
  have d76 : decodeAt e.code 76 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 78) := by
    simpa [env] using decode_at sel bdec8
  have s76 : step e { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 }
      1 d76 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 29 e _ _ s76]
  have d78 : decodeAt e.code 78 = some ({ op := .DUP ⟨1, by decide⟩ }, 79) := by
    simpa [env] using decode_at sel bdec10
  have s78 : step e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 } := by
    have hs := step_dup2 e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 }
      1 (wrap n) [] d78 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 28 e _ _ s78]
  have d79 : decodeAt e.code 79 = some ({ op := .ADD }, 80) := by
    simpa [env] using decode_at sel bdec11
  have s79 : step e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 } := by
    have hs := step_add e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 }
      (wrap n) 1 [wrap n] d79 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 27 e _ _ s79]
  have d80 : decodeAt e.code 80 = some ({ op := .DUP ⟨0, by decide⟩ }, 81) := by
    simpa [env] using decode_at sel bdec12
  have s80 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 } := by
    have hs := step_dup1 e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 }
      (addW (wrap n) 1) [wrap n] d80 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s80]
  have d81 : decodeAt e.code 81 = some ({ op := .SWAP ⟨1, by decide⟩ }, 82) := by
    simpa [env] using decode_at sel bdec13
  have s81 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 } := by
    have hs := step_swap2 e
      { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 }
      (addW (wrap n) 1) (addW (wrap n) 1) (wrap n) [] d81 rfl
    simpa using hs
  rw [run_of_next 25 e _ _ s81]
  have d82 : decodeAt e.code 82 = some ({ op := .GT }, 83) := by
    simpa [env] using decode_at sel bdec14
  have s82 : step e { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, addW (wrap n) 1], pc := 83 } := by
    have hs := step_gt e
      { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 }
      (wrap n) (addW (wrap n) 1) [addW (wrap n) 1] d82 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) 1) = 1 := by
      rw [hwrap]; exact gtW_add_overflow hov
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 24 e _ _ s82]
  have d83 : decodeAt e.code 83 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyRevPc }, 86) := by
    simpa [env] using decode_at sel bdec15
  have s83 : step e { st0 n with mem := mem1 n, stack := [1, addW (wrap n) 1], pc := 83 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [bodyRevPc, 1, addW (wrap n) 1], pc := 86 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [1, addW (wrap n) 1], pc := 83 }
      bodyRevPc d83 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 23 e _ _ s83]
  have d86 : decodeAt e.code 86 = some ({ op := .JUMPI }, 87) := by
    simpa [env] using decode_at sel bdec18
  have s86 : step e { st0 n with mem := mem1 n, stack := [bodyRevPc, 1, addW (wrap n) 1], pc := 86 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyRevPc } := by
    have hs := step_jumpi_nz e
      { st0 n with mem := mem1 n, stack := [bodyRevPc, 1, addW (wrap n) 1], pc := 86 }
      bodyRevPc 1 [addW (wrap n) 1] d86 rfl (by decide) (isJumpDest_rev sel)
    simpa [env] using hs
  rw [run_of_next 22 e _ _ s86]
  have d91 : decodeAt e.code bodyRevPc = some ({ op := .JUMPDEST }, 92) := by
    simpa [env, bodyRevPc] using decode_at sel bdec23
  have s91 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyRevPc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 92 } :=
    step_jumpdest e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyRevPc } d91
  rw [run_of_next 21 e _ _ s91]
  have d92 : decodeAt e.code 92 =
      some ({ op := .PUSH ⟨32, by decide⟩,
              imm := wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224) }, 125) := by
    simpa [env] using decode_at sel bdec24
  have s92 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 92 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 125 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 92 }
      (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224)) d92
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 20 e _ _ s92]
  have d125 : decodeAt e.code 125 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 126) := by
    simpa [env] using decode_at sel bdec57
  have s125 : step e { st0 n with mem := mem1 n, stack := [wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 125 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 126 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 125 }
      0 d125 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 19 e _ _ s125]
  have d126 : decodeAt e.code 126 = some ({ op := .MSTORE }, 127) := by
    simpa [env] using decode_at sel bdec58
  have s126 : step e { st0 n with mem := mem1 n, stack := [0, wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 126 } =
      StepResult.next { st0 n with mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224)), stack := [addW (wrap n) 1], pc := 127 } :=
    step_mstore e { st0 n with mem := mem1 n, stack := [0, wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224), addW (wrap n) 1], pc := 126 }
      0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
      [addW (wrap n) 1] d126 rfl
  rw [run_of_next 18 e _ _ s126]
  have d127 : decodeAt e.code 127 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0x11 }, 129) := by
    simpa [env] using decode_at sel bdec59
  have s127 : step e { st0 n with
      mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
      stack := [addW (wrap n) 1], pc := 127 } =
      StepResult.next { st0 n with
        mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
        stack := [0x11, addW (wrap n) 1], pc := 129 } := by
    have hs := step_push e { st0 n with
        mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
        stack := [addW (wrap n) 1], pc := 127 }
      0x11 d127 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 17 e _ _ s127]
  have d129 : decodeAt e.code 129 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 131) := by
    simpa [env] using decode_at sel bdec61
  have s129 : step e { st0 n with
      mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
      stack := [0x11, addW (wrap n) 1], pc := 129 } =
      StepResult.next { st0 n with
        mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
        stack := [4, 0x11, addW (wrap n) 1], pc := 131 } := by
    have hs := step_push e { st0 n with
        mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
        stack := [0x11, addW (wrap n) 1], pc := 129 }
      4 d129 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 16 e _ _ s129]
  have d131 : decodeAt e.code 131 = some ({ op := .MSTORE }, 132) := by
    simpa [env] using decode_at sel bdec63
  have s131 : step e { st0 n with
      mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
      stack := [4, 0x11, addW (wrap n) 1], pc := 131 } =
      StepResult.next { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [addW (wrap n) 1], pc := 132 } :=
    step_mstore e { st0 n with
        mem := memStore (mem1 n) 0 (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))
        stack := [4, 0x11, addW (wrap n) 1], pc := 131 }
      4 0x11 [addW (wrap n) 1] d131 rfl
  rw [run_of_next 15 e _ _ s131]
  have d132 : decodeAt e.code 132 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 36 }, 134) := by
    simpa [env] using decode_at sel bdec64
  have s132 : step e { st0 n with
      mem := memStore (memStore (mem1 n) 0
        (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
      stack := [addW (wrap n) 1], pc := 132 } =
      StepResult.next { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [36, addW (wrap n) 1], pc := 134 } := by
    have hs := step_push e { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [addW (wrap n) 1], pc := 132 }
      36 d132 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 14 e _ _ s132]
  have d134 : decodeAt e.code 134 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 135) := by
    simpa [env] using decode_at sel bdec66
  have s134 : step e { st0 n with
      mem := memStore (memStore (mem1 n) 0
        (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
      stack := [36, addW (wrap n) 1], pc := 134 } =
      StepResult.next { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [0, 36, addW (wrap n) 1], pc := 135 } := by
    have hs := step_push e { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [36, addW (wrap n) 1], pc := 134 }
      0 d134 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 13 e _ _ s134]
  have d135 : decodeAt e.code 135 = some ({ op := .REVERT }, 136) := by
    simpa [env] using decode_at sel bdec67
  have s135 : step e { st0 n with
      mem := memStore (memStore (mem1 n) 0
        (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
      stack := [0, 36, addW (wrap n) 1], pc := 135 } =
      StepResult.halt
        (.revert ((List.range (36 : Nat)).map fun i =>
          memGet (memStore (memStore (mem1 n) 0
            (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11)
            (0 + i)))
        { st0 n with
          mem := memStore (memStore (mem1 n) 0
            (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
          stack := [0, 36, addW (wrap n) 1], pc := 135 } := by
    have hs := step_revert e { st0 n with
        mem := memStore (memStore (mem1 n) 0
          (wrap (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224))) 4 0x11
        stack := [0, 36, addW (wrap n) 1], pc := 135 }
      0 36 [addW (wrap n) 1] d135 rfl
    simpa using hs
  rw [run_of_halt 12 e _ _ _ s135]
  simp [st0]

end Lsc3.Compile.IncContract
