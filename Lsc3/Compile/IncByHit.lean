import Lsc3.Compile.IncByBody
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# `bytecode_ok` for the `incrementBy` body (no overflow, `n ≠ 0`)

Calldata is `packCall 0 [arg]` so `CALLDATALOAD` at offset 4 loads `arg`.
`incBy_hit` — apply it; do not instantiate at a Keccak selector.
-/

namespace Lsc3.Compile.IncByBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Jump

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_spine :
    code = loadParamBytes ++ (requireBytes ++ (prefixBytes ++ (checkedAddBytes ++ tailBytes))) := by
  simp [code, List.append_assoc]

theorem code_drop6 : code.drop 6 = requireBytes ++ (prefixBytes ++ (checkedAddBytes ++ tailBytes)) := by
  rw [code_spine, List.drop_left' loadParamBytes_length]

theorem code_drop6_push :
    code.drop 6 = 0x60 :: 0x80 :: code.drop 8 := by
  rw [code_drop6]
  rw [show 8 = 6 + 2 from rfl, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop8 :
    code.drop 8 = Opcode.toByte .MLOAD :: code.drop 9 := by
  rw [show 8 = 6 + 2 from rfl, show 9 = 6 + 3 from rfl, drop_add, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop9 :
    code.drop 9 = 0x5f :: code.drop 10 := by
  rw [show 9 = 6 + 3 from rfl, show 10 = 6 + 4 from rfl, drop_add, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop10 :
    code.drop 10 = Opcode.toByte .EQ :: code.drop 11 := by
  rw [show 10 = 6 + 4 from rfl, show 11 = 6 + 5 from rfl, drop_add, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop11 :
    code.drop 11 = Opcode.toByte .ISZERO :: code.drop 12 := by
  rw [show 11 = 6 + 5 from rfl, show 12 = 6 + 6 from rfl, drop_add, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop12 :
    code.drop 12 = Opcode.toByte .ISZERO :: code.drop 13 := by
  rw [show 12 = 6 + 6 from rfl, show 13 = 6 + 7 from rfl, drop_add, drop_add, code_drop6]
  rw [requireBytes]
  simp only [requireHeadBytes, List.append_assoc]
  rfl

theorem code_drop13 :
    code.drop 13 =
      emitPush2 reqRPc ++ ([Opcode.toByte .JUMPI] ++ (emitPush2 reqOPc ++
        ([Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++ (zeroRevertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (prefixBytes ++ (checkedAddBytes ++ tailBytes)))))))) := by
  rw [show 13 = 6 + 7 from rfl, drop_add, code_drop6]
  rw [requireBytes]
  simp only [List.append_assoc]
  rw [List.drop_left' requireHeadBytes_length]

theorem code_drop16 :
    code.drop 16 =
      [Opcode.toByte .JUMPI] ++ (emitPush2 reqOPc ++ ([Opcode.toByte .JUMP] ++
        ([Opcode.toByte .JUMPDEST] ++ (zeroRevertBytes ++ ([Opcode.toByte .JUMPDEST] ++
          (prefixBytes ++ (checkedAddBytes ++ tailBytes))))))) := by
  rw [show 16 = 13 + 3 from rfl, drop_add, code_drop13, List.drop_left' (emitPush2_length reqRPc)]

theorem code_drop17 :
    code.drop 17 =
      emitPush2 reqOPc ++ ([Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++
        (zeroRevertBytes ++ ([Opcode.toByte .JUMPDEST] ++
          (prefixBytes ++ (checkedAddBytes ++ tailBytes)))))) := by
  rw [show 17 = 16 + 1 from rfl, drop_add, code_drop16]; rfl

theorem code_drop20 :
    code.drop 20 =
      [Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++ (zeroRevertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (prefixBytes ++ (checkedAddBytes ++ tailBytes))))) := by
  rw [show 20 = 17 + 3 from rfl, drop_add, code_drop17, List.drop_left' (emitPush2_length reqOPc)]

theorem code_drop21 :
    code.drop 21 =
      [Opcode.toByte .JUMPDEST] ++ (zeroRevertBytes ++ ([Opcode.toByte .JUMPDEST] ++
        (prefixBytes ++ (checkedAddBytes ++ tailBytes)))) := by
  rw [show 21 = 20 + 1 from rfl, drop_add, code_drop20]; rfl

theorem code_drop22 :
    code.drop 22 =
      zeroRevertBytes ++ ([Opcode.toByte .JUMPDEST] ++
        (prefixBytes ++ (checkedAddBytes ++ tailBytes))) := by
  rw [show 22 = 21 + 1 from rfl, drop_add, code_drop21]; rfl

theorem code_drop61 :
    code.drop 61 =
      [Opcode.toByte .JUMPDEST] ++ (prefixBytes ++ (checkedAddBytes ++ tailBytes)) := by
  rw [show 61 = 22 + 39 from rfl, drop_add, code_drop22, List.drop_left' zeroRevertBytes_length]

theorem code_drop62 :
    code.drop 62 = prefixBytes ++ (checkedAddBytes ++ tailBytes) := by
  rw [show 62 = 61 + 1 from rfl, drop_add, code_drop61]; rfl

theorem code_drop73 :
    code.drop 73 = checkedAddBytes ++ tailBytes := by
  rw [show 73 = 62 + 11 from rfl, drop_add, code_drop62, List.drop_left' prefixBytes_length]

theorem code_drop73_spine :
    code.drop 73 =
      [0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 addRPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 addOPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes))))))) := by
  rw [code_drop73]
  simp [checkedAddBytes, List.append_assoc]

theorem code_drop78 :
    code.drop 78 =
      emitPush2 addRPc ++ (Opcode.toByte .JUMPI :: (emitPush2 addOPc ++
        (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
          (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))))) := by
  rw [show 78 = 73 + 5 from rfl, drop_add, code_drop73_spine]
  rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]

theorem code_drop81 :
    code.drop 81 =
      Opcode.toByte .JUMPI :: (emitPush2 addOPc ++ (Opcode.toByte .JUMP ::
        (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++
          (Opcode.toByte .JUMPDEST :: tailBytes))))) := by
  rw [show 81 = 78 + 3 from rfl, drop_add, code_drop78, List.drop_left' (emitPush2_length addRPc)]

theorem code_drop82 :
    code.drop 82 =
      emitPush2 addOPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))) := by
  rw [show 82 = 81 + 1 from rfl, drop_add, code_drop81]; rfl

theorem code_drop85 :
    code.drop 85 =
      Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes))) := by
  rw [show 85 = 82 + 3 from rfl, drop_add, code_drop82, List.drop_left' (emitPush2_length addOPc)]

theorem code_drop86 :
    code.drop 86 =
      Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ Opcode.toByte .JUMPDEST :: tailBytes) := by
  rw [show 86 = 85 + 1 from rfl, drop_add, code_drop85]; rfl

theorem code_drop131 :
    code.drop 131 = Opcode.toByte .JUMPDEST :: tailBytes := by
  rw [show 131 = 86 + 45 from rfl, drop_add, code_drop86]
  rw [show 45 = 44 + 1 from rfl, List.drop_succ_cons]
  rw [List.drop_left' IncBody.panicBytes_length]

theorem code_drop132 : code.drop 132 = tailBytes := by
  rw [show 132 = 131 + 1 from rfl, drop_add, code_drop131]; rfl

theorem tail_drop13 :
    tailBytes.drop 13 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] :=
  rfl

theorem code_drop145 :
    code.drop 145 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] := by
  rw [show 145 = 132 + 13 from rfl, drop_add, code_drop132, tail_drop13]

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 2) := by
  have h : code.drop 0 = 0x60 :: 4 :: code.drop 2 := by
    simp [code, loadParamBytes]
  have h' := decodeAt_of_drop h (decodeAt_push1_head (4 : UInt8) (code.drop 2))
  simpa [wrap] using h'

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .CALLDATALOAD }, 3) := by
  have h : code.drop 2 = Opcode.toByte .CALLDATALOAD :: code.drop 3 := by
    simp [code, loadParamBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_calldataload_head _)

theorem decode_pc3 :
    decodeAt code 3 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 5) := by
  have hdrop : code.drop 3 = 0x60 :: 0x80 :: code.drop 5 := by
    simp [code, loadParamBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 5))
  simpa [wrap, localBase] using h

theorem decode_pc5 :
    decodeAt code 5 = some ({ op := .MSTORE }, 6) := by
  have h : code.drop 5 = Opcode.toByte .MSTORE :: code.drop 6 := by
    simp [code, loadParamBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc6 :
    decodeAt code 6 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 8) := by
  have h := decodeAt_of_drop code_drop6_push (decodeAt_push1_head (0x80 : UInt8) (code.drop 8))
  simpa [wrap, localBase] using h

theorem decode_pc8 :
    decodeAt code 8 = some ({ op := .MLOAD }, 9) :=
  decodeAt_of_drop code_drop8 (decodeAt_mload_head _)

theorem decode_pc9 :
    decodeAt code 9 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 10) :=
  decodeAt_of_drop code_drop9 (decodeAt_push0_head _)

theorem decode_pc10 :
    decodeAt code 10 = some ({ op := .EQ }, 11) :=
  decodeAt_of_drop code_drop10 (decodeAt_eq_head _)

theorem decode_pc11 :
    decodeAt code 11 = some ({ op := .ISZERO }, 12) :=
  decodeAt_of_drop code_drop11 (decodeAt_iszero_head _)

theorem decode_pc12 :
    decodeAt code 12 = some ({ op := .ISZERO }, 13) :=
  decodeAt_of_drop code_drop12 (decodeAt_iszero_head _)

theorem decode_pc13 :
    decodeAt code 13 = some ({ op := .PUSH ⟨2, by decide⟩, imm := reqRPc }, 16) := by
  have hdrop : code.drop 13 = emitPush2 reqRPc ++ code.drop 16 := by
    rw [code_drop13, code_drop16]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 reqRPc _)
  simpa [reqRPc_mod] using h

theorem decode_pc16 :
    decodeAt code 16 = some ({ op := .JUMPI }, 17) := by
  have h : code.drop 16 = Opcode.toByte .JUMPI :: code.drop 17 := code_drop16
  exact decodeAt_of_drop h (decodeAt_jumpi_head _)

theorem decode_pc17 :
    decodeAt code 17 = some ({ op := .PUSH ⟨2, by decide⟩, imm := reqOPc }, 20) := by
  have hdrop : code.drop 17 = emitPush2 reqOPc ++ code.drop 20 := by
    rw [code_drop17, code_drop20]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 reqOPc _)
  simpa [reqOPc_mod] using h

theorem decode_pc20 :
    decodeAt code 20 = some ({ op := .JUMP }, 21) := by
  have h : code.drop 20 = Opcode.toByte .JUMP :: code.drop 21 := code_drop20
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem decode_pc21 :
    decodeAt code 21 = some ({ op := .JUMPDEST }, 22) := by
  exact decodeAt_of_drop code_drop21 (decodeAt_jumpdest_head _)

theorem decode_pc22 :
    decodeAt code 22 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap (zeroSel * 2 ^ 224) }, 55) := by
  have hdrop : code.drop 22 =
      emitPush32 (zeroSel * 2 ^ 224) ++
        ([0x5f, 0x52, 0x60, 4, 0x5f, 0xfd] ++ ([Opcode.toByte .JUMPDEST] ++
          (prefixBytes ++ (checkedAddBytes ++ tailBytes)))) := by
    rw [code_drop22, zeroRevertBytes, List.append_assoc]
  have h := decodeAt_of_drop hdrop (decodeAt_push32 (zeroSel * 2 ^ 224) _)
  simpa using h

theorem decode_pc55 :
    decodeAt code 55 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 56) := by
  have h : code.drop 55 = 0x5f :: code.drop 56 := by
    rw [show 55 = 22 + 33 from rfl, drop_add, code_drop22, zeroRevertBytes, List.append_assoc]
    rw [List.drop_left' (emitPush32_length (zeroSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc56 :
    decodeAt code 56 = some ({ op := .MSTORE }, 57) := by
  have h : code.drop 56 = Opcode.toByte .MSTORE :: code.drop 57 := by
    rw [show 56 = 22 + 34 from rfl, drop_add, code_drop22, zeroRevertBytes, List.append_assoc]
    rw [show 34 = 33 + 1 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (zeroSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc57 :
    decodeAt code 57 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 59) := by
  have hdrop : code.drop 57 = 0x60 :: 4 :: code.drop 59 := by
    rw [show 57 = 22 + 35 from rfl, drop_add, code_drop22, zeroRevertBytes, List.append_assoc]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (zeroSel * 2 ^ 224))]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (4 : UInt8) (code.drop 59))
  simpa [wrap] using h

theorem decode_pc59 :
    decodeAt code 59 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 60) := by
  have h : code.drop 59 = 0x5f :: code.drop 60 := by
    rw [show 59 = 22 + 37 from rfl, drop_add, code_drop22, zeroRevertBytes, List.append_assoc]
    rw [show 37 = 33 + 4 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (zeroSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc60 :
    decodeAt code 60 = some ({ op := .REVERT }, 61) := by
  have h : code.drop 60 = 0xfd :: code.drop 61 := by
    rw [show 60 = 22 + 38 from rfl, drop_add, code_drop22, zeroRevertBytes, List.append_assoc]
    rw [show 38 = 33 + 5 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length (zeroSel * 2 ^ 224))]
    rfl
  exact decodeAt_of_drop h (decodeAt_revert_head _)

theorem decode_pc61 :
    decodeAt code 61 = some ({ op := .JUMPDEST }, 62) := by
  exact decodeAt_of_drop code_drop61 (decodeAt_jumpdest_head _)

theorem isJumpDest_reqR : isJumpDest code reqRPc = true := by
  simpa [reqRPc] using isJumpDest_of_decode decode_pc21

theorem isJumpDest_reqO : isJumpDest code reqOPc = true := by
  simpa [reqOPc] using isJumpDest_of_decode decode_pc61

theorem decode_pc62 :
    decodeAt code 62 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 63) := by
  have h : code.drop 62 = 0x5f :: code.drop 63 := by
    rw [code_drop62]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc63 :
    decodeAt code 63 = some ({ op := .SLOAD }, 64) := by
  have h : code.drop 63 = Opcode.toByte .SLOAD :: code.drop 64 := by
    rw [show 63 = 62 + 1 from rfl, drop_add, code_drop62]; rfl
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem decode_pc64 :
    decodeAt code 64 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 66) := by
  have hdrop : code.drop 64 = 0x60 :: 0xA0 :: code.drop 66 := by
    rw [show 64 = 62 + 2 from rfl, drop_add, code_drop62]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 66))
  simpa [wrap, localBase] using h

theorem decode_pc66 :
    decodeAt code 66 = some ({ op := .MSTORE }, 67) := by
  have h : code.drop 66 = Opcode.toByte .MSTORE :: code.drop 67 := by
    rw [show 66 = 62 + 4 from rfl, drop_add, code_drop62]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc67 :
    decodeAt code 67 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 69) := by
  have hdrop : code.drop 67 = 0x60 :: 0xA0 :: code.drop 69 := by
    rw [show 67 = 62 + 5 from rfl, drop_add, code_drop62]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 69))
  simpa [wrap, localBase] using h

theorem decode_pc69 :
    decodeAt code 69 = some ({ op := .MLOAD }, 70) := by
  have h : code.drop 69 = Opcode.toByte .MLOAD :: code.drop 70 := by
    rw [show 69 = 62 + 7 from rfl, drop_add, code_drop62]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc70 :
    decodeAt code 70 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 72) := by
  have hdrop : code.drop 70 = 0x60 :: 0x80 :: code.drop 72 := by
    rw [show 70 = 62 + 8 from rfl, drop_add, code_drop62]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 72))
  simpa [wrap, localBase] using h

theorem decode_pc72 :
    decodeAt code 72 = some ({ op := .MLOAD }, 73) := by
  have h : code.drop 72 = Opcode.toByte .MLOAD :: code.drop 73 := by
    rw [show 72 = 62 + 10 from rfl, drop_add, code_drop62]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc73 :
    decodeAt code 73 = some ({ op := .DUP ⟨1, by decide⟩ }, 74) := by
  have h : code.drop 73 = 0x81 :: code.drop 74 := by
    rw [code_drop73_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem decode_pc74 :
    decodeAt code 74 = some ({ op := .ADD }, 75) := by
  have h : code.drop 74 = 0x01 :: code.drop 75 := by
    rw [show 74 = 73 + 1 from rfl, drop_add, code_drop73_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_add_head _)

theorem decode_pc75 :
    decodeAt code 75 = some ({ op := .DUP ⟨0, by decide⟩ }, 76) := by
  have h : code.drop 75 = 0x80 :: code.drop 76 := by
    rw [show 75 = 73 + 2 from rfl, drop_add, code_drop73_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_dup1_head _)

theorem decode_pc76 :
    decodeAt code 76 = some ({ op := .SWAP ⟨1, by decide⟩ }, 77) := by
  have h : code.drop 76 = 0x91 :: code.drop 77 := by
    rw [show 76 = 73 + 3 from rfl, drop_add, code_drop73_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_swap2_head _)

theorem decode_pc77 :
    decodeAt code 77 = some ({ op := .GT }, 78) := by
  have h : code.drop 77 = 0x11 :: code.drop 78 := by
    rw [show 77 = 73 + 4 from rfl, drop_add, code_drop73_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_gt_head _)

theorem decode_pc78 :
    decodeAt code 78 = some ({ op := .PUSH ⟨2, by decide⟩, imm := addRPc }, 81) := by
  have hdrop : code.drop 78 = emitPush2 addRPc ++ code.drop 81 := by
    rw [code_drop78, code_drop81]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 addRPc _)
  simpa [addRPc_mod] using h

theorem decode_pc81 :
    decodeAt code 81 = some ({ op := .JUMPI }, 82) := by
  have h : code.drop 81 = Opcode.toByte .JUMPI :: code.drop 82 := code_drop81
  exact decodeAt_of_drop h (decodeAt_jumpi_head _)

theorem decode_pc82 :
    decodeAt code 82 = some ({ op := .PUSH ⟨2, by decide⟩, imm := addOPc }, 85) := by
  have hdrop : code.drop 82 = emitPush2 addOPc ++ code.drop 85 := by
    rw [code_drop82, code_drop85]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 addOPc _)
  simpa [addOPc_mod] using h

theorem decode_pc85 :
    decodeAt code 85 = some ({ op := .JUMP }, 86) := by
  have h : code.drop 85 = Opcode.toByte .JUMP :: code.drop 86 := code_drop85
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem decode_pc131 :
    decodeAt code 131 = some ({ op := .JUMPDEST }, 132) := by
  exact decodeAt_of_drop code_drop131 (decodeAt_jumpdest_head _)

theorem isJumpDest_addO : isJumpDest code addOPc = true := by
  simpa [addOPc] using isJumpDest_of_decode decode_pc131

theorem decode_pc132 :
    decodeAt code 132 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 64 }, 134) := by
  have hdrop : code.drop 132 = 0x60 :: 0xC0 :: code.drop 134 := by
    rw [code_drop132]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xC0 : UInt8) (code.drop 134))
  simpa [wrap, localBase] using h

theorem decode_pc134 :
    decodeAt code 134 = some ({ op := .MSTORE }, 135) := by
  have h : code.drop 134 = Opcode.toByte .MSTORE :: code.drop 135 := by
    rw [show 134 = 132 + 2 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc135 :
    decodeAt code 135 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 64 }, 137) := by
  have hdrop : code.drop 135 = 0x60 :: 0xC0 :: code.drop 137 := by
    rw [show 135 = 132 + 3 from rfl, drop_add, code_drop132]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xC0 : UInt8) (code.drop 137))
  simpa [wrap, localBase] using h

theorem decode_pc137 :
    decodeAt code 137 = some ({ op := .MLOAD }, 138) := by
  have h : code.drop 137 = Opcode.toByte .MLOAD :: code.drop 138 := by
    rw [show 137 = 132 + 5 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc138 :
    decodeAt code 138 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 139) := by
  have h : code.drop 138 = 0x5f :: code.drop 139 := by
    rw [show 138 = 132 + 6 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc139 :
    decodeAt code 139 = some ({ op := .SSTORE }, 140) := by
  have h : code.drop 139 = Opcode.toByte .SSTORE :: code.drop 140 := by
    rw [show 139 = 132 + 7 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_sstore_head _)

theorem decode_pc140 :
    decodeAt code 140 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 142) := by
  have hdrop : code.drop 140 = 0x60 :: 0x80 :: code.drop 142 := by
    rw [show 140 = 132 + 8 from rfl, drop_add, code_drop132]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 142))
  simpa [wrap, localBase] using h

theorem decode_pc142 :
    decodeAt code 142 = some ({ op := .MLOAD }, 143) := by
  have h : code.drop 142 = Opcode.toByte .MLOAD :: code.drop 143 := by
    rw [show 142 = 132 + 10 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc143 :
    decodeAt code 143 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 144) := by
  have h : code.drop 143 = 0x5f :: code.drop 144 := by
    rw [show 143 = 132 + 11 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc144 :
    decodeAt code 144 = some ({ op := .MSTORE }, 145) := by
  have h : code.drop 144 = Opcode.toByte .MSTORE :: code.drop 145 := by
    rw [show 144 = 132 + 12 from rfl, drop_add, code_drop132]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc145 :
    decodeAt code 145 = some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 178) := by
  have h := decodeAt_of_drop code_drop145 (decodeAt_push32 incTopic _)
  simpa using h

theorem decode_pc178 :
    decodeAt code 178 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 180) := by
  have hdrop : code.drop 178 = 0x60 :: 0x20 :: code.drop 180 := by
    rw [show 178 = 145 + 33 from rfl, drop_add, code_drop145]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x20 : UInt8) (code.drop 180))
  simpa [wrap] using h

theorem decode_pc180 :
    decodeAt code 180 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 181) := by
  have h : code.drop 180 = 0x5f :: code.drop 181 := by
    rw [show 180 = 145 + 35 from rfl, drop_add, code_drop145]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc181 :
    decodeAt code 181 = some ({ op := .LOG ⟨1, by decide⟩ }, 182) := by
  have h : code.drop 181 = 0xa1 :: code.drop 182 := by
    rw [show 181 = 145 + 36 from rfl, drop_add, code_drop145]
    rw [show 36 = 33 + 3 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_log1_head _)

theorem decode_pc182 :
    decodeAt code 182 = some ({ op := .STOP }, 183) := by
  have h : code.drop 182 = 0x00 :: code.drop 183 := by
    rw [show 182 = 145 + 37 from rfl, drop_add, code_drop145]
    rw [show 37 = 33 + 4 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_stop_head _)

def env (arg : Nat) : Env :=
  { code := code, calldata := packCall 0 [arg], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

abbrev memP (n arg : Nat) : Mem := memStore (st0 n).mem localBase (wrap arg)
abbrev mem1 (n arg : Nat) : Mem := memStore (memP n arg) (localBase + 32) n
abbrev mem2 (n arg : Nat) (v : Nat) : Mem := memStore (mem1 n arg) (localBase + 64) v
abbrev mem3 (n arg : Nat) (v : Nat) : Mem := memStore (mem2 n arg v) 0 (wrap arg)
abbrev stor1 (n arg : Nat) : EVM.Storage :=
  fun k => if k = 0 then n + arg else (st0 n).storage k
abbrev log1 (n arg v : Nat) : List Log :=
  [{ topics := [wrap incTopic]
     data := (List.range 32).map fun i => memGet (mem3 n arg v) (0 + i) }]

theorem memLoad_mem1_param (n arg : Nat) :
    memLoad (mem1 n arg) localBase = wrap arg := by
  unfold mem1
  rw [memLoad_memStore_ne (m := memP n arg) (off := localBase + 32) (v := n)
    (off' := localBase)]
  · rw [memP, IncBody.memLoad_memStore, wrap_wrap]
  · exact Or.inl (Nat.le_refl _)

theorem memLoad_mem2_param (n arg v : Nat) :
    memLoad (mem2 n arg v) localBase = wrap arg := by
  unfold mem2
  rw [memLoad_memStore_ne (m := mem1 n arg) (off := localBase + 64) (v := v)
    (off' := localBase)]
  · exact memLoad_mem1_param n arg
  · refine Or.inl ?_
    simp [localBase]

/-- Matching `incrementBy arg`: STOP with slot 0 equal to `n + arg` (`arg ≠ 0`, no overflow). -/
theorem incBy_hit (n arg : Nat) (hnz : arg ≠ 0) (h : n + arg < wordBound) :
    (match run 55 (env arg) (st0 n) with
    | some (Halt.stop, s) => s.storage 0 = n + arg
    | _ => False) := by
  have hn : n < wordBound := Nat.lt_of_le_of_lt (Nat.le_add_right n arg) h
  have harg : arg < wordBound := Nat.lt_of_le_of_lt (Nat.le_add_left arg n) h
  have hwrapn : wrap n = n := Nat.mod_eq_of_lt hn
  have hwrapa : wrap arg = arg := Nat.mod_eq_of_lt harg
  have hadd : addW n arg = n + arg := addW_of_lt h
  have hval : wrap (addW n arg) = n + arg := by rw [hadd]; exact Nat.mod_eq_of_lt h
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
      StepResult.next { st0 n with mem := mem1 n arg, stack := [0, addW (wrap n) (wrap arg)], pc := 78 } := by
    have hs := step_gt e { st0 n with mem := mem1 n arg, stack := [wrap n, addW (wrap n) (wrap arg), addW (wrap n) (wrap arg)], pc := 77 }
      (wrap n) (addW (wrap n) (wrap arg)) [addW (wrap n) (wrap arg)] decode_pc77 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) (wrap arg)) = 0 := by
      rw [hwrapn, hwrapa]; exact gtW_add_of_lt h
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 27 e _ _ s77]
  have s78 : step e { st0 n with mem := mem1 n arg, stack := [0, addW (wrap n) (wrap arg)], pc := 78 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addRPc, 0, addW (wrap n) (wrap arg)], pc := 81 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [0, addW (wrap n) (wrap arg)], pc := 78 }
      addRPc decode_pc78 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s78]
  have s81 : step e { st0 n with mem := mem1 n arg, stack := [addRPc, 0, addW (wrap n) (wrap arg)], pc := 81 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 82 } := by
    have hs := step_jumpi_zero e
      { st0 n with mem := mem1 n arg, stack := [addRPc, 0, addW (wrap n) (wrap arg)], pc := 81 }
      addRPc [addW (wrap n) (wrap arg)] decode_pc81 rfl
    simpa using hs
  rw [run_of_next 25 e _ _ s81]
  have s82 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 82 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addOPc, addW (wrap n) (wrap arg)], pc := 85 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 82 }
      addOPc decode_pc82 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 24 e _ _ s82]
  have s85 : step e { st0 n with mem := mem1 n arg, stack := [addOPc, addW (wrap n) (wrap arg)], pc := 85 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addOPc } := by
    have hs := step_jump e { st0 n with mem := mem1 n arg, stack := [addOPc, addW (wrap n) (wrap arg)], pc := 85 }
      addOPc [addW (wrap n) (wrap arg)] decode_pc85 rfl isJumpDest_addO
    simpa [env] using hs
  rw [run_of_next 23 e _ _ s85]
  have s131 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addOPc } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 132 } :=
    step_jumpdest e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := addOPc }
      (by simpa [env, addOPc] using decode_pc131)
  rw [run_of_next 22 e _ _ s131]
  have s132 : step e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 132 } =
      StepResult.next { st0 n with mem := mem1 n arg, stack := [localBase + 64, addW (wrap n) (wrap arg)], pc := 134 } := by
    have hs := step_push e { st0 n with mem := mem1 n arg, stack := [addW (wrap n) (wrap arg)], pc := 132 }
      (localBase + 64) decode_pc132 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 21 e _ _ s132]
  have s134 : step e { st0 n with mem := mem1 n arg, stack := [localBase + 64, addW (wrap n) (wrap arg)], pc := 134 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 135 } :=
    step_mstore e { st0 n with mem := mem1 n arg, stack := [localBase + 64, addW (wrap n) (wrap arg)], pc := 134 }
      (localBase + 64) (addW (wrap n) (wrap arg)) [] decode_pc134 rfl
  rw [run_of_next 20 e _ _ s134]
  have s135 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 135 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [localBase + 64], pc := 137 } := by
    have hs := step_push e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 135 }
      (localBase + 64) decode_pc135 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 19 e _ _ s135]
  have s137 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [localBase + 64], pc := 137 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [n + arg], pc := 138 } := by
    have hs := step_mload e
      { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [localBase + 64], pc := 137 }
      (localBase + 64) [] decode_pc137 rfl (list_length_lt_1024 (k := 0) rfl)
    have hload : memLoad (mem2 n arg (addW (wrap n) (wrap arg))) (localBase + 64) = n + arg := by
      unfold mem2
      rw [IncBody.memLoad_memStore, hwrapn, hwrapa, hval]
    rw [hload] at hs
    exact hs
  rw [run_of_next 18 e _ _ s137]
  have s138 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [n + arg], pc := 138 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [0, n + arg], pc := 139 } := by
    have hs := step_push e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [n + arg], pc := 138 }
      0 decode_pc138 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 17 e _ _ s138]
  have s139 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [0, n + arg], pc := 139 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 140 } :=
    step_sstore e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), stack := [0, n + arg], pc := 139 }
      0 (n + arg) [] decode_pc139 rfl
  rw [run_of_next 16 e _ _ s139]
  have s140 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 140 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [localBase], pc := 142 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 140 }
      localBase decode_pc140 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 15 e _ _ s140]
  have s142 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [localBase], pc := 142 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap arg], pc := 143 } := by
    have hs := step_mload e
      { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [localBase], pc := 142 }
      localBase [] decode_pc142 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [memLoad_mem2_param] using hs
  rw [run_of_next 14 e _ _ s142]
  have s143 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap arg], pc := 143 } =
      StepResult.next { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, wrap arg], pc := 144 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap arg], pc := 143 }
      0 decode_pc143 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 13 e _ _ s143]
  have s144 : step e { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, wrap arg], pc := 144 } =
      StepResult.next { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 145 } :=
    step_mstore e
      { st0 n with mem := mem2 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, wrap arg], pc := 144 }
      0 (wrap arg) [] decode_pc144 rfl
  rw [run_of_next 12 e _ _ s144]
  have s145 : step e { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 145 } =
      StepResult.next { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap incTopic], pc := 178 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [], pc := 145 }
      (wrap incTopic) decode_pc145 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 11 e _ _ s145]
  have s178 : step e { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap incTopic], pc := 178 } =
      StepResult.next { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [32, wrap incTopic], pc := 180 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [wrap incTopic], pc := 178 }
      32 decode_pc178 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 10 e _ _ s178]
  have s180 : step e { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [32, wrap incTopic], pc := 180 } =
      StepResult.next { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, 32, wrap incTopic], pc := 181 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [32, wrap incTopic], pc := 180 }
      0 decode_pc180 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 9 e _ _ s180]
  have s181 : step e { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, 32, wrap incTopic], pc := 181 } =
      StepResult.next { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, logs := log1 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 182 } := by
    have hs := step_log1 e
      { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, stack := [0, 32, wrap incTopic], pc := 181 }
      0 32 (wrap incTopic) [] decode_pc181 rfl
    simpa [log1] using hs
  rw [run_of_next 8 e _ _ s181]
  have s182 : step e { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, logs := log1 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 182 } =
      StepResult.halt Halt.stop { st0 n with mem := mem3 n arg (addW (wrap n) (wrap arg)), storage := stor1 n arg, logs := log1 n arg (addW (wrap n) (wrap arg)), stack := [], pc := 182 } :=
    step_stop e _ decode_pc182
  rw [run_of_halt 7 e _ _ _ s182]
  simp [stor1]

/-- `incrementBy 0` reverts; storage is unchanged. -/
theorem incBy_zero (n : Nat) :
    (match run 25 (env 0) (st0 n) with
    | some (Halt.revert _, s) => s.storage 0 = n
    | _ => False) := by
  have hcd : calldataLoad (packCall 0 [0]) 4 = wrap 0 := calldataLoad_packCall_arg 0 0
  have hwrap0 : wrap 0 = 0 := rfl
  let e := env 0
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 24 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall 0 [0]) 4], pc := 3 } := by
    have hs := step_calldataload e { st0 n with stack := [4], pc := 2 } 4 []
      decode_pc2 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using hs
  rw [run_of_next 23 e _ _ s2]
  have s3 : step e { st0 n with stack := [calldataLoad (packCall 0 [0]) 4], pc := 3 } =
      StepResult.next { st0 n with stack := [localBase, calldataLoad (packCall 0 [0]) 4], pc := 5 } := by
    have hs := step_push e { st0 n with stack := [calldataLoad (packCall 0 [0]) 4], pc := 3 }
      localBase decode_pc3 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 22 e _ _ s3]
  have s5 : step e { st0 n with stack := [localBase, calldataLoad (packCall 0 [0]) 4], pc := 5 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [], pc := 6 } := by
    have hs := step_mstore e { st0 n with stack := [localBase, calldataLoad (packCall 0 [0]) 4], pc := 5 }
      localBase (calldataLoad (packCall 0 [0]) 4) [] decode_pc5 rfl
    simpa [env, memP, hcd] using hs
  rw [run_of_next 21 e _ _ s5]
  have s6 : step e { st0 n with mem := memP n 0, stack := [], pc := 6 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [localBase], pc := 8 } := by
    have hs := step_push e { st0 n with mem := memP n 0, stack := [], pc := 6 }
      localBase decode_pc6 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 20 e _ _ s6]
  have s8 : step e { st0 n with mem := memP n 0, stack := [localBase], pc := 8 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [0], pc := 9 } := by
    have hs := step_mload e { st0 n with mem := memP n 0, stack := [localBase], pc := 8 }
      localBase [] decode_pc8 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore, hwrap0] using hs
  rw [run_of_next 19 e _ _ s8]
  have s9 : step e { st0 n with mem := memP n 0, stack := [0], pc := 9 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [0, 0], pc := 10 } := by
    have hs := step_push e { st0 n with mem := memP n 0, stack := [0], pc := 9 }
      0 decode_pc9 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 18 e _ _ s9]
  have s10 : step e { st0 n with mem := memP n 0, stack := [0, 0], pc := 10 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [1], pc := 11 } := by
    have hs := step_eq e { st0 n with mem := memP n 0, stack := [0, 0], pc := 10 }
      0 0 [] decode_pc10 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [eqW_self] using hs
  rw [run_of_next 17 e _ _ s10]
  have s11 : step e { st0 n with mem := memP n 0, stack := [1], pc := 11 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [0], pc := 12 } := by
    have hs := step_iszero e { st0 n with mem := memP n 0, stack := [1], pc := 11 }
      1 [] decode_pc11 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 16 e _ _ s11]
  have s12 : step e { st0 n with mem := memP n 0, stack := [0], pc := 12 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [1], pc := 13 } := by
    have hs := step_iszero e { st0 n with mem := memP n 0, stack := [0], pc := 12 }
      0 [] decode_pc12 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 15 e _ _ s12]
  have s13 : step e { st0 n with mem := memP n 0, stack := [1], pc := 13 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [reqRPc, 1], pc := 16 } := by
    have hs := step_push e { st0 n with mem := memP n 0, stack := [1], pc := 13 }
      reqRPc decode_pc13 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 14 e _ _ s13]
  have s16 : step e { st0 n with mem := memP n 0, stack := [reqRPc, 1], pc := 16 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [], pc := reqRPc } := by
    have hs := step_jumpi_nz e { st0 n with mem := memP n 0, stack := [reqRPc, 1], pc := 16 }
      reqRPc 1 [] decode_pc16 rfl (by decide) isJumpDest_reqR
    simpa [env] using hs
  rw [run_of_next 13 e _ _ s16]
  have s21 : step e { st0 n with mem := memP n 0, stack := [], pc := reqRPc } =
      StepResult.next { st0 n with mem := memP n 0, stack := [], pc := 22 } :=
    step_jumpdest e { st0 n with mem := memP n 0, stack := [], pc := reqRPc }
      (by simpa [env, reqRPc] using decode_pc21)
  rw [run_of_next 12 e _ _ s21]
  have s22 : step e { st0 n with mem := memP n 0, stack := [], pc := 22 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [wrap (zeroSel * 2 ^ 224)], pc := 55 } := by
    have hs := step_push e { st0 n with mem := memP n 0, stack := [], pc := 22 }
      (wrap (zeroSel * 2 ^ 224)) decode_pc22 (list_length_lt_1024 (k := 0) rfl)
    simpa [env] using hs
  rw [run_of_next 11 e _ _ s22]
  have s55 : step e { st0 n with mem := memP n 0, stack := [wrap (zeroSel * 2 ^ 224)], pc := 55 } =
      StepResult.next { st0 n with mem := memP n 0, stack := [0, wrap (zeroSel * 2 ^ 224)], pc := 56 } := by
    have hs := step_push e { st0 n with mem := memP n 0, stack := [wrap (zeroSel * 2 ^ 224)], pc := 55 }
      0 decode_pc55 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 10 e _ _ s55]
  have s56 : step e { st0 n with mem := memP n 0, stack := [0, wrap (zeroSel * 2 ^ 224)], pc := 56 } =
      StepResult.next { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [], pc := 57 } :=
    step_mstore e { st0 n with mem := memP n 0, stack := [0, wrap (zeroSel * 2 ^ 224)], pc := 56 }
      0 (wrap (zeroSel * 2 ^ 224)) [] decode_pc56 rfl
  rw [run_of_next 9 e _ _ s56]
  have s57 : step e { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [], pc := 57 } =
      StepResult.next { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [4], pc := 59 } := by
    have hs := step_push e
      { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [], pc := 57 }
      4 decode_pc57 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 8 e _ _ s57]
  have s59 : step e { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [4], pc := 59 } =
      StepResult.next { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [0, 4], pc := 60 } := by
    have hs := step_push e
      { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [4], pc := 59 }
      0 decode_pc59 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 7 e _ _ s59]
  have s60 : step e { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [0, 4], pc := 60 } =
      StepResult.halt
        (.revert ((List.range 4).map fun i =>
          memGet (memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224))) (0 + i)))
        { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [0, 4], pc := 60 } := by
    have hs := step_revert e
      { st0 n with mem := memStore (memP n 0) 0 (wrap (zeroSel * 2 ^ 224)), stack := [0, 4], pc := 60 }
      0 4 [] decode_pc60 rfl
    simpa using hs
  rw [run_of_halt 6 e _ _ _ s60]
  simp [st0]

end Lsc3.Compile.IncByBody
