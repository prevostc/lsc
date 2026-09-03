import Lsc3.Compile.GetIncHit
import Lsc3.Compile.IncContract
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# Matching-selector `increment` on the two-function compiler

Calldata is `packCall iSel []`. The get branch EQ is 0 (`gSel` and `iSel` differ
in the low 32 bits); the increment branch EQ is 1 and jumps to PC 91. The body
is `IncContract.bodyBytes` shifted to PC 92 (checked-add destinations 115 and 160).

`getInc_inc_hit` — apply it; do not instantiate at `selectorOf`.
-/

namespace Lsc3.Compile.GetInc

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Jump
open Lsc3.Compile.DispatchGet (push4Bytes decodeAt_push4)
open Lsc3.Compile.IncContract (tailBytes incTopic)

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_drop28 (gSel iSel : Nat) :
    (code gSel iSel).drop 28 =
      emitPush4 iSel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
              ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))))) := by
  rw [show 28 = 23 + 5 from rfl, drop_add, code_drop23]
  simp [branchIncBytes, List.append_assoc]
  try rw [List.drop_left' GetContract.loadSelBytes_length]

theorem code_drop33 (gSel iSel : Nat) :
    (code gSel iSel).drop 33 =
      [Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
              ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))))) := by
  rw [show 33 = 28 + 5 from rfl, drop_add, code_drop28, List.drop_left' (emitPush4_length iSel)]

theorem code_drop34 (gSel iSel : Nat) :
    (code gSel iSel).drop 34 =
      emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))) := by
  rw [show 34 = 33 + 1 from rfl, drop_add, code_drop33]; rfl

theorem code_drop37 (gSel iSel : Nat) :
    (code gSel iSel).drop 37 =
      [Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (GetBody.code ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))) := by
  rw [show 37 = 34 + 3 from rfl, drop_add, code_drop34, List.drop_left' (emitPush2_length incPc)]

theorem code_drop91 (gSel iSel : Nat) :
    (code gSel iSel).drop 91 = [Opcode.toByte .JUMPDEST] ++ bodyBytes := by
  rw [show 91 = 83 + 8 from rfl, drop_add, code_drop83, List.drop_left' getBody_code_length]

theorem code_drop92 (gSel iSel : Nat) :
    (code gSel iSel).drop 92 = bodyBytes := by
  rw [show 92 = 91 + 1 from rfl, drop_add, code_drop91]; rfl

def incPre (gSel iSel : Nat) : List UInt8 :=
  checkBytes ++ branchGetBytes gSel ++ branchIncBytes iSel ++ fallBytes ++
    [Opcode.toByte .JUMPDEST] ++ revertBytes ++ [Opcode.toByte .JUMPDEST] ++
    GetBody.code ++ [Opcode.toByte .JUMPDEST]

@[simp] theorem incPre_length (gSel iSel : Nat) : (incPre gSel iSel).length = 92 := by
  simp [incPre]

theorem code_incPre (gSel iSel : Nat) :
    code gSel iSel = incPre gSel iSel ++ bodyBytes := by
  simp [code, incPre, List.append_assoc]

theorem decode_pc23 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 23 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 24) := by
  have h : (code gSel iSel).drop 23 = 0x5f :: (code gSel iSel).drop 24 := by
    rw [show 24 = 23 + 1 from rfl, drop_add, code_drop23]
    simp [branchIncBytes, loadSelBytes, GetContract.loadSelBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc24 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 24 = some ({ op := .CALLDATALOAD }, 25) := by
  have h : (code gSel iSel).drop 24 = Opcode.toByte .CALLDATALOAD :: (code gSel iSel).drop 25 := by
    rw [show 24 = 23 + 1 from rfl, show 25 = 23 + 2 from rfl, drop_add, drop_add, code_drop23]
    simp [branchIncBytes, loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc25 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 25 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 27) := by
  have hdrop : (code gSel iSel).drop 25 = 0x60 :: 0xE0 :: (code gSel iSel).drop 27 := by
    rw [show 25 = 23 + 2 from rfl, show 27 = 23 + 4 from rfl, drop_add, drop_add, code_drop23]
    simp [branchIncBytes, loadSelBytes, GetContract.loadSelBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) ((code gSel iSel).drop 27))
  simpa [wrap] using h

theorem decode_pc27 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 27 = some ({ op := .SHR }, 28) := by
  have h : (code gSel iSel).drop 27 = Opcode.toByte .SHR :: (code gSel iSel).drop 28 := by
    rw [show 27 = 23 + 4 from rfl, drop_add, code_drop23, code_drop28]
    simp [branchIncBytes, loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .SHR _ rfl)

theorem decode_pc28 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 28 =
      some ({ op := .PUSH ⟨4, by decide⟩, imm := iSel % 2 ^ 32 }, 33) := by
  have hdrop : (code gSel iSel).drop 28 = emitPush4 iSel ++ (code gSel iSel).drop 33 := by
    rw [code_drop28, code_drop33]
  rw [emitPush4_eq_push4] at hdrop
  have h := decodeAt_of_drop hdrop (decodeAt_push4 iSel _)
  simpa using h

theorem decode_pc33 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 33 = some ({ op := .EQ }, 34) := by
  have h : (code gSel iSel).drop 33 = Opcode.toByte .EQ :: (code gSel iSel).drop 34 := by
    rw [code_drop33, code_drop34]; rfl
  exact decodeAt_of_drop h (decodeAt_op_head .EQ _ rfl)

theorem decode_pc34 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 34 = some ({ op := .PUSH ⟨2, by decide⟩, imm := incPc }, 37) := by
  have hdrop : (code gSel iSel).drop 34 = emitPush2 incPc ++ (code gSel iSel).drop 37 := by
    rw [code_drop34, code_drop37]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 incPc _)
  simpa [incPc_mod] using h

theorem decode_pc37 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 37 = some ({ op := .JUMPI }, 38) := by
  have h : (code gSel iSel).drop 37 = Opcode.toByte .JUMPI :: (code gSel iSel).drop 38 := by
    rw [code_drop37]; rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc91 (gSel iSel : Nat) :
    decodeAt (code gSel iSel) 91 = some ({ op := .JUMPDEST }, 92) := by
  have h : (code gSel iSel).drop 91 = Opcode.toByte .JUMPDEST :: bodyBytes := by
    rw [code_drop91]; rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem isJumpDest_inc (gSel iSel : Nat) : isJumpDest (code gSel iSel) incPc = true := by
  simpa [incPc] using isJumpDest_of_decode (decode_pc91 gSel iSel)

theorem body_spine :
    bodyBytes =
      IncBody.prefixBytes ++ ([0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 bodyRevPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes)))))))) := by
  simp [bodyBytes, checkedAddBytes, List.append_assoc]

theorem body_drop10 :
    bodyBytes.drop 10 =
      [0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 bodyRevPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes))))))) := by
  rw [body_spine, List.drop_left' IncBody.prefixBytes_length]

theorem bdec0 :
    decodeAt bodyBytes 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  have h : bodyBytes.drop 0 = 0x5f :: bodyBytes.drop 1 := by
    simp [bodyBytes, IncBody.prefixBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem bdec1 :
    decodeAt bodyBytes 1 = some ({ op := .SLOAD }, 2) := by
  have h : bodyBytes.drop 1 = Opcode.toByte .SLOAD :: bodyBytes.drop 2 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem bdec2 :
    decodeAt bodyBytes 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 4) := by
  have hdrop : bodyBytes.drop 2 = 0x60 :: 0x80 :: bodyBytes.drop 4 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (bodyBytes.drop 4))
  simpa [wrap, localBase] using h

theorem bdec4 :
    decodeAt bodyBytes 4 = some ({ op := .MSTORE }, 5) := by
  have h : bodyBytes.drop 4 = Opcode.toByte .MSTORE :: bodyBytes.drop 5 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem bdec5 :
    decodeAt bodyBytes 5 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 7) := by
  have hdrop : bodyBytes.drop 5 = 0x60 :: 0x80 :: bodyBytes.drop 7 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (bodyBytes.drop 7))
  simpa [wrap, localBase] using h

theorem bdec7 :
    decodeAt bodyBytes 7 = some ({ op := .MLOAD }, 8) := by
  have h : bodyBytes.drop 7 = Opcode.toByte .MLOAD :: bodyBytes.drop 8 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem bdec8 :
    decodeAt bodyBytes 8 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 10) := by
  have hdrop : bodyBytes.drop 8 = 0x60 :: 1 :: bodyBytes.drop 10 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (bodyBytes.drop 10))
  simpa [wrap] using h

theorem bdec10 :
    decodeAt bodyBytes 10 = some ({ op := .DUP ⟨1, by decide⟩ }, 11) := by
  have h : bodyBytes.drop 10 = 0x81 :: bodyBytes.drop 11 := by
    rw [body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem bdec11 :
    decodeAt bodyBytes 11 = some ({ op := .ADD }, 12) := by
  have h : bodyBytes.drop 11 = 0x01 :: bodyBytes.drop 12 := by
    rw [show 11 = 10 + 1 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_add_head _)

theorem bdec12 :
    decodeAt bodyBytes 12 = some ({ op := .DUP ⟨0, by decide⟩ }, 13) := by
  have h : bodyBytes.drop 12 = 0x80 :: bodyBytes.drop 13 := by
    rw [show 12 = 10 + 2 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup1_head _)

theorem bdec13 :
    decodeAt bodyBytes 13 = some ({ op := .SWAP ⟨1, by decide⟩ }, 14) := by
  have h : bodyBytes.drop 13 = 0x91 :: bodyBytes.drop 14 := by
    rw [show 13 = 10 + 3 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_swap2_head _)

theorem bdec14 :
    decodeAt bodyBytes 14 = some ({ op := .GT }, 15) := by
  have h : bodyBytes.drop 14 = 0x11 :: bodyBytes.drop 15 := by
    rw [show 14 = 10 + 4 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_gt_head _)

theorem bdec15 :
    decodeAt bodyBytes 15 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyRevPc }, 18) := by
  have hdrop : bodyBytes.drop 15 =
      emitPush2 bodyRevPc ++ (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++
        (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
          (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))))) := by
    rw [show 15 = 10 + 5 from rfl, drop_add, body_drop10]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 bodyRevPc _)
  simpa [bodyRevPc_mod] using h

theorem bdec18 :
    decodeAt bodyBytes 18 = some ({ op := .JUMPI }, 19) := by
  have h : bodyBytes.drop 18 = Opcode.toByte .JUMPI :: bodyBytes.drop 19 := by
    rw [show 18 = 10 + 8 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jumpi_head _)

theorem bdec19 :
    decodeAt bodyBytes 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyOkPc }, 22) := by
  have hdrop : bodyBytes.drop 19 =
      emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))) := by
    rw [show 19 = 10 + 9 from rfl, drop_add, body_drop10]
    rw [show 9 = 5 + 4 from rfl, drop_add]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
    rw [show 4 = 3 + 1 from rfl, drop_add]
    rw [List.drop_left' (emitPush2_length bodyRevPc)]
    rw [List.drop_succ_cons]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push2 bodyOkPc _)
  simpa [bodyOkPc_mod] using h

theorem bdec22 :
    decodeAt bodyBytes 22 = some ({ op := .JUMP }, 23) := by
  have h : bodyBytes.drop 22 = Opcode.toByte .JUMP :: bodyBytes.drop 23 := by
    rw [show 22 = 10 + 12 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem body_drop23 :
    bodyBytes.drop 23 =
      Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ Opcode.toByte .JUMPDEST :: tailBytes) := by
  rw [show 23 = 10 + 13 from rfl, drop_add, body_drop10]
  rw [show 13 = 5 + 8 from rfl, drop_add]
  rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  rw [show 8 = 3 + 5 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length bodyRevPc)]
  rw [List.drop_succ_cons]
  rw [show 4 = 3 + 1 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length bodyOkPc)]
  rw [List.drop_succ_cons]
  rfl

theorem body_drop23_eq : bodyBytes.drop 23 = IncContract.bodyBytes.drop 23 := by
  rw [body_drop23, IncContract.body_drop23]

theorem decode_body_ge23 {pc next : Nat} {instr : Instr}
    (hpc : 23 ≤ pc)
    (hd : decodeAt IncContract.bodyBytes pc = some (instr, next)) :
    decodeAt bodyBytes pc = some (instr, next) := by
  have hpc' : pc = 23 + (pc - 23) := by omega
  have hdrop : bodyBytes.drop pc = IncContract.bodyBytes.drop pc := by
    rw [hpc', drop_add, drop_add, body_drop23_eq]
  rw [decodeAt_drop, hdrop, ← decodeAt_drop]
  exact hd

theorem bdec68 :
    decodeAt bodyBytes 68 = some ({ op := .JUMPDEST }, 69) :=
  decode_body_ge23 (by decide) IncContract.bdec68

theorem bdec69 :
    decodeAt bodyBytes 69 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 71) :=
  decode_body_ge23 (by decide) IncContract.bdec69

theorem bdec71 :
    decodeAt bodyBytes 71 = some ({ op := .MSTORE }, 72) :=
  decode_body_ge23 (by decide) IncContract.bdec71

theorem bdec72 :
    decodeAt bodyBytes 72 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 74) :=
  decode_body_ge23 (by decide) IncContract.bdec72

theorem bdec74 :
    decodeAt bodyBytes 74 = some ({ op := .MLOAD }, 75) :=
  decode_body_ge23 (by decide) IncContract.bdec74

theorem bdec75 :
    decodeAt bodyBytes 75 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 76) :=
  decode_body_ge23 (by decide) IncContract.bdec75

theorem bdec76 :
    decodeAt bodyBytes 76 = some ({ op := .SSTORE }, 77) :=
  decode_body_ge23 (by decide) IncContract.bdec76

theorem bdec77 :
    decodeAt bodyBytes 77 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 79) :=
  decode_body_ge23 (by decide) IncContract.bdec77

theorem bdec79 :
    decodeAt bodyBytes 79 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 80) :=
  decode_body_ge23 (by decide) IncContract.bdec79

theorem bdec80 :
    decodeAt bodyBytes 80 = some ({ op := .MSTORE }, 81) :=
  decode_body_ge23 (by decide) IncContract.bdec80

theorem bdec81 :
    decodeAt bodyBytes 81 = some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 114) :=
  decode_body_ge23 (by decide) IncContract.bdec81

theorem bdec114 :
    decodeAt bodyBytes 114 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 116) :=
  decode_body_ge23 (by decide) IncContract.bdec114

theorem bdec116 :
    decodeAt bodyBytes 116 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 117) :=
  decode_body_ge23 (by decide) IncContract.bdec116

theorem bdec117 :
    decodeAt bodyBytes 117 = some ({ op := .LOG ⟨1, by decide⟩ }, 118) :=
  decode_body_ge23 (by decide) IncContract.bdec117

theorem bdec118 :
    decodeAt bodyBytes 118 = some ({ op := .STOP }, 119) :=
  decode_body_ge23 (by decide) IncContract.bdec118

theorem decode_body (gSel iSel : Nat) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt bodyBytes pc = some (instr, next0)) :
    decodeAt (code gSel iSel) ((incPre gSel iSel).length + pc) =
      some (instr, next0 + (incPre gSel iSel).length) := by
  rw [code_incPre, decodeAt_append, hd]
  rfl

theorem decode_at (gSel iSel : Nat) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt bodyBytes pc = some (instr, next0)) :
    decodeAt (code gSel iSel) (92 + pc) = some (instr, next0 + 92) := by
  have h := decode_body gSel iSel hd
  simpa [incPre_length] using h

theorem isJumpDest_ok (gSel iSel : Nat) : isJumpDest (code gSel iSel) bodyOkPc = true := by
  have h := isJumpDest_of_decode (decode_at gSel iSel bdec68)
  simpa [bodyOkPc] using h

def envInc (gSel iSel : Nat) (args : List Nat) : Env :=
  { code := code gSel iSel, calldata := packCall iSel args, address := 0, caller := 0,
    callvalue := 0, timestamp := 0, number := 0 }

abbrev mem1 (n : Nat) : Mem := memStore (st0 n).mem localBase n
abbrev mem2 (n : Nat) (v : Nat) : Mem := memStore (mem1 n) (localBase + 32) v
abbrev mem3 (n : Nat) (v : Nat) : Mem := memStore (mem2 n v) 0 1
abbrev stor1 (n : Nat) : EVM.Storage := fun k => if k = 0 then n + 1 else (st0 n).storage k
abbrev log1 (n v : Nat) : List Log :=
  [{ topics := [wrap incTopic]
     data := (List.range 32).map fun i => memGet (mem3 n v) (0 + i) }]

/-- Matching increment selector: STOP with storage slot 0 equal to `n + 1` (no overflow). -/
theorem getInc_inc_hit (gSel iSel n : Nat)
    (hne : gSel % 2 ^ 32 ≠ iSel % 2 ^ 32) (h : n + 1 < wordBound) :
    (match run 58 (envInc gSel iSel []) (st0 n) with
    | some (Halt.stop, s) => s.storage 0 = n + 1
    | _ => False) := by
  have hn : n < wordBound := Nat.lt_of_succ_lt h
  have hwrap : wrap n = n := Nat.mod_eq_of_lt hn
  have hadd : addW (wrap n) 1 = n + 1 := by rw [hwrap]; exact addW_succ_of_lt h
  have hval : wrap (addW (wrap n) 1) = n + 1 := by rw [hadd]; exact Nat.mod_eq_of_lt h
  let e := envInc gSel iSel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 (decode_pc0 gSel iSel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 57 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have hs := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 56 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have hs := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at hs
    exact hs
  rw [run_of_next 55 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [revPc, 0], pc := 7 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 4 } revPc (decode_pc4 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 54 e _ _ s4]
  have s7 : step e { st0 n with stack := [revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [revPc, 0], pc := 7 }
      revPc [] (decode_pc7 gSel iSel) rfl
    simpa using hs
  rw [run_of_next 53 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have hs := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 gSel iSel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 52 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 10 } := by
    have hs := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [envInc, st0] using hs
  rw [run_of_next 51 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 12 } := by
    have hs := step_push e
      { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 10 } 0xE0 (decode_pc10 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 50 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 13 } := by
    have hs := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall iSel []) 0) [] (decode_pc12 gSel iSel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 49 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)],
            pc := 18 } := by
    have hs := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 13 }
      (gSel % 2 ^ 32) (decode_pc13 gSel iSel) (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 48 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [0], pc := 19 } := by
    have hs := step_eq e
      { st0 n with
        stack := [gSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 18 }
      (gSel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall iSel []) 0)) []
      (decode_pc18 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW] at hs ⊢
    split_ifs at hs with heq
    · exact absurd heq.symm (by simpa using hne.symm)
    · exact hs
  rw [run_of_next 47 e _ _ s18]
  have s19 : step e { st0 n with stack := [0], pc := 19 } =
      StepResult.next { st0 n with stack := [getPc, 0], pc := 22 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 19 } getPc (decode_pc19 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 46 e _ _ s19]
  have s22 : step e { st0 n with stack := [getPc, 0], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := 23 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [getPc, 0], pc := 22 } getPc []
      (decode_pc22 gSel iSel) rfl
    simpa using hs
  rw [run_of_next 45 e _ _ s22]
  have s23 : step e { st0 n with stack := [], pc := 23 } =
      StepResult.next { st0 n with stack := [0], pc := 24 } := by
    have hs := step_push e { st0 n with stack := [], pc := 23 } 0 (decode_pc23 gSel iSel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 44 e _ _ s23]
  have s24 : step e { st0 n with stack := [0], pc := 24 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 25 } := by
    have hs := step_calldataload e { st0 n with stack := [0], pc := 24 } 0 []
      (decode_pc24 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [envInc, st0] using hs
  rw [run_of_next 43 e _ _ s24]
  have s25 :
      step e { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 25 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 27 } := by
    have hs := step_push e
      { st0 n with stack := [calldataLoad (packCall iSel []) 0], pc := 25 } 0xE0 (decode_pc25 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 42 e _ _ s25]
  have s27 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 27 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 28 } := by
    have hs := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall iSel []) 0], pc := 27 }
      0xE0 (calldataLoad (packCall iSel []) 0) [] (decode_pc27 gSel iSel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 41 e _ _ s27]
  have s28 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 28 } =
        StepResult.next
          { st0 n with
            stack := [iSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)],
            pc := 33 } := by
    have hs := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 28 }
      (iSel % 2 ^ 32) (decode_pc28 gSel iSel) (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 40 e _ _ s28]
  have s33 :
      step e
        { st0 n with
          stack := [iSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 33 } =
        StepResult.next { st0 n with stack := [1], pc := 34 } := by
    have hs := step_eq e
      { st0 n with
        stack := [iSel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall iSel []) 0)], pc := 33 }
      (iSel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall iSel []) 0)) []
      (decode_pc33 gSel iSel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at hs ⊢
    exact hs
  rw [run_of_next 39 e _ _ s33]
  have s34 : step e { st0 n with stack := [1], pc := 34 } =
      StepResult.next { st0 n with stack := [incPc, 1], pc := 37 } := by
    have hs := step_push e { st0 n with stack := [1], pc := 34 } incPc (decode_pc34 gSel iSel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 38 e _ _ s34]
  have s37 : step e { st0 n with stack := [incPc, 1], pc := 37 } =
      StepResult.next { st0 n with stack := [], pc := incPc } := by
    have hs := step_jumpi_nz e { st0 n with stack := [incPc, 1], pc := 37 } incPc 1 []
      (decode_pc37 gSel iSel) rfl (by decide) (isJumpDest_inc gSel iSel)
    simpa [envInc] using hs
  rw [run_of_next 37 e _ _ s37]
  have s91 : step e { st0 n with stack := [], pc := incPc } =
      StepResult.next { st0 n with stack := [], pc := 92 } := by
    have hdec : decodeAt e.code incPc = some ({ op := .JUMPDEST }, 92) := by
      simpa [envInc, incPc] using decode_pc91 gSel iSel
    exact step_jumpdest e { st0 n with stack := [], pc := incPc } hdec
  rw [run_of_next 36 e _ _ s91]
  have d92 : decodeAt e.code 92 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 93) := by
    simpa [envInc] using decode_at gSel iSel bdec0
  have s92 : step e { st0 n with stack := [], pc := 92 } =
      StepResult.next { st0 n with stack := [0], pc := 93 } := by
    have hs := step_push e { st0 n with stack := [], pc := 92 } 0 d92
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 35 e _ _ s92]
  have d93 : decodeAt e.code 93 = some ({ op := .SLOAD }, 94) := by
    simpa [envInc] using decode_at gSel iSel bdec1
  have s93 : step e { st0 n with stack := [0], pc := 93 } =
      StepResult.next { st0 n with stack := [n], pc := 94 } := by
    have hs := step_sload e { st0 n with stack := [0], pc := 93 } 0 [] d93 rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 34 e _ _ s93]
  have d94 : decodeAt e.code 94 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 96) := by
    simpa [envInc] using decode_at gSel iSel bdec2
  have s94 : step e { st0 n with stack := [n], pc := 94 } =
      StepResult.next { st0 n with stack := [localBase, n], pc := 96 } := by
    have hs := step_push e { st0 n with stack := [n], pc := 94 } localBase d94
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 33 e _ _ s94]
  have d96 : decodeAt e.code 96 = some ({ op := .MSTORE }, 97) := by
    simpa [envInc] using decode_at gSel iSel bdec4
  have s96 : step e { st0 n with stack := [localBase, n], pc := 96 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 97 } :=
    step_mstore e { st0 n with stack := [localBase, n], pc := 96 } localBase n [] d96 rfl
  rw [run_of_next 32 e _ _ s96]
  have d97 : decodeAt e.code 97 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 99) := by
    simpa [envInc] using decode_at gSel iSel bdec5
  have s97 : step e { st0 n with mem := mem1 n, stack := [], pc := 97 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 99 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [], pc := 97 }
      localBase d97 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 31 e _ _ s97]
  have d99 : decodeAt e.code 99 = some ({ op := .MLOAD }, 100) := by
    simpa [envInc] using decode_at gSel iSel bdec7
  have s99 : step e { st0 n with mem := mem1 n, stack := [localBase], pc := 99 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 100 } := by
    have hs := step_mload e { st0 n with mem := mem1 n, stack := [localBase], pc := 99 }
      localBase [] d99 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 30 e _ _ s99]
  have d100 : decodeAt e.code 100 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 102) := by
    simpa [envInc] using decode_at gSel iSel bdec8
  have s100 : step e { st0 n with mem := mem1 n, stack := [wrap n], pc := 100 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 102 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [wrap n], pc := 100 }
      1 d100 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 29 e _ _ s100]
  have d102 : decodeAt e.code 102 = some ({ op := .DUP ⟨1, by decide⟩ }, 103) := by
    simpa [envInc] using decode_at gSel iSel bdec10
  have s102 : step e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 102 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 103 } := by
    have hs := step_dup2 e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 102 }
      1 (wrap n) [] d102 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 28 e _ _ s102]
  have d103 : decodeAt e.code 103 = some ({ op := .ADD }, 104) := by
    simpa [envInc] using decode_at gSel iSel bdec11
  have s103 : step e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 103 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 104 } := by
    have hs := step_add e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 103 }
      (wrap n) 1 [wrap n] d103 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 27 e _ _ s103]
  have d104 : decodeAt e.code 104 = some ({ op := .DUP ⟨0, by decide⟩ }, 105) := by
    simpa [envInc] using decode_at gSel iSel bdec12
  have s104 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 104 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 105 } := by
    have hs := step_dup1 e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 104 }
      (addW (wrap n) 1) [wrap n] d104 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s104]
  have d105 : decodeAt e.code 105 = some ({ op := .SWAP ⟨1, by decide⟩ }, 106) := by
    simpa [envInc] using decode_at gSel iSel bdec13
  have s105 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 105 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 106 } := by
    have hs := step_swap2 e
      { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 105 }
      (addW (wrap n) 1) (addW (wrap n) 1) (wrap n) [] d105 rfl
    simpa using hs
  rw [run_of_next 25 e _ _ s105]
  have d106 : decodeAt e.code 106 = some ({ op := .GT }, 107) := by
    simpa [envInc] using decode_at gSel iSel bdec14
  have s106 : step e { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 106 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 107 } := by
    have hs := step_gt e
      { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 106 }
      (wrap n) (addW (wrap n) 1) [addW (wrap n) 1] d106 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) 1) = 0 := by
      rw [hwrap]; exact gtW_add_no_overflow h
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 24 e _ _ s106]
  have d107 : decodeAt e.code 107 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyRevPc }, 110) := by
    simpa [envInc] using decode_at gSel iSel bdec15
  have s107 : step e { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 107 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 110 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 107 }
      bodyRevPc d107 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 23 e _ _ s107]
  have d110 : decodeAt e.code 110 = some ({ op := .JUMPI }, 111) := by
    simpa [envInc] using decode_at gSel iSel bdec18
  have s110 : step e { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 110 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 111 } := by
    have hs := step_jumpi_zero e
      { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 110 }
      bodyRevPc [addW (wrap n) 1] d110 rfl
    simpa using hs
  rw [run_of_next 22 e _ _ s110]
  have d111 : decodeAt e.code 111 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyOkPc }, 114) := by
    simpa [envInc] using decode_at gSel iSel bdec19
  have s111 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 111 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 114 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 111 }
      bodyOkPc d111 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 21 e _ _ s111]
  have d114 : decodeAt e.code 114 = some ({ op := .JUMP }, 115) := by
    simpa [envInc] using decode_at gSel iSel bdec22
  have s114 : step e { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 114 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } := by
    have hs := step_jump e { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 114 }
      bodyOkPc [addW (wrap n) 1] d114 rfl (isJumpDest_ok gSel iSel)
    simpa [envInc] using hs
  rw [run_of_next 20 e _ _ s114]
  have d160 : decodeAt e.code bodyOkPc = some ({ op := .JUMPDEST }, 161) := by
    simpa [envInc, bodyOkPc] using decode_at gSel iSel bdec68
  have s160 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 161 } :=
    step_jumpdest e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } d160
  rw [run_of_next 19 e _ _ s160]
  have d161 : decodeAt e.code 161 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 163) := by
    simpa [envInc] using decode_at gSel iSel bdec69
  have s161 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 161 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 163 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 161 }
      (localBase + 32) d161 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 18 e _ _ s161]
  have d163 : decodeAt e.code 163 = some ({ op := .MSTORE }, 164) := by
    simpa [envInc] using decode_at gSel iSel bdec71
  have s163 : step e { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 163 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 164 } :=
    step_mstore e { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 163 }
      (localBase + 32) (addW (wrap n) 1) [] d163 rfl
  rw [run_of_next 17 e _ _ s163]
  have d164 : decodeAt e.code 164 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 166) := by
    simpa [envInc] using decode_at gSel iSel bdec72
  have s164 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 164 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 166 } := by
    have hs := step_push e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 164 }
      (localBase + 32) d164 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 16 e _ _ s164]
  have d166 : decodeAt e.code 166 = some ({ op := .MLOAD }, 167) := by
    simpa [envInc] using decode_at gSel iSel bdec74
  have s166 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 166 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 167 } := by
    have hs := step_mload e
      { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 166 }
      (localBase + 32) [] d166 rfl (list_length_lt_1024 (k := 0) rfl)
    simp only [IncBody.memLoad_memStore] at hs
    rw [hval] at hs
    exact hs
  rw [run_of_next 15 e _ _ s166]
  have d167 : decodeAt e.code 167 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 168) := by
    simpa [envInc] using decode_at gSel iSel bdec75
  have s167 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 167 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 168 } := by
    have hs := step_push e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 167 }
      0 d167 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 14 e _ _ s167]
  have d168 : decodeAt e.code 168 = some ({ op := .SSTORE }, 169) := by
    simpa [envInc] using decode_at gSel iSel bdec76
  have s168 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 168 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 169 } :=
    step_sstore e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 168 }
      0 (n + 1) [] d168 rfl
  rw [run_of_next 13 e _ _ s168]
  have d169 : decodeAt e.code 169 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 171) := by
    simpa [envInc] using decode_at gSel iSel bdec77
  have s169 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 169 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 171 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 169 }
      1 d169 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 12 e _ _ s169]
  have d171 : decodeAt e.code 171 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 172) := by
    simpa [envInc] using decode_at gSel iSel bdec79
  have s171 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 171 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 172 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 171 }
      0 d171 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 11 e _ _ s171]
  have d172 : decodeAt e.code 172 = some ({ op := .MSTORE }, 173) := by
    simpa [envInc] using decode_at gSel iSel bdec80
  have s172 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 172 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 173 } :=
    step_mstore e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 172 }
      0 1 [] d172 rfl
  rw [run_of_next 10 e _ _ s172]
  have d173 : decodeAt e.code 173 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 206) := by
    simpa [envInc] using decode_at gSel iSel bdec81
  have s173 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 173 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 206 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 173 }
      (wrap incTopic) d173 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 9 e _ _ s173]
  have d206 : decodeAt e.code 206 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 208) := by
    simpa [envInc] using decode_at gSel iSel bdec114
  have s206 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 206 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 208 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 206 }
      32 d206 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 8 e _ _ s206]
  have d208 : decodeAt e.code 208 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 209) := by
    simpa [envInc] using decode_at gSel iSel bdec116
  have s208 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 208 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 209 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 208 }
      0 d208 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 7 e _ _ s208]
  have d209 : decodeAt e.code 209 = some ({ op := .LOG ⟨1, by decide⟩ }, 210) := by
    simpa [envInc] using decode_at gSel iSel bdec117
  have s209 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 209 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 210 } := by
    have hs := step_log1 e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 209 }
      0 32 (wrap incTopic) [] d209 rfl
    simpa [log1] using hs
  rw [run_of_next 6 e _ _ s209]
  have d210 : decodeAt e.code 210 = some ({ op := .STOP }, 211) := by
    simpa [envInc] using decode_at gSel iSel bdec118
  have s210 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 210 } =
      StepResult.halt Halt.stop { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 210 } :=
    step_stop e _ d210
  rw [run_of_halt 5 e _ _ _ s210]
  simp [stor1]

end Lsc3.Compile.GetInc
