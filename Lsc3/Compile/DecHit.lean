import Lsc3.Compile.DecBody
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# `bytecode_ok` for the `decrement` body

Saturating: `n = 0` stores `0`; `0 < n < 2^256` stores `n - 1`. Isolated body (no dispatcher).
Apply `dec_hit` / `dec_zero`; do not instantiate them at a Keccak selector.
-/

namespace Lsc3.Compile.DecBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Codegen Lsc3.Compile.Jump

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_spine :
    code = loadBytes ++ (condBytes ++ ([Opcode.toByte .ISZERO] ++ (emitPush2 elsePc ++
      ([Opcode.toByte .JUMPI] ++ (thenBytes ++ (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
        ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST]))))))))) :=
  rfl

theorem code_drop5 :
    code.drop 5 = condBytes ++ ([Opcode.toByte .ISZERO] ++ (emitPush2 elsePc ++
      ([Opcode.toByte .JUMPI] ++ (thenBytes ++ (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
        ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST])))))))) := by
  rw [code_spine, List.drop_left' loadBytes_length]

theorem code_drop10 :
    code.drop 10 = Opcode.toByte .ISZERO :: (emitPush2 elsePc ++
      ([Opcode.toByte .JUMPI] ++ (thenBytes ++ (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
        ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST]))))))) := by
  rw [show 10 = 5 + 5 from rfl, drop_add, code_drop5, List.drop_left' condBytes_length]; rfl

theorem code_drop11 :
    code.drop 11 = emitPush2 elsePc ++ ([Opcode.toByte .JUMPI] ++ (thenBytes ++
      (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++
        (elseBytes ++ [Opcode.toByte .JUMPDEST])))))) := by
  rw [show 11 = 10 + 1 from rfl, drop_add, code_drop10]; rfl

theorem code_drop14 :
    code.drop 14 = Opcode.toByte .JUMPI :: (thenBytes ++ (emitPush2 endPc ++
      ([Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++
        (elseBytes ++ [Opcode.toByte .JUMPDEST]))))) := by
  rw [show 14 = 11 + 3 from rfl, drop_add, code_drop11, List.drop_left' (emitPush2_length elsePc)]; rfl

theorem code_drop15 :
    code.drop 15 = thenBytes ++ (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
      ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST])))) := by
  rw [show 15 = 14 + 1 from rfl, drop_add, code_drop14]; rfl

theorem code_drop25 :
    code.drop 25 = emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
      ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST]))) := by
  rw [show 25 = 15 + 10 from rfl, drop_add, code_drop15, List.drop_left' thenBytes_length]

theorem code_drop28 :
    code.drop 28 = Opcode.toByte .JUMP :: ([Opcode.toByte .JUMPDEST] ++
      (elseBytes ++ [Opcode.toByte .JUMPDEST])) := by
  rw [show 28 = 25 + 3 from rfl, drop_add, code_drop25, List.drop_left' (emitPush2_length endPc)]; rfl

theorem code_drop29 :
    code.drop 29 = Opcode.toByte .JUMPDEST :: (elseBytes ++ [Opcode.toByte .JUMPDEST]) := by
  rw [show 29 = 28 + 1 from rfl, drop_add, code_drop28]; rfl

theorem code_drop30 :
    code.drop 30 = elseBytes ++ [Opcode.toByte .JUMPDEST] := by
  rw [show 30 = 29 + 1 from rfl, drop_add, code_drop29]; rfl

theorem code_drop35 :
    code.drop 35 = checkedSubBytes ++ (elseTailBytes ++ [Opcode.toByte .JUMPDEST]) := by
  rw [show 35 = 30 + 5 from rfl, drop_add, code_drop30]
  simp only [elseBytes, List.append_assoc]
  rw [List.drop_left' (by decide :
    ([0x60, 0x80, Opcode.toByte .MLOAD, 0x60, 1] : List UInt8).length = 5)]

theorem code_drop35_spine :
    code.drop 35 =
      [0x81, 0x81, 0x11] ++ (emitPush2 subRPc ++ (Opcode.toByte .JUMPI ::
        (emitPush2 subOPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
          (IncBody.panicBytes ++ ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
            (elseTailBytes ++ [Opcode.toByte .JUMPDEST])))))))) := by
  rw [code_drop35]
  simp only [checkedSubBytes, List.append_assoc]
  rfl

theorem code_drop38 :
    code.drop 38 =
      emitPush2 subRPc ++ (Opcode.toByte .JUMPI :: (emitPush2 subOPc ++
        (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++
          ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
            (elseTailBytes ++ [Opcode.toByte .JUMPDEST]))))))) := by
  rw [show 38 = 35 + 3 from rfl, drop_add, code_drop35_spine]
  rw [List.drop_left' (by decide : ([0x81, 0x81, 0x11] : List UInt8).length = 3)]

theorem code_drop41 :
    code.drop 41 =
      Opcode.toByte .JUMPI :: (emitPush2 subOPc ++ (Opcode.toByte .JUMP ::
        (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++
          ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
            (elseTailBytes ++ [Opcode.toByte .JUMPDEST])))))) := by
  rw [show 41 = 38 + 3 from rfl, drop_add, code_drop38, List.drop_left' (emitPush2_length subRPc)]

theorem code_drop42 :
    code.drop 42 =
      emitPush2 subOPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (IncBody.panicBytes ++ ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
          (elseTailBytes ++ [Opcode.toByte .JUMPDEST]))))) := by
  rw [show 42 = 41 + 1 from rfl, drop_add, code_drop41]; rfl

theorem code_drop45 :
    code.drop 45 =
      Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++
        ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
          (elseTailBytes ++ [Opcode.toByte .JUMPDEST])))) := by
  rw [show 45 = 42 + 3 from rfl, drop_add, code_drop42, List.drop_left' (emitPush2_length subOPc)]

theorem code_drop46 :
    code.drop 46 =
      Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++
        ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
          (elseTailBytes ++ [Opcode.toByte .JUMPDEST]))) := by
  rw [show 46 = 45 + 1 from rfl, drop_add, code_drop45]; rfl

theorem code_drop47 :
    code.drop 47 =
      IncBody.panicBytes ++ ([Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB] ++
        (elseTailBytes ++ [Opcode.toByte .JUMPDEST])) := by
  rw [show 47 = 46 + 1 from rfl, drop_add, code_drop46]; rfl

theorem code_drop91 :
    code.drop 91 =
      Opcode.toByte .JUMPDEST :: 0x90 :: Opcode.toByte .SUB ::
        (elseTailBytes ++ [Opcode.toByte .JUMPDEST]) := by
  rw [show 91 = 47 + 44 from rfl, drop_add, code_drop47,
    List.drop_left' IncBody.panicBytes_length]
  rfl

theorem code_drop92 :
    code.drop 92 =
      0x90 :: Opcode.toByte .SUB :: (elseTailBytes ++ [Opcode.toByte .JUMPDEST]) := by
  rw [show 92 = 91 + 1 from rfl, drop_add, code_drop91]; rfl

theorem code_drop93 :
    code.drop 93 = Opcode.toByte .SUB :: (elseTailBytes ++ [Opcode.toByte .JUMPDEST]) := by
  rw [show 93 = 92 + 1 from rfl, drop_add, code_drop92]; rfl

theorem code_drop94 :
    code.drop 94 = elseTailBytes ++ [Opcode.toByte .JUMPDEST] := by
  rw [show 94 = 93 + 1 from rfl, drop_add, code_drop93]; rfl

theorem code_drop103 :
    code.drop 103 = [Opcode.toByte .JUMPDEST] := by
  rw [show 103 = 94 + 9 from rfl, drop_add, code_drop94, List.drop_left' elseTailBytes_length]

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  have h : code.drop 0 = 0x5f :: code.drop 1 := by simp [code, loadBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc1 :
    decodeAt code 1 = some ({ op := .SLOAD }, 2) := by
  have h : code.drop 1 = Opcode.toByte .SLOAD :: code.drop 2 := by
    simp [code, loadBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 4) := by
  have hdrop : code.drop 2 = 0x60 :: 0x80 :: code.drop 4 := by
    simp [code, loadBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 4))
  simpa [wrap, localBase] using h

theorem decode_pc4 :
    decodeAt code 4 = some ({ op := .MSTORE }, 5) := by
  have h : code.drop 4 = Opcode.toByte .MSTORE :: code.drop 5 := by
    simp [code, loadBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc5 :
    decodeAt code 5 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 7) := by
  have hdrop : code.drop 5 = 0x60 :: 0x80 :: code.drop 7 := by
    rw [code_drop5]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 7))
  simpa [wrap, localBase] using h

theorem decode_pc7 :
    decodeAt code 7 = some ({ op := .MLOAD }, 8) := by
  have h : code.drop 7 = Opcode.toByte .MLOAD :: code.drop 8 := by
    rw [show 7 = 5 + 2 from rfl, drop_add, code_drop5]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc8 :
    decodeAt code 8 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 9) := by
  have h : code.drop 8 = 0x5f :: code.drop 9 := by
    rw [show 8 = 5 + 3 from rfl, drop_add, code_drop5]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc9 :
    decodeAt code 9 = some ({ op := .EQ }, 10) := by
  have h : code.drop 9 = Opcode.toByte .EQ :: code.drop 10 := by
    rw [show 9 = 5 + 4 from rfl, drop_add, code_drop5]; rfl
  exact decodeAt_of_drop h (decodeAt_eq_head _)

theorem decode_pc10 :
    decodeAt code 10 = some ({ op := .ISZERO }, 11) :=
  decodeAt_of_drop code_drop10 (decodeAt_iszero_head _)

theorem decode_pc11 :
    decodeAt code 11 = some ({ op := .PUSH ⟨2, by decide⟩, imm := elsePc }, 14) := by
  have hdrop : code.drop 11 = emitPush2 elsePc ++ code.drop 14 := by
    rw [code_drop11, code_drop14]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push2 elsePc _)
  simpa [elsePc_mod] using h

theorem decode_pc14 :
    decodeAt code 14 = some ({ op := .JUMPI }, 15) :=
  decodeAt_of_drop code_drop14 (decodeAt_jumpi_head _)

theorem decode_pc15 :
    decodeAt code 15 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 16) := by
  have h : code.drop 15 = 0x5f :: code.drop 16 := by
    rw [code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc16 :
    decodeAt code 16 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 18) := by
  have hdrop : code.drop 16 = 0x60 :: 0xA0 :: code.drop 18 := by
    rw [show 16 = 15 + 1 from rfl, drop_add, code_drop15]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 18))
  simpa [wrap, localBase] using h

theorem decode_pc18 :
    decodeAt code 18 = some ({ op := .MSTORE }, 19) := by
  have h : code.drop 18 = Opcode.toByte .MSTORE :: code.drop 19 := by
    rw [show 18 = 15 + 3 from rfl, drop_add, code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc19 :
    decodeAt code 19 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 21) := by
  have hdrop : code.drop 19 = 0x60 :: 0xA0 :: code.drop 21 := by
    rw [show 19 = 15 + 4 from rfl, drop_add, code_drop15]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 21))
  simpa [wrap, localBase] using h

theorem decode_pc21 :
    decodeAt code 21 = some ({ op := .MLOAD }, 22) := by
  have h : code.drop 21 = Opcode.toByte .MLOAD :: code.drop 22 := by
    rw [show 21 = 15 + 6 from rfl, drop_add, code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc22 :
    decodeAt code 22 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 23) := by
  have h : code.drop 22 = 0x5f :: code.drop 23 := by
    rw [show 22 = 15 + 7 from rfl, drop_add, code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc23 :
    decodeAt code 23 = some ({ op := .SSTORE }, 24) := by
  have h : code.drop 23 = Opcode.toByte .SSTORE :: code.drop 24 := by
    rw [show 23 = 15 + 8 from rfl, drop_add, code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_sstore_head _)

theorem decode_pc24 :
    decodeAt code 24 = some ({ op := .STOP }, 25) := by
  have h : code.drop 24 = Opcode.toByte .STOP :: code.drop 25 := by
    rw [show 24 = 15 + 9 from rfl, drop_add, code_drop15]; rfl
  exact decodeAt_of_drop h (decodeAt_stop_head _)

theorem decode_pc29 :
    decodeAt code 29 = some ({ op := .JUMPDEST }, 30) :=
  decodeAt_of_drop code_drop29 (decodeAt_jumpdest_head _)

theorem isJumpDest_else : isJumpDest code elsePc = true := by
  simpa [elsePc] using isJumpDest_of_decode decode_pc29

theorem decode_pc30 :
    decodeAt code 30 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 32) := by
  have hdrop : code.drop 30 = 0x60 :: 0x80 :: code.drop 32 := by
    rw [code_drop30]; simp only [elseBytes]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 32))
  simpa [wrap, localBase] using h

theorem decode_pc32 :
    decodeAt code 32 = some ({ op := .MLOAD }, 33) := by
  have h : code.drop 32 = Opcode.toByte .MLOAD :: code.drop 33 := by
    rw [show 32 = 30 + 2 from rfl, drop_add, code_drop30]
    simp only [elseBytes]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc33 :
    decodeAt code 33 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 35) := by
  have hdrop : code.drop 33 = 0x60 :: 1 :: code.drop 35 := by
    rw [show 33 = 30 + 3 from rfl, drop_add, code_drop30]
    simp only [elseBytes]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (code.drop 35))
  simpa [wrap] using h

theorem decode_pc35 :
    decodeAt code 35 = some ({ op := .DUP ⟨1, by decide⟩ }, 36) := by
  have h : code.drop 35 = 0x81 :: code.drop 36 := by
    rw [code_drop35_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem decode_pc36 :
    decodeAt code 36 = some ({ op := .DUP ⟨1, by decide⟩ }, 37) := by
  have h : code.drop 36 = 0x81 :: code.drop 37 := by
    rw [show 36 = 35 + 1 from rfl, drop_add, code_drop35_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem decode_pc37 :
    decodeAt code 37 = some ({ op := .GT }, 38) := by
  have h : code.drop 37 = 0x11 :: code.drop 38 := by
    rw [show 37 = 35 + 2 from rfl, drop_add, code_drop35_spine]; rfl
  exact decodeAt_of_drop h (decodeAt_gt_head _)

theorem decode_pc38 :
    decodeAt code 38 = some ({ op := .PUSH ⟨2, by decide⟩, imm := subRPc }, 41) := by
  have hdrop : code.drop 38 = emitPush2 subRPc ++ code.drop 41 := by
    rw [code_drop38, code_drop41]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 subRPc _)
  simpa [subRPc_mod] using h

theorem decode_pc41 :
    decodeAt code 41 = some ({ op := .JUMPI }, 42) :=
  decodeAt_of_drop code_drop41 (decodeAt_jumpi_head _)

theorem decode_pc42 :
    decodeAt code 42 = some ({ op := .PUSH ⟨2, by decide⟩, imm := subOPc }, 45) := by
  have hdrop : code.drop 42 = emitPush2 subOPc ++ code.drop 45 := by
    rw [code_drop42, code_drop45]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 subOPc _)
  simpa [subOPc_mod] using h

theorem decode_pc45 :
    decodeAt code 45 = some ({ op := .JUMP }, 46) :=
  decodeAt_of_drop code_drop45 (decodeAt_jump_head _)

theorem decode_pc91 :
    decodeAt code 91 = some ({ op := .JUMPDEST }, 92) :=
  decodeAt_of_drop code_drop91 (decodeAt_jumpdest_head _)

theorem isJumpDest_subO : isJumpDest code subOPc = true := by
  simpa [subOPc] using isJumpDest_of_decode decode_pc91

theorem decode_pc92 :
    decodeAt code 92 = some ({ op := .SWAP ⟨0, by decide⟩ }, 93) :=
  decodeAt_of_drop code_drop92 (decodeAt_swap1_head _)

theorem decode_pc93 :
    decodeAt code 93 = some ({ op := .SUB }, 94) :=
  decodeAt_of_drop code_drop93 (decodeAt_sub_head _)

theorem decode_pc94 :
    decodeAt code 94 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 96) := by
  have hdrop : code.drop 94 = 0x60 :: 0xA0 :: code.drop 96 := by
    rw [code_drop94]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 96))
  simpa [wrap, localBase] using h

theorem decode_pc96 :
    decodeAt code 96 = some ({ op := .MSTORE }, 97) := by
  have h : code.drop 96 = Opcode.toByte .MSTORE :: code.drop 97 := by
    rw [show 96 = 94 + 2 from rfl, drop_add, code_drop94]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc97 :
    decodeAt code 97 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 99) := by
  have hdrop : code.drop 97 = 0x60 :: 0xA0 :: code.drop 99 := by
    rw [show 97 = 94 + 3 from rfl, drop_add, code_drop94]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 99))
  simpa [wrap, localBase] using h

theorem decode_pc99 :
    decodeAt code 99 = some ({ op := .MLOAD }, 100) := by
  have h : code.drop 99 = Opcode.toByte .MLOAD :: code.drop 100 := by
    rw [show 99 = 94 + 5 from rfl, drop_add, code_drop94]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc100 :
    decodeAt code 100 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 101) := by
  have h : code.drop 100 = 0x5f :: code.drop 101 := by
    rw [show 100 = 94 + 6 from rfl, drop_add, code_drop94]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc101 :
    decodeAt code 101 = some ({ op := .SSTORE }, 102) := by
  have h : code.drop 101 = Opcode.toByte .SSTORE :: code.drop 102 := by
    rw [show 101 = 94 + 7 from rfl, drop_add, code_drop94]; rfl
  exact decodeAt_of_drop h (decodeAt_sstore_head _)

theorem decode_pc102 :
    decodeAt code 102 = some ({ op := .STOP }, 103) := by
  have h : code.drop 102 = Opcode.toByte .STOP :: code.drop 103 := by
    rw [show 102 = 94 + 8 from rfl, drop_add, code_drop94]; rfl
  exact decodeAt_of_drop h (decodeAt_stop_head _)

def env : Env :=
  { code := code, calldata := [], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

abbrev mem1 (n : Nat) : Mem := memStore (st0 n).mem localBase n

abbrev mem2 (n : Nat) (v : Nat) : Mem := memStore (mem1 n) (localBase + 32) v

abbrev stor1 (n v : Nat) : EVM.Storage := fun k => if k = 0 then v else (st0 n).storage k

/-- `0 < n < 2^256`: STOP with storage slot 0 equal to `n - 1`. -/
theorem dec_hit (n : Nat) (hpos : 0 < n) (hn : n < wordBound) :
    (match run 32 env (st0 n) with
    | some (Halt.stop, s) => s.storage 0 = n - 1
    | _ => False) := by
  have hwrap : wrap n = n := Nat.mod_eq_of_lt hn
  have hsub : subW (wrap n) 1 = n - 1 := by rw [hwrap]; exact subW_pred hpos hn
  have hval : wrap (subW (wrap n) 1) = n - 1 := by
    rw [hsub]; exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.sub_lt hpos (by decide)) hn)
  have s0 : step env (st0 n) =
      StepResult.next { st0 n with stack := [0], pc := 1 } := by
    have hs := step_push env (st0 n) 0 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 31 env (st0 n) _ s0]
  have s1 : step env { st0 n with stack := [0], pc := 1 } =
      StepResult.next { st0 n with stack := [n], pc := 2 } := by
    have hs := step_sload env { st0 n with stack := [0], pc := 1 } 0 []
      decode_pc1 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 30 env _ _ s1]
  have s2 : step env { st0 n with stack := [n], pc := 2 } =
      StepResult.next { st0 n with stack := [localBase, n], pc := 4 } := by
    have hs := step_push env { st0 n with stack := [n], pc := 2 } localBase decode_pc2
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 29 env _ _ s2]
  have s4 : step env { st0 n with stack := [localBase, n], pc := 4 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 5 } :=
    step_mstore env { st0 n with stack := [localBase, n], pc := 4 } localBase n []
      decode_pc4 rfl
  rw [run_of_next 28 env _ _ s4]
  have s5 : step env { st0 n with mem := mem1 n, stack := [], pc := 5 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 7 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [], pc := 5 }
      localBase decode_pc5 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 27 env _ _ s5]
  have s7 : step env { st0 n with mem := mem1 n, stack := [localBase], pc := 7 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 } := by
    have hs := step_mload env { st0 n with mem := mem1 n, stack := [localBase], pc := 7 }
      localBase [] decode_pc7 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 26 env _ _ s7]
  have s8 : step env { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, wrap n], pc := 9 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 }
      0 decode_pc8 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 25 env _ _ s8]
  have s9 : step env { st0 n with mem := mem1 n, stack := [0, wrap n], pc := 9 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0], pc := 10 } := by
    have hs := step_eq env { st0 n with mem := mem1 n, stack := [0, wrap n], pc := 9 }
      0 (wrap n) [] decode_pc9 rfl (list_length_lt_1024 (k := 0) rfl)
    have hne : wrap n ≠ 0 := by rw [hwrap]; exact Nat.ne_of_gt hpos
    simp only [eqW_ne (Ne.symm hne)] at hs
    exact hs
  rw [run_of_next 24 env _ _ s9]
  have s10 : step env { st0 n with mem := mem1 n, stack := [0], pc := 10 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1], pc := 11 } := by
    have hs := step_iszero env { st0 n with mem := mem1 n, stack := [0], pc := 10 }
      0 [] decode_pc10 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 23 env _ _ s10]
  have s11 : step env { st0 n with mem := mem1 n, stack := [1], pc := 11 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [elsePc, 1], pc := 14 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [1], pc := 11 }
      elsePc decode_pc11 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 22 env _ _ s11]
  have s14 : step env { st0 n with mem := mem1 n, stack := [elsePc, 1], pc := 14 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := elsePc } := by
    have hs := step_jumpi_nz env { st0 n with mem := mem1 n, stack := [elsePc, 1], pc := 14 }
      elsePc 1 [] decode_pc14 rfl (by decide) isJumpDest_else
    simpa [env] using hs
  rw [run_of_next 21 env _ _ s14]
  have s29 : step env { st0 n with mem := mem1 n, stack := [], pc := elsePc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 30 } :=
    step_jumpdest env { st0 n with mem := mem1 n, stack := [], pc := elsePc }
      (by simpa [env, elsePc] using decode_pc29)
  rw [run_of_next 20 env _ _ s29]
  have s30 : step env { st0 n with mem := mem1 n, stack := [], pc := 30 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 32 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [], pc := 30 }
      localBase decode_pc30 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 19 env _ _ s30]
  have s32 : step env { st0 n with mem := mem1 n, stack := [localBase], pc := 32 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 33 } := by
    have hs := step_mload env { st0 n with mem := mem1 n, stack := [localBase], pc := 32 }
      localBase [] decode_pc32 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 18 env _ _ s32]
  have s33 : step env { st0 n with mem := mem1 n, stack := [wrap n], pc := 33 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 35 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [wrap n], pc := 33 }
      1 decode_pc33 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 17 env _ _ s33]
  have s35 : step env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 35 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 36 } := by
    have hs := step_dup2 env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 35 }
      1 (wrap n) [] decode_pc35 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 16 env _ _ s35]
  have s36 : step env { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 36 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n, 1, wrap n], pc := 37 } := by
    have hs := step_dup2 env { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 36 }
      (wrap n) 1 [wrap n] decode_pc36 rfl (list_length_lt_1024 (k := 3) rfl)
    simpa using hs
  rw [run_of_next 15 env _ _ s36]
  have s37 : step env { st0 n with mem := mem1 n, stack := [1, wrap n, 1, wrap n], pc := 37 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, 1, wrap n], pc := 38 } := by
    have hs := step_gt env { st0 n with mem := mem1 n, stack := [1, wrap n, 1, wrap n], pc := 37 }
      1 (wrap n) [1, wrap n] decode_pc37 rfl (list_length_lt_1024 (k := 2) rfl)
    have hgt : gtW 1 (wrap n) = 0 := by rw [hwrap]; exact gtW_one_of_pos hpos
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 14 env _ _ s37]
  have s38 : step env { st0 n with mem := mem1 n, stack := [0, 1, wrap n], pc := 38 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [subRPc, 0, 1, wrap n], pc := 41 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [0, 1, wrap n], pc := 38 }
      subRPc decode_pc38 (list_length_lt_1024 (k := 3) rfl)
    simpa using hs
  rw [run_of_next 13 env _ _ s38]
  have s41 : step env { st0 n with mem := mem1 n, stack := [subRPc, 0, 1, wrap n], pc := 41 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 42 } := by
    have hs := step_jumpi_zero env
      { st0 n with mem := mem1 n, stack := [subRPc, 0, 1, wrap n], pc := 41 }
      subRPc [1, wrap n] decode_pc41 rfl
    simpa using hs
  rw [run_of_next 12 env _ _ s41]
  have s42 : step env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 42 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [subOPc, 1, wrap n], pc := 45 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 42 }
      subOPc decode_pc42 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 11 env _ _ s42]
  have s45 : step env { st0 n with mem := mem1 n, stack := [subOPc, 1, wrap n], pc := 45 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := subOPc } := by
    have hs := step_jump env { st0 n with mem := mem1 n, stack := [subOPc, 1, wrap n], pc := 45 }
      subOPc [1, wrap n] decode_pc45 rfl isJumpDest_subO
    simpa [env] using hs
  rw [run_of_next 10 env _ _ s45]
  have s91 : step env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := subOPc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 92 } :=
    step_jumpdest env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := subOPc }
      (by simpa [env, subOPc] using decode_pc91)
  rw [run_of_next 9 env _ _ s91]
  have s92 : step env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 92 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1], pc := 93 } := by
    have hs := step_swap1 env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 92 }
      1 (wrap n) [] decode_pc92 rfl
    simpa using hs
  rw [run_of_next 8 env _ _ s92]
  have s93 : step env { st0 n with mem := mem1 n, stack := [wrap n, 1], pc := 93 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [subW (wrap n) 1], pc := 94 } := by
    have hs := step_sub env { st0 n with mem := mem1 n, stack := [wrap n, 1], pc := 93 }
      (wrap n) 1 [] decode_pc93 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 7 env _ _ s93]
  have s94 : step env { st0 n with mem := mem1 n, stack := [subW (wrap n) 1], pc := 94 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase + 32, subW (wrap n) 1], pc := 96 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [subW (wrap n) 1], pc := 94 }
      (localBase + 32) decode_pc94 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 6 env _ _ s94]
  have s96 : step env { st0 n with mem := mem1 n, stack := [localBase + 32, subW (wrap n) 1], pc := 96 } =
      StepResult.next { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [], pc := 97 } :=
    step_mstore env { st0 n with mem := mem1 n, stack := [localBase + 32, subW (wrap n) 1], pc := 96 }
      (localBase + 32) (subW (wrap n) 1) [] decode_pc96 rfl
  rw [run_of_next 5 env _ _ s96]
  have s97 : step env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [], pc := 97 } =
      StepResult.next { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [localBase + 32], pc := 99 } := by
    have hs := step_push env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [], pc := 97 }
      (localBase + 32) decode_pc97 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 4 env _ _ s97]
  have s99 : step env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [localBase + 32], pc := 99 } =
      StepResult.next { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [n - 1], pc := 100 } := by
    have hs := step_mload env
      { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [localBase + 32], pc := 99 }
      (localBase + 32) [] decode_pc99 rfl (list_length_lt_1024 (k := 0) rfl)
    have hload : memLoad (mem2 n (subW (wrap n) 1)) (localBase + 32) = n - 1 := by
      unfold mem2
      rw [IncBody.memLoad_memStore, hval]
    rw [hload] at hs
    exact hs
  rw [run_of_next 3 env _ _ s99]
  have s100 : step env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [n - 1], pc := 100 } =
      StepResult.next { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [0, n - 1], pc := 101 } := by
    have hs := step_push env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [n - 1], pc := 100 }
      0 decode_pc100 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 2 env _ _ s100]
  have s101 : step env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [0, n - 1], pc := 101 } =
      StepResult.next { st0 n with mem := mem2 n (subW (wrap n) 1), storage := stor1 n (n - 1), stack := [], pc := 102 } :=
    step_sstore env { st0 n with mem := mem2 n (subW (wrap n) 1), stack := [0, n - 1], pc := 101 }
      0 (n - 1) [] decode_pc101 rfl
  rw [run_of_next 1 env _ _ s101]
  have s102 : step env { st0 n with mem := mem2 n (subW (wrap n) 1), storage := stor1 n (n - 1), stack := [], pc := 102 } =
      StepResult.halt .stop { st0 n with mem := mem2 n (subW (wrap n) 1), storage := stor1 n (n - 1), stack := [], pc := 102 } :=
    step_stop env { st0 n with mem := mem2 n (subW (wrap n) 1), storage := stor1 n (n - 1), stack := [], pc := 102 }
      decode_pc102
  rw [run_of_halt 0 env _ _ _ s102]
  simp [stor1]

/-- `n = 0`: STOP with storage slot 0 still `0`. -/
theorem dec_zero :
    (match run 19 env (st0 0) with
    | some (Halt.stop, s) => s.storage 0 = 0
    | _ => False) := by
  have s0 : step env (st0 0) =
      StepResult.next { st0 0 with stack := [0], pc := 1 } := by
    have hs := step_push env (st0 0) 0 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 18 env (st0 0) _ s0]
  have s1 : step env { st0 0 with stack := [0], pc := 1 } =
      StepResult.next { st0 0 with stack := [0], pc := 2 } := by
    have hs := step_sload env { st0 0 with stack := [0], pc := 1 } 0 []
      decode_pc1 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 17 env _ _ s1]
  have s2 : step env { st0 0 with stack := [0], pc := 2 } =
      StepResult.next { st0 0 with stack := [localBase, 0], pc := 4 } := by
    have hs := step_push env { st0 0 with stack := [0], pc := 2 } localBase decode_pc2
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 16 env _ _ s2]
  have s4 : step env { st0 0 with stack := [localBase, 0], pc := 4 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [], pc := 5 } :=
    step_mstore env { st0 0 with stack := [localBase, 0], pc := 4 } localBase 0 []
      decode_pc4 rfl
  rw [run_of_next 15 env _ _ s4]
  have s5 : step env { st0 0 with mem := mem1 0, stack := [], pc := 5 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [localBase], pc := 7 } := by
    have hs := step_push env { st0 0 with mem := mem1 0, stack := [], pc := 5 }
      localBase decode_pc5 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 14 env _ _ s5]
  have s7 : step env { st0 0 with mem := mem1 0, stack := [localBase], pc := 7 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [0], pc := 8 } := by
    have hs := step_mload env { st0 0 with mem := mem1 0, stack := [localBase], pc := 7 }
      localBase [] decode_pc7 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore, wrap] using hs
  rw [run_of_next 13 env _ _ s7]
  have s8 : step env { st0 0 with mem := mem1 0, stack := [0], pc := 8 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [0, 0], pc := 9 } := by
    have hs := step_push env { st0 0 with mem := mem1 0, stack := [0], pc := 8 }
      0 decode_pc8 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 12 env _ _ s8]
  have s9 : step env { st0 0 with mem := mem1 0, stack := [0, 0], pc := 9 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [1], pc := 10 } := by
    have hs := step_eq env { st0 0 with mem := mem1 0, stack := [0, 0], pc := 9 }
      0 0 [] decode_pc9 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [eqW] using hs
  rw [run_of_next 11 env _ _ s9]
  have s10 : step env { st0 0 with mem := mem1 0, stack := [1], pc := 10 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [0], pc := 11 } := by
    have hs := step_iszero env { st0 0 with mem := mem1 0, stack := [1], pc := 10 }
      1 [] decode_pc10 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [iszeroW] using hs
  rw [run_of_next 10 env _ _ s10]
  have s11 : step env { st0 0 with mem := mem1 0, stack := [0], pc := 11 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [elsePc, 0], pc := 14 } := by
    have hs := step_push env { st0 0 with mem := mem1 0, stack := [0], pc := 11 }
      elsePc decode_pc11 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 9 env _ _ s11]
  have s14 : step env { st0 0 with mem := mem1 0, stack := [elsePc, 0], pc := 14 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [], pc := 15 } := by
    have hs := step_jumpi_zero env { st0 0 with mem := mem1 0, stack := [elsePc, 0], pc := 14 }
      elsePc [] decode_pc14 rfl
    simpa using hs
  rw [run_of_next 8 env _ _ s14]
  have s15 : step env { st0 0 with mem := mem1 0, stack := [], pc := 15 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [0], pc := 16 } := by
    have hs := step_push env { st0 0 with mem := mem1 0, stack := [], pc := 15 }
      0 decode_pc15 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 7 env _ _ s15]
  have s16 : step env { st0 0 with mem := mem1 0, stack := [0], pc := 16 } =
      StepResult.next { st0 0 with mem := mem1 0, stack := [localBase + 32, 0], pc := 18 } := by
    have hs := step_push env { st0 0 with mem := mem1 0, stack := [0], pc := 16 }
      (localBase + 32) decode_pc16 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 6 env _ _ s16]
  have s18 : step env { st0 0 with mem := mem1 0, stack := [localBase + 32, 0], pc := 18 } =
      StepResult.next { st0 0 with mem := mem2 0 0, stack := [], pc := 19 } :=
    step_mstore env { st0 0 with mem := mem1 0, stack := [localBase + 32, 0], pc := 18 }
      (localBase + 32) 0 [] decode_pc18 rfl
  rw [run_of_next 5 env _ _ s18]
  have s19 : step env { st0 0 with mem := mem2 0 0, stack := [], pc := 19 } =
      StepResult.next { st0 0 with mem := mem2 0 0, stack := [localBase + 32], pc := 21 } := by
    have hs := step_push env { st0 0 with mem := mem2 0 0, stack := [], pc := 19 }
      (localBase + 32) decode_pc19 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 4 env _ _ s19]
  have s21 : step env { st0 0 with mem := mem2 0 0, stack := [localBase + 32], pc := 21 } =
      StepResult.next { st0 0 with mem := mem2 0 0, stack := [0], pc := 22 } := by
    have hs := step_mload env { st0 0 with mem := mem2 0 0, stack := [localBase + 32], pc := 21 }
      (localBase + 32) [] decode_pc21 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore, wrap] using hs
  rw [run_of_next 3 env _ _ s21]
  have s22 : step env { st0 0 with mem := mem2 0 0, stack := [0], pc := 22 } =
      StepResult.next { st0 0 with mem := mem2 0 0, stack := [0, 0], pc := 23 } := by
    have hs := step_push env { st0 0 with mem := mem2 0 0, stack := [0], pc := 22 }
      0 decode_pc22 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 2 env _ _ s22]
  have s23 : step env { st0 0 with mem := mem2 0 0, stack := [0, 0], pc := 23 } =
      StepResult.next { st0 0 with mem := mem2 0 0, storage := stor1 0 0, stack := [], pc := 24 } :=
    step_sstore env { st0 0 with mem := mem2 0 0, stack := [0, 0], pc := 23 }
      0 0 [] decode_pc23 rfl
  rw [run_of_next 1 env _ _ s23]
  have s24 : step env { st0 0 with mem := mem2 0 0, storage := stor1 0 0, stack := [], pc := 24 } =
      StepResult.halt .stop { st0 0 with mem := mem2 0 0, storage := stor1 0 0, stack := [], pc := 24 } :=
    step_stop env { st0 0 with mem := mem2 0 0, storage := stor1 0 0, stack := [], pc := 24 }
      decode_pc24
  rw [run_of_halt 0 env _ _ _ s24]
  simp [stor1]

end Lsc3.Compile.DecBody
