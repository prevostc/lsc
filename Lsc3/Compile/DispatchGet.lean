import Lsc3.EVM.Lemmas
import Lsc3.Compile.Exec
import Lsc3.Compile.Encode
import Lsc3.Compile.GetBody

/-!
# One-function dispatcher + `get` body

Hand-assembled (PUSH1 jump, not the compiler's PUSH32) so PCs stay small.
Matching calldata jumps to the `get` body; a different selector `STOP`s.
-/

namespace Lsc3.Compile.DispatchGet

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.GetBody

private theorem foldl_range_eq {α} (n : Nat) (f g : α → Nat → α)
    (h : ∀ acc i, i < n → f acc i = g acc i) (acc : α) :
    (List.range n).foldl f acc = (List.range n).foldl g acc := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (fun acc i hi => h acc i (Nat.lt_succ_of_lt hi))]
    rw [h _ n (Nat.lt_succ_self n)]

private theorem toNat_ofNat_mod256 (t : Nat) :
    (UInt8.ofNat (t % 256)).toNat = t % 256 := by
  change (t % 256) % 256 = t % 256
  rw [Nat.mod_mod]

private theorem pow256_4 : 256 ^ 4 = 2 ^ 32 := by
  change (2 ^ 8) ^ 4 = 2 ^ 32
  rw [← Nat.pow_mul]

def push4Bytes (sel : Nat) : List UInt8 :=
  Opcode.toByte (.PUSH ⟨4, by decide⟩) :: natToBytesBE sel 4

@[simp] theorem push4Bytes_length (sel : Nat) : (push4Bytes sel).length = 5 := by
  simp [push4Bytes, natToBytesBE_length]

theorem readImm_push4 (sel : Nat) (rest : List UInt8) :
    readImm (push4Bytes sel ++ rest) 0 4 = sel % 2 ^ 32 := by
  have hlen : ∀ i, i < 4 → 1 + i < (push4Bytes sel ++ rest).length := by
    intro i hi
    simp [push4Bytes, natToBytesBE_length]; omega
  have hfold :
      (List.range 4).foldl (fun acc i =>
        if 1 + i < (push4Bytes sel ++ rest).length then
          acc * 256 + ((push4Bytes sel ++ rest)[1 + i]!).toNat
        else acc) 0 =
        (List.range 4).foldl (fun acc i => acc * 256 + sel / 256 ^ (3 - i) % 256) 0 := by
    refine foldl_range_eq 4 _ _ ?_ 0
    intro acc i hi
    have hi' := hlen i hi
    simp only [hi', ↓reduceIte]
    rw [Nat.add_comm 1 i]
    have hi2 : i + 1 < (push4Bytes sel ++ rest).length := by
      simpa [Nat.add_comm] using hi'
    rw [getElem!_pos (push4Bytes sel ++ rest) (i + 1) hi2]
    simp only [push4Bytes, List.cons_append]
    rw [List.getElem_cons_succ]
    have hlt : i < (natToBytesBE sel 4).length := by simp [natToBytesBE_length]; exact hi
    rw [List.getElem_append_left hlt, natToBytesBE_getElem sel 4 i hi, toNat_ofNat_mod256]
  simp only [readImm, Nat.zero_add]
  rw [hfold, packSel_high sel 4 (by decide), Nat.sub_self, Nat.pow_zero, Nat.div_one, pow256_4]
  exact wrap_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem decodeAt_push4 (sel : Nat) (rest : List UInt8) :
    decodeAt (push4Bytes sel ++ rest) 0 =
      some ({ op := .PUSH ⟨4, by decide⟩, imm := sel % 2 ^ 32 }, 5) := by
  unfold decodeAt
  have hpc : 0 < (push4Bytes sel ++ rest).length := by simp [push4Bytes, natToBytesBE_length]
  rw [dif_pos hpc]
  have hbyte : (push4Bytes sel ++ rest)[0] = Opcode.toByte (.PUSH ⟨4, by decide⟩) := by
    simp [push4Bytes]
  rw [hbyte, ofByte_toByte]
  simp [Opcode.immBytes, readImm_push4]

def loadSelBytes : List UInt8 := [0x5f, 0x35, 0x60, 0xE0, 0x1c]

/-- `JUMPDEST` lives at PC 15. -/
def dest : Nat := 15

def preBytes (sel : Nat) : List UInt8 :=
  loadSelBytes ++ push4Bytes sel ++ [0x14, 0x60, 15, 0x57, 0x00, 0x5b]

def code (sel : Nat) : List UInt8 := preBytes sel ++ GetBody.code

@[simp] theorem preBytes_length (sel : Nat) : (preBytes sel).length = 16 := by
  simp [preBytes, loadSelBytes, push4Bytes_length]

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

private theorem code_assoc (sel : Nat) :
    code sel =
      loadSelBytes ++
        (push4Bytes sel ++ ([0x14, 0x60, 15, 0x57, 0x00, 0x5b] ++ GetBody.code)) := by
  simp [code, preBytes, List.append_assoc]

theorem code_drop5 (sel : Nat) :
    (code sel).drop 5 =
      push4Bytes sel ++ [0x14, 0x60, 15, 0x57, 0x00, 0x5b] ++ GetBody.code := by
  rw [code_assoc, List.drop_left' (by simp [loadSelBytes]), List.append_assoc]

theorem code_drop10 (sel : Nat) :
    (code sel).drop 10 = [0x14, 0x60, 15, 0x57, 0x00, 0x5b] ++ GetBody.code := by
  rw [show 10 = 5 + 5 from rfl, drop_add, code_drop5, List.append_assoc,
    List.drop_left' (push4Bytes_length sel)]

theorem code_drop11 (sel : Nat) :
    (code sel).drop 11 = [0x60, 15, 0x57, 0x00, 0x5b] ++ GetBody.code := by
  rw [show 11 = 10 + 1 from rfl, drop_add, code_drop10]; rfl

theorem code_drop13 (sel : Nat) :
    (code sel).drop 13 = [0x57, 0x00, 0x5b] ++ GetBody.code := by
  rw [show 13 = 10 + 3 from rfl, drop_add, code_drop10]; rfl

theorem code_drop14 (sel : Nat) :
    (code sel).drop 14 = [0x00, 0x5b] ++ GetBody.code := by
  rw [show 14 = 10 + 4 from rfl, drop_add, code_drop10]; rfl

theorem code_drop15 (sel : Nat) :
    (code sel).drop 15 = [0x5b] ++ GetBody.code := by
  rw [show 15 = 10 + 5 from rfl, drop_add, code_drop10]; rfl

def env (sel : Nat) (args : List Nat) : Env :=
  { code := code sel, calldata := packCall sel args, address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

theorem decode_pc0 (sel : Nat) :
    decodeAt (code sel) 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  have h : (code sel).drop 0 = 0x5f :: (code sel).drop 1 := by
    simp [code, preBytes, loadSelBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc1 (sel : Nat) :
    decodeAt (code sel) 1 = some ({ op := .CALLDATALOAD }, 2) := by
  have h : (code sel).drop 1 = Opcode.toByte .CALLDATALOAD :: (code sel).drop 2 := by
    simp [code, preBytes, loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc2 (sel : Nat) :
    decodeAt (code sel) 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 4) := by
  have hdrop : (code sel).drop 2 = 0x60 :: 0xE0 :: (code sel).drop 4 := by
    simp [code, preBytes, loadSelBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) ((code sel).drop 4))
  simpa [wrap] using h

theorem decode_pc4 (sel : Nat) :
    decodeAt (code sel) 4 = some ({ op := .SHR }, 5) := by
  have h : (code sel).drop 4 = Opcode.toByte .SHR :: (code sel).drop 5 := by
    simp [code, preBytes, loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .SHR _ rfl)

theorem decode_pc5 (sel : Nat) :
    decodeAt (code sel) 5 =
      some ({ op := .PUSH ⟨4, by decide⟩, imm := sel % 2 ^ 32 }, 10) := by
  have hdrop : (code sel).drop 5 = push4Bytes sel ++ (code sel).drop 10 := by
    rw [code_drop5, code_drop10]
    simp [List.append_assoc]
  have h := decodeAt_of_drop hdrop (decodeAt_push4 sel _)
  simpa using h

theorem decode_pc10 (sel : Nat) :
    decodeAt (code sel) 10 = some ({ op := .EQ }, 11) := by
  have h : (code sel).drop 10 = Opcode.toByte .EQ :: (code sel).drop 11 := by
    rw [code_drop10, code_drop11]
    simp [Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .EQ _ rfl)

theorem decode_pc11 (sel : Nat) :
    decodeAt (code sel) 11 = some ({ op := .PUSH ⟨1, by decide⟩, imm := dest }, 13) := by
  have hdrop : (code sel).drop 11 = 0x60 :: 15 :: (code sel).drop 13 := by
    rw [code_drop11, code_drop13]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (15 : UInt8) ((code sel).drop 13))
  simpa [wrap, dest] using h

theorem decode_pc13 (sel : Nat) :
    decodeAt (code sel) 13 = some ({ op := .JUMPI }, 14) := by
  have h : (code sel).drop 13 = Opcode.toByte .JUMPI :: (code sel).drop 14 := by
    rw [code_drop13, code_drop14]
    simp [Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc14 (sel : Nat) :
    decodeAt (code sel) 14 = some ({ op := .STOP }, 15) := by
  have h : (code sel).drop 14 = Opcode.toByte .STOP :: (code sel).drop 15 := by
    rw [code_drop14, code_drop15]
    simp [Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .STOP _ rfl)

theorem decode_pc15 (sel : Nat) :
    decodeAt (code sel) 15 = some ({ op := .JUMPDEST }, 16) := by
  have h : (code sel).drop 15 = Opcode.toByte .JUMPDEST :: GetBody.code := by
    rw [code_drop15]
    simp [Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem isJumpDest_15 (sel : Nat) : isJumpDest (code sel) dest = true :=
  isJumpDest_of_decode (decode_pc15 sel)

/-- Matching selector jumps into the `get` body and returns storage slot 0. -/
theorem dispatch_get_hit (sel : Nat) (n : Nat) :
    match run 32 (env sel []) (st0 n) with
    | some (Halt.ret data, _) => decodeWord data = wrap n
    | _ => False := by
  let e := env sel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [0], pc := 1 } := by
    have h := step_push e (st0 n) 0 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 31 e (st0 n) _ s0]
  have s1 : step e { st0 n with stack := [0], pc := 1 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 2 } := by
    have h := step_calldataload e { st0 n with stack := [0], pc := 1 } 0 []
      (decode_pc1 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using h
  rw [run_of_next 30 e _ _ s1]
  have s2 :
      step e { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 2 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 4 } := by
    have h := step_push e
      { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 2 } 0xE0 (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 29 e _ _ s2]
  have s4 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 4 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 5 } := by
    have h := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 4 }
      0xE0 (calldataLoad (packCall sel []) 0) [] (decode_pc4 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 28 e _ _ s4]
  have s5 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 5 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)],
            pc := 10 } := by
    have h := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 5 }
      (sel % 2 ^ 32) (decode_pc5 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 27 e _ _ s5]
  have s10 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 10 } =
        StepResult.next { st0 n with stack := [1], pc := 11 } := by
    have h := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 10 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall sel []) 0)) []
      (decode_pc10 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at h ⊢
    exact h
  rw [run_of_next 26 e _ _ s10]
  have s11 : step e { st0 n with stack := [1], pc := 11 } =
      StepResult.next { st0 n with stack := [dest, 1], pc := 13 } := by
    have h := step_push e { st0 n with stack := [1], pc := 11 } dest (decode_pc11 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 25 e _ _ s11]
  have s13 : step e { st0 n with stack := [dest, 1], pc := 13 } =
      StepResult.next { st0 n with stack := [], pc := dest } := by
    have h := step_jumpi_nz e { st0 n with stack := [dest, 1], pc := 13 } dest 1 []
      (decode_pc13 sel) rfl (by decide) (isJumpDest_15 sel)
    simpa [env] using h
  rw [run_of_next 24 e _ _ s13]
  have s15 : step e { st0 n with stack := [], pc := dest } =
      StepResult.next { st0 n with stack := [], pc := 16 } := by
    have hdec : decodeAt e.code dest = some ({ op := .JUMPDEST }, 16) := by
      simpa [env, dest] using decode_pc15 sel
    exact step_jumpdest e { st0 n with stack := [], pc := dest } hdec
  rw [run_of_next 23 e _ _ s15]
  have hcode : e.code = preBytes sel ++ GetBody.code := rfl
  have d16 : decodeAt e.code 16 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 17) := by
    rw [hcode, show (16 : Nat) = (preBytes sel).length + 0 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc0
  have s16 : step e { st0 n with stack := [], pc := 16 } =
      StepResult.next { st0 n with stack := [0], pc := 17 } := by
    have h := step_push e { st0 n with stack := [], pc := 16 } 0 d16
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 22 e _ _ s16]
  have d17 : decodeAt e.code 17 = some ({ op := .SLOAD }, 18) := by
    rw [hcode, show (17 : Nat) = (preBytes sel).length + 1 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc1
  have s17 : step e { st0 n with stack := [0], pc := 17 } =
      StepResult.next { st0 n with stack := [n], pc := 18 } := by
    have h := step_sload e { st0 n with stack := [0], pc := 17 } 0 [] d17 rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using h
  rw [run_of_next 21 e _ _ s17]
  have d18 : decodeAt e.code 18 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 19) := by
    rw [hcode, show (18 : Nat) = (preBytes sel).length + 2 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc2
  have s18 : step e { st0 n with stack := [n], pc := 18 } =
      StepResult.next { st0 n with stack := [0, n], pc := 19 } := by
    have h := step_push e { st0 n with stack := [n], pc := 18 } 0 d18
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 20 e _ _ s18]
  have d19 : decodeAt e.code 19 = some ({ op := .MSTORE }, 20) := by
    rw [hcode, show (19 : Nat) = (preBytes sel).length + 3 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc3
  have s19 : step e { st0 n with stack := [0, n], pc := 19 } =
      StepResult.next
        { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 20 } :=
    step_mstore e { st0 n with stack := [0, n], pc := 19 } 0 n [] d19 rfl
  rw [run_of_next 19 e _ _ s19]
  have d20 : decodeAt e.code 20 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 22) := by
    rw [hcode, show (20 : Nat) = (preBytes sel).length + 4 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc4
  have s20 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 20 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 22 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 20 } 32 d20
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 18 e _ _ s20]
  have d22 : decodeAt e.code 22 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 23) := by
    rw [hcode, show (22 : Nat) = (preBytes sel).length + 6 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc6
  have s22 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 22 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 23 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 22 } 0 d22
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 17 e _ _ s22]
  have d23 : decodeAt e.code 23 = some ({ op := .RETURN }, 24) := by
    rw [hcode, show (23 : Nat) = (preBytes sel).length + 7 from by simp [preBytes_length]]
    simpa [preBytes_length] using GetBody.decode_suffix (preBytes sel) GetBody.decode_pc7
  have s23 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 23 } =
        StepResult.halt
          (.ret ((List.range 32).map fun i =>
            memGet (memStore (st0 n).mem 0 n) (0 + i)))
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 23 } := by
    have h := step_return e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 23 }
      0 32 [] d23 rfl
    simpa using h
  rw [run_of_halt 16 e _ _ _ s23]
  rw [GetBody.memStore_packWord]
  simp only
  exact decodeWord_packWord_of_lt (wrap_lt n)

/-- A different 4-byte selector does not enter the body. -/
theorem dispatch_get_miss (sel other : Nat) (n : Nat)
    (hne : other % 2 ^ 32 ≠ sel % 2 ^ 32) :
    match run 32 { env sel [] with calldata := packCall other [] } (st0 n) with
    | some (Halt.stop, _) => True
    | _ => False := by
  let e : Env := { env sel [] with calldata := packCall other [] }
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [0], pc := 1 } := by
    have h := step_push e (st0 n) 0 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 31 e (st0 n) _ s0]
  have s1 : step e { st0 n with stack := [0], pc := 1 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 2 } := by
    have h := step_calldataload e { st0 n with stack := [0], pc := 1 } 0 []
      (decode_pc1 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using h
  rw [run_of_next 30 e _ _ s1]
  have s2 :
      step e { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 2 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 4 } := by
    have h := step_push e
      { st0 n with stack := [calldataLoad (packCall other []) 0], pc := 2 } 0xE0 (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 29 e _ _ s2]
  have s4 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 4 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 5 } := by
    have h := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall other []) 0], pc := 4 }
      0xE0 (calldataLoad (packCall other []) 0) [] (decode_pc4 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 28 e _ _ s4]
  have s5 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 5 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)],
            pc := 10 } := by
    have h := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 5 }
      (sel % 2 ^ 32) (decode_pc5 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 27 e _ _ s5]
  have s10 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 10 } =
        StepResult.next { st0 n with stack := [0], pc := 11 } := by
    have h := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall other []) 0)], pc := 10 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall other []) 0)) []
      (decode_pc10 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW] at h ⊢
    split_ifs at h with heq
    · exact absurd heq.symm (by simpa using hne)
    · exact h
  rw [run_of_next 26 e _ _ s10]
  have s11 : step e { st0 n with stack := [0], pc := 11 } =
      StepResult.next { st0 n with stack := [dest, 0], pc := 13 } := by
    have h := step_push e { st0 n with stack := [0], pc := 11 } dest (decode_pc11 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 25 e _ _ s11]
  have s13 : step e { st0 n with stack := [dest, 0], pc := 13 } =
      StepResult.next { st0 n with stack := [], pc := 14 } := by
    have h := step_jumpi_zero e { st0 n with stack := [dest, 0], pc := 13 } dest []
      (decode_pc13 sel) rfl
    simpa using h
  rw [run_of_next 24 e _ _ s13]
  have s14 : step e { st0 n with stack := [], pc := 14 } =
      StepResult.halt .stop { st0 n with stack := [], pc := 14 } :=
    step_stop e { st0 n with stack := [], pc := 14 } (decode_pc14 sel)
  rw [run_of_halt 23 e _ _ _ s14]
  trivial

end Lsc3.Compile.DispatchGet
