import Lsc3.EVM.Step
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Compositional lemmas for `Lsc3.EVM`

These are the building blocks of `bytecode_ok`. They reason about `step` from a `decodeAt`
hypothesis rather than by kernel-reducing a whole program (MSTORE of 32 bytes already exceeds
the heartbeat budget).
-/

namespace Lsc3.EVM

open Lsc3 (wordBound)

/-! ## Memory -/

@[simp] theorem memGet_memSet_eq (m : Mem) (off : Nat) (b : UInt8) :
    memGet (memSet m off b) off = b := by
  simp [memGet, memSet]

@[simp] theorem memGet_memSet_ne (m : Mem) (off off' : Nat) (b : UInt8) (h : off' ≠ off) :
    memGet (memSet m off b) off' = memGet m off' := by
  simp [memGet, memSet, h]

/-! ## Stack -/

@[simp] theorem stackPop_cons (x : Word) (xs : List Word) :
    stackPop (x :: xs) = some (x, xs) := rfl

@[simp] theorem pop2_cons (a b : Word) (rest : List Word) :
    pop2 (a :: b :: rest) = some (a, b, rest) := rfl

@[simp] theorem pop3_cons (a b c : Word) (rest : List Word) :
    pop3 (a :: b :: c :: rest) = some (a, b, c, rest) := rfl

theorem stackPush_of_lt (s : List Word) (v : Word) (h : s.length < 1024) :
    stackPush s v = some (v :: s) := by
  simp [stackPush, Nat.not_le.mpr h]

/-! ## `memStore` bytes (no kernel reduction of 32 writes) -/

theorem memGet_foldl_memSet (m : Mem) (off : Nat) (byte : Nat → UInt8) (k j : Nat)
    (hj : j < k) :
    memGet ((List.range k).foldl (fun mem i => memSet mem (off + i) (byte i)) m) (off + j) =
      byte j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hje : j = k
    · subst hje
      exact memGet_memSet_eq _ _ _
    · have hj' : j < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hje
      have hne : off + j ≠ off + k := by omega
      rw [memGet_memSet_ne _ _ _ _ hne]
      exact ih j hj'

theorem memGet_memStore (m : Mem) (off v i : Nat) (hi : i < 32) :
    memGet (memStore m off v) (off + i) =
      UInt8.ofNat ((wrap v / 256 ^ (31 - i)) % 256) := by
  simp only [memStore]
  exact memGet_foldl_memSet m off
    (fun j => UInt8.ofNat ((wrap v / 256 ^ (31 - j)) % 256)) 32 i hi

theorem memGet_foldl_memSet_ne (m : Mem) (off : Nat) (byte : Nat → UInt8) (k j : Nat)
    (hj : ∀ i, i < k → j ≠ off + i) :
    memGet ((List.range k).foldl (fun mem i => memSet mem (off + i) (byte i)) m) j =
      memGet m j := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hne : j ≠ off + k := hj k (Nat.lt_succ_self k)
    rw [memGet_memSet_ne _ _ _ _ hne]
    exact ih m (fun i hi => hj i (Nat.lt_succ_of_lt hi))

theorem memGet_memStore_ne (m : Mem) (off v j : Nat)
    (h : ∀ i, i < 32 → j ≠ off + i) :
    memGet (memStore m off v) j = memGet m j := by
  simp only [memStore]
  exact memGet_foldl_memSet_ne m off
    (fun i => UInt8.ofNat ((wrap v / 256 ^ (31 - i)) % 256)) 32 j h

@[simp] theorem wrap_lt (n : Nat) : wrap n < wordBound :=
  Nat.mod_lt n (by decide)

@[simp] theorem wrap_wrap (n : Nat) : wrap (wrap n) = wrap n :=
  Nat.mod_eq_of_lt (wrap_lt n)

@[simp] theorem eqW_self (a : Word) : eqW a a = 1 := by simp [eqW]

theorem eqW_eq {a b : Word} (h : a = b) : eqW a b = 1 := by simp [eqW, h]

theorem eqW_ne {a b : Word} (h : a ≠ b) : eqW a b = 0 := by simp [eqW, h]

theorem list_length_lt_1024 {α} {xs : List α} {k : Nat}
    (hk : xs.length = k) (hbound : k < 1024 := by decide) : xs.length < 1024 :=
  hk ▸ hbound

/-! ## Decode round-trip -/

theorem ofByte_toByte (op : Opcode) : Opcode.ofByte op.toByte = some op := by
  cases op with
  | PUSH k => fin_cases k <;> rfl
  | DUP k => fin_cases k <;> rfl
  | SWAP k => fin_cases k <;> rfl
  | LOG k => fin_cases k <;> rfl
  | STOP => rfl | ADD => rfl | MUL => rfl | SUB => rfl | DIV => rfl | MOD => rfl
  | ADDMOD => rfl | MULMOD => rfl
  | LT => rfl | GT => rfl | EQ => rfl | ISZERO => rfl | AND => rfl | OR => rfl
  | XOR => rfl | NOT => rfl | SHL => rfl | SHR => rfl
  | KECCAK256 => rfl
  | ADDRESS => rfl | CALLER => rfl | CALLVALUE => rfl | CALLDATALOAD => rfl
  | CALLDATASIZE => rfl | CALLDATACOPY => rfl | CODESIZE => rfl | CODECOPY => rfl
  | TIMESTAMP => rfl | NUMBER => rfl
  | POP => rfl | MLOAD => rfl | MSTORE => rfl | SLOAD => rfl | SSTORE => rfl
  | JUMP => rfl | JUMPI => rfl | JUMPDEST => rfl | TLOAD => rfl | TSTORE => rfl
  | CALL => rfl
  | RETURN => rfl | REVERT => rfl | INVALID => rfl

theorem decodeAt_op_head (op : Opcode) (rest : List UInt8)
    (himm : Opcode.immBytes op = 0) :
    decodeAt (op.toByte :: rest) 0 = some ({ op := op }, 1) := by
  unfold decodeAt
  have hpc : 0 < (op.toByte :: rest).length := by simp
  rw [dif_pos hpc, List.getElem_cons_zero, ofByte_toByte]
  simp [himm, readImm, wrap]

theorem decodeAt_eq_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .EQ :: rest) 0 = some ({ op := .EQ }, 1) :=
  decodeAt_op_head .EQ rest rfl

theorem decodeAt_iszero_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .ISZERO :: rest) 0 = some ({ op := .ISZERO }, 1) :=
  decodeAt_op_head .ISZERO rest rfl

theorem decodeAt_calldataload_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .CALLDATALOAD :: rest) 0 = some ({ op := .CALLDATALOAD }, 1) :=
  decodeAt_op_head .CALLDATALOAD rest rfl

/-! ## `step` from a decode hypothesis -/

@[simp] theorem run_succ (n : Nat) (env : Env) (s : State) :
    run (n + 1) env s =
      match step env s with
      | StepResult.halt h s' => some (h, s')
      | StepResult.next s' => run n env s' :=
  rfl

theorem step_stop (env : Env) (s : State) {nextPc : Nat}
    (h : decodeAt env.code s.pc = some ({ op := .STOP }, nextPc)) :
    step env s = StepResult.halt .stop s := by
  unfold step
  rw [h]

theorem step_jumpdest (env : Env) (s : State) {nextPc : Nat}
    (h : decodeAt env.code s.pc = some ({ op := .JUMPDEST }, nextPc)) :
    step env s = StepResult.next { s with pc := nextPc } := by
  unfold step
  rw [h]

theorem step_add (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .ADD }, nextPc))
    (hst : s.stack = a :: b :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := addW a b :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_sub (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SUB }, nextPc))
    (hst : s.stack = a :: b :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := subW a b :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_push (env : Env) (s : State) (imm : Word) {k : Fin 33} {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .PUSH k, imm := imm }, nextPc))
    (hlen : s.stack.length < 1024) :
    step env s = StepResult.next { s with stack := imm :: s.stack, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [withPush, stackPush, Nat.not_le.mpr hlen]

theorem decodeAt_stop_head (rest : List UInt8) :
    decodeAt (0x00 :: rest) 0 = some ({ op := .STOP }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_push0_head (rest : List UInt8) :
    decodeAt (0x5f :: rest) 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_sload_head (rest : List UInt8) :
    decodeAt (0x54 :: rest) 0 = some ({ op := .SLOAD }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_mstore_head (rest : List UInt8) :
    decodeAt (0x52 :: rest) 0 = some ({ op := .MSTORE }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_return_head (rest : List UInt8) :
    decodeAt (0xf3 :: rest) 0 = some ({ op := .RETURN }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_revert_head (rest : List UInt8) :
    decodeAt (0xfd :: rest) 0 = some ({ op := .REVERT }, 1) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

theorem decodeAt_push1_head (imm : UInt8) (rest : List UInt8) :
    decodeAt (0x60 :: imm :: rest) 0 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := wrap imm.toNat }, 2) := by
  unfold decodeAt Opcode.ofByte Opcode.immBytes readImm
  simp [wrap]

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

theorem memLoad_memStore_ne (m : Mem) (off v off' : Nat)
    (h : off' + 32 ≤ off ∨ off + 32 ≤ off') :
    memLoad (memStore m off v) off' = memLoad m off' := by
  simp only [memLoad]
  apply congrArg wrap
  refine foldl_range_eq 32 _ _ ?_ 0
  intro acc i hi
  have hne : memGet (memStore m off v) (off' + i) = memGet m (off' + i) := by
    apply memGet_memStore_ne
    intro k hk
    cases h with
    | inl hle => omega
    | inr hle => omega
  rw [hne]

/-- Immediate bytes at `pc` are the prefix of `code.drop pc`. -/
theorem readImm_drop (code : List UInt8) (pc immLen : Nat) :
    readImm code pc immLen = readImm (code.drop pc) 0 immLen := by
  simp only [readImm]
  congr 1
  apply foldl_range_eq
  intro acc i hi
  have hiff : pc + 1 + i < code.length ↔ 1 + i < (code.drop pc).length := by
    simp [List.length_drop]
    omega
  by_cases h1 : pc + 1 + i < code.length
  · have h2 : 1 + i < (code.drop pc).length := hiff.mp h1
    rw [if_pos h1, if_pos h2, getElem!_pos code (pc + 1 + i) h1,
      getElem!_pos (code.drop pc) (1 + i) h2, List.getElem_drop,
      getElem_congr_idx (Nat.add_assoc pc 1 i)]
  · have h2 : ¬ 1 + i < (code.drop pc).length := mt hiff.mpr h1
    rw [if_neg h1, if_neg h2]

/-- Decoding at `pc` is decoding the suffix from 0, with PCs shifted. -/
theorem decodeAt_drop (code : List UInt8) (pc : Nat) :
    decodeAt code pc =
      (decodeAt (code.drop pc) 0).map fun p => (p.1, p.2 + pc) := by
  simp only [decodeAt]
  by_cases hpc : pc < code.length
  · have hdrop : 0 < (code.drop pc).length := by
      simp [List.length_drop]; omega
    rw [dif_pos hpc, dif_pos hdrop]
    have hbyte : code[pc] = (code.drop pc)[0] :=
      (List.getElem_drop (xs := code) (i := pc) (j := 0) (h := hdrop)).symm
    rw [hbyte]
    cases Opcode.ofByte (code.drop pc)[0] with
    | none => simp [Nat.add_comm]
    | some op => simp [readImm_drop, Nat.add_comm]
  · have hdrop0 : ¬ 0 < (code.drop pc).length := by
      simp [List.length_drop]; omega
    rw [dif_neg hpc, dif_neg hdrop0]
    rfl

theorem decodeAt_of_drop {instr : Instr} {n0 pc : Nat} {code rest : List UInt8}
    (h : code.drop pc = rest)
    (hd : decodeAt rest 0 = some (instr, n0)) :
    decodeAt code pc = some (instr, n0 + pc) := by
  rw [decodeAt_drop, h, hd]
  rfl

/-- Decoding after a prefix is decoding the suffix, with PCs shifted by the prefix length. -/
theorem decodeAt_append (pre rest : List UInt8) (pc : Nat) :
    decodeAt (pre ++ rest) (pre.length + pc) =
      (decodeAt rest pc).map fun p => (p.1, p.2 + pre.length) := by
  have hdrop : (pre ++ rest).drop (pre.length + pc) = rest.drop pc := by
    rw [← List.drop_drop, List.drop_left]
  rw [decodeAt_drop, decodeAt_drop (code := rest), hdrop]
  cases decodeAt (rest.drop pc) 0 with
  | none => rfl
  | some p =>
    simp [Nat.add_assoc, Nat.add_comm pc]

theorem run_extra (n k : Nat) (env : Env) (s : State) {r : Halt × State}
    (h : run n env s = some r) : run (n + k) env s = some r := by
  induction n generalizing s with
  | zero => simp [run_zero] at h
  | succ n ih =>
    rw [show n.succ + k = (n + k).succ from Nat.succ_add n k]
    rw [run_succ] at h ⊢
    cases hstep : step env s with
    | halt _ _ =>
      simp [hstep] at h ⊢
      exact h
    | next s' =>
      simp [hstep] at h ⊢
      exact ih s' h

/-- Extra fuel does not change a `RETURN` that already happened. -/
theorem ret_run_extra (n k : Nat) (env : Env) (s : State) (P : List UInt8 → Prop)
    (h : match run n env s with
         | some (Halt.ret data, _) => P data
         | _ => False) :
    match run (n + k) env s with
    | some (Halt.ret data, _) => P data
    | _ => False := by
  generalize hr : run n env s = r at h
  cases r with
  | none =>
    simp only at h
  | some p =>
    cases p with
    | mk hlt s' =>
      cases hlt with
      | ret data =>
        have hextra : run (n + k) env s = some (Halt.ret data, s') :=
          run_extra n k env s (by rw [hr])
        rw [hextra]
        exact h
      | stop =>
        simp only at h
      | revert _ =>
        simp only at h
      | exceptional _ =>
        simp only at h

theorem run_of_next (n : Nat) (env : Env) (s s' : State)
    (h : step env s = StepResult.next s') :
    run (n + 1) env s = run n env s' := by
  rw [run_succ, h]

theorem run_of_halt (n : Nat) (env : Env) (s s' : State) (hlt : Halt)
    (h : step env s = StepResult.halt hlt s') :
    run (n + 1) env s = some (hlt, s') := by
  rw [run_succ, h]

theorem step_sload (env : Env) (s : State) (key : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SLOAD }, nextPc))
    (hst : s.stack = key :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := s.storage key :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackPop, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_mstore (env : Env) (s : State) (off v : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .MSTORE }, nextPc))
    (hst : s.stack = off :: v :: rest) :
    step env s = StepResult.next { s with mem := memStore s.mem off v, stack := rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2]

theorem step_return (env : Env) (s : State) (off size : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .RETURN }, nextPc))
    (hst : s.stack = off :: size :: rest) :
    step env s = StepResult.halt (.ret ((List.range size).map fun i => memGet s.mem (off + i))) s := by
  unfold step
  rw [hdec]
  simp [hst, pop2, haltRet]

theorem step_revert (env : Env) (s : State) (off size : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .REVERT }, nextPc))
    (hst : s.stack = off :: size :: rest) :
    step env s = StepResult.halt (.revert ((List.range size).map fun i => memGet s.mem (off + i))) s := by
  unfold step
  rw [hdec]
  simp [hst, pop2, haltRevert]

theorem step_eq (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .EQ }, nextPc))
    (hst : s.stack = a :: b :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := eqW a b :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_lt (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .LT }, nextPc))
    (hst : s.stack = a :: b :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := ltW a b :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_shr (env : Env) (s : State) (shift value : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SHR }, nextPc))
    (hst : s.stack = shift :: value :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := shrW shift value :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_calldataload (env : Env) (s : State) (off : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .CALLDATALOAD }, nextPc))
    (hst : s.stack = off :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next
      { s with stack := calldataLoad env.calldata off :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackPop, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_calldatasize (env : Env) (s : State) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .CALLDATASIZE }, nextPc))
    (hlen : s.stack.length < 1024) :
    step env s = StepResult.next
      { s with stack := env.calldata.length :: s.stack, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_jumpi_zero (env : Env) (s : State) (dest : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .JUMPI }, nextPc))
    (hst : s.stack = dest :: 0 :: rest) :
    step env s = StepResult.next { s with stack := rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2]

theorem step_jumpi_nz (env : Env) (s : State) (dest cond : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .JUMPI }, nextPc))
    (hst : s.stack = dest :: cond :: rest)
    (hcond : cond ≠ 0)
    (hdest : isJumpDest env.code dest = true) :
    step env s = StepResult.next { s with stack := rest, pc := dest } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, hcond, hdest]

theorem step_jump (env : Env) (s : State) (dest : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .JUMP }, nextPc))
    (hst : s.stack = dest :: rest)
    (hdest : isJumpDest env.code dest = true) :
    step env s = StepResult.next { s with stack := rest, pc := dest } := by
  unfold step
  rw [hdec]
  simp [hst, stackPop, hdest]

theorem isJumpDest_of_decode {code : List UInt8} {dest nextPc : Nat}
    (h : decodeAt code dest = some ({ op := .JUMPDEST }, nextPc)) :
    isJumpDest code dest = true := by
  simp [isJumpDest, h]

theorem step_dup1 (env : Env) (s : State) (x : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .DUP ⟨0, by decide⟩ }, nextPc))
    (hst : s.stack = x :: rest)
    (hlen : (x :: rest).length < 1024) :
    step env s = StepResult.next { s with stack := x :: x :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  have hpush : ¬ 1023 ≤ rest.length := by
    simp at hlen; omega
  simp [hst, stackDup, stackPush, hpush]

theorem step_dup2 (env : Env) (s : State) (x y : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .DUP ⟨1, by decide⟩ }, nextPc))
    (hst : s.stack = x :: y :: rest)
    (hlen : (x :: y :: rest).length < 1024) :
    step env s = StepResult.next { s with stack := y :: x :: y :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  have hpush : ¬ 1022 ≤ rest.length := by
    simp at hlen; omega
  simp [hst, stackDup, stackPush, hpush]

theorem step_swap1 (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SWAP ⟨0, by decide⟩ }, nextPc))
    (hst : s.stack = a :: b :: rest) :
    step env s = StepResult.next { s with stack := b :: a :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackSwap]

theorem step_swap2 (env : Env) (s : State) (a b c : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SWAP ⟨1, by decide⟩ }, nextPc))
    (hst : s.stack = a :: b :: c :: rest) :
    step env s = StepResult.next { s with stack := c :: b :: a :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackSwap]

theorem step_gt (env : Env) (s : State) (a b : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .GT }, nextPc))
    (hst : s.stack = a :: b :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := gtW a b :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_iszero (env : Env) (s : State) (a : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .ISZERO }, nextPc))
    (hst : s.stack = a :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next { s with stack := iszeroW a :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackPop, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_sstore (env : Env) (s : State) (key v : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .SSTORE }, nextPc))
    (hst : s.stack = key :: v :: rest) :
    step env s = StepResult.next
      { s with storage := fun k => if k = key then v else s.storage k, stack := rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, pop2]

theorem step_mload (env : Env) (s : State) (off : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .MLOAD }, nextPc))
    (hst : s.stack = off :: rest)
    (hlen : rest.length < 1024) :
    step env s = StepResult.next
      { s with stack := memLoad s.mem off :: rest, pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, stackPop, withPush, stackPush, Nat.not_le.mpr hlen]

theorem step_log1 (env : Env) (s : State) (off size topic : Word) (rest : List Word) {nextPc : Nat}
    (hdec : decodeAt env.code s.pc = some ({ op := .LOG ⟨1, by decide⟩ }, nextPc))
    (hst : s.stack = off :: size :: topic :: rest) :
    step env s = StepResult.next
      { s with
        logs := s.logs ++
          [{ topics := [topic]
             data := (List.range size).map fun i => memGet s.mem (off + i) }]
        stack := rest
        pc := nextPc } := by
  unfold step
  rw [hdec]
  simp [hst, popN]
  split_ifs with hif
  · omega
  · simp

theorem decodeAt_add_head (rest : List UInt8) :
    decodeAt (0x01 :: rest) 0 = some ({ op := .ADD }, 1) :=
  decodeAt_op_head .ADD rest rfl

theorem decodeAt_sub_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .SUB :: rest) 0 = some ({ op := .SUB }, 1) :=
  decodeAt_op_head .SUB rest rfl

theorem decodeAt_gt_head (rest : List UInt8) :
    decodeAt (0x11 :: rest) 0 = some ({ op := .GT }, 1) :=
  decodeAt_op_head .GT rest rfl

theorem decodeAt_sstore_head (rest : List UInt8) :
    decodeAt (0x55 :: rest) 0 = some ({ op := .SSTORE }, 1) :=
  decodeAt_op_head .SSTORE rest rfl

theorem decodeAt_mload_head (rest : List UInt8) :
    decodeAt (0x51 :: rest) 0 = some ({ op := .MLOAD }, 1) :=
  decodeAt_op_head .MLOAD rest rfl

theorem decodeAt_dup1_head (rest : List UInt8) :
    decodeAt (0x80 :: rest) 0 = some ({ op := .DUP ⟨0, by decide⟩ }, 1) :=
  decodeAt_op_head (.DUP ⟨0, by decide⟩) rest rfl

theorem decodeAt_dup2_head (rest : List UInt8) :
    decodeAt (0x81 :: rest) 0 = some ({ op := .DUP ⟨1, by decide⟩ }, 1) :=
  decodeAt_op_head (.DUP ⟨1, by decide⟩) rest rfl

theorem decodeAt_swap1_head (rest : List UInt8) :
    decodeAt (0x90 :: rest) 0 = some ({ op := .SWAP ⟨0, by decide⟩ }, 1) :=
  decodeAt_op_head (.SWAP ⟨0, by decide⟩) rest rfl

theorem decodeAt_swap2_head (rest : List UInt8) :
    decodeAt (0x91 :: rest) 0 = some ({ op := .SWAP ⟨1, by decide⟩ }, 1) :=
  decodeAt_op_head (.SWAP ⟨1, by decide⟩) rest rfl

theorem decodeAt_log1_head (rest : List UInt8) :
    decodeAt (0xa1 :: rest) 0 = some ({ op := .LOG ⟨1, by decide⟩ }, 1) :=
  decodeAt_op_head (.LOG ⟨1, by decide⟩) rest rfl

theorem decodeAt_jump_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .JUMP :: rest) 0 = some ({ op := .JUMP }, 1) :=
  decodeAt_op_head .JUMP rest rfl

theorem decodeAt_jumpi_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .JUMPI :: rest) 0 = some ({ op := .JUMPI }, 1) :=
  decodeAt_op_head .JUMPI rest rfl

theorem decodeAt_jumpdest_head (rest : List UInt8) :
    decodeAt (Opcode.toByte .JUMPDEST :: rest) 0 = some ({ op := .JUMPDEST }, 1) :=
  decodeAt_op_head .JUMPDEST rest rfl

/-- Unsigned add overflow test used by `checkedAdd`: `GT n (n+1)` is 0 when `n+1` fits. -/
theorem gtW_add_no_overflow {n : Nat} (h : n + 1 < wordBound) :
    gtW n (addW n 1) = 0 := by
  simp [gtW, addW, wrap, Nat.mod_eq_of_lt h]

theorem addW_succ_of_lt {n : Nat} (h : n + 1 < wordBound) :
    addW n 1 = n + 1 := by
  simp [addW, wrap, Nat.mod_eq_of_lt h]

theorem addW_of_lt {a b : Nat} (h : a + b < wordBound) : addW a b = a + b := by
  simp [addW, wrap, Nat.mod_eq_of_lt h]

theorem gtW_add_of_lt {a b : Nat} (h : a + b < wordBound) : gtW a (addW a b) = 0 := by
  rw [addW_of_lt h]
  simp [gtW]
  try exact Nat.not_lt.mpr (Nat.le_add_right a b)

theorem addW_succ_overflow {n : Nat} (h : n + 1 = wordBound) :
    addW n 1 = 0 := by
  simp [addW, wrap, h]

theorem gtW_add_overflow {n : Nat} (h : n + 1 = wordBound) :
    gtW n (addW n 1) = 1 := by
  have hn0 : 0 < n := by
    have : n = wordBound - 1 := Nat.eq_sub_of_add_eq h
    subst this
    decide
  rw [addW_succ_overflow h]
  simp [gtW, hn0]

/-- `checkedAdd` overflow test for a two-word add: `GT a (a+b)` is 1 when the sum wraps. -/
theorem gtW_add_of_ge {a b : Nat} (ha : a < wordBound) (hb : b < wordBound)
    (h : wordBound ≤ a + b) : gtW a (addW a b) = 1 := by
  have hrest : a + b - wordBound < wordBound := by
    have : a + b < wordBound + wordBound := Nat.add_lt_add ha hb
    omega
  have hmod : (a + b) % wordBound = a + b - wordBound := by
    calc
      (a + b) % wordBound
          = (wordBound + (a + b - wordBound)) % wordBound := by rw [Nat.add_sub_of_le h]
      _ = (wordBound % wordBound + (a + b - wordBound) % wordBound) % wordBound :=
        Nat.add_mod _ _ _
      _ = (a + b - wordBound) % wordBound := by simp [Nat.mod_self]
      _ = a + b - wordBound := Nat.mod_eq_of_lt hrest
  have hlt : a + b - wordBound < a := by
    have : a + b < a + wordBound := Nat.add_lt_add_left hb a
    omega
  simp [gtW, addW, wrap, hmod, hlt]

/-- `checkedSub` overflow test: `GT 1 n` is 0 when `n ≥ 1`. -/
theorem gtW_one_of_pos {n : Nat} (h : 0 < n) : gtW 1 n = 0 := by
  simp [gtW]; omega

theorem subW_pred {n : Nat} (hpos : 0 < n) (hn : n < wordBound) :
    subW n 1 = n - 1 := by
  have hsum : n + wordBound - 1 = n - 1 + wordBound := by omega
  unfold subW wrap
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt]
  omega

end Lsc3.EVM
