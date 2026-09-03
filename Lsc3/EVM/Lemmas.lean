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
  | RETURN => rfl | REVERT => rfl | INVALID => rfl

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

end Lsc3.EVM
