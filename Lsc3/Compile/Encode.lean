import Lsc3.Compile.Instr

/-!
# LSC v3 — encode structured assembly to bytecode
-/

namespace Lsc3.Compile

open Lsc3.EVM

def pushWidth (n : Nat) : Nat :=
  if n == 0 then 0 else Nat.div (Nat.log2 n) 8 + 1

def pushOpcode (width : Nat) : Opcode :=
  if h : width < 33 then .PUSH ⟨width, h⟩ else .PUSH ⟨32, by decide⟩

def natToBytesLE (n : Nat) : Nat → List UInt8
  | 0 => []
  | w + 1 => UInt8.ofNat (n % 256) :: natToBytesLE (n / 256) w

def natToBytesBE (n : Nat) (width : Nat) : List UInt8 :=
  (natToBytesLE n width).reverse

def emitPush (n : Nat) : List UInt8 :=
  let width := pushWidth n
  let op := Opcode.toByte (pushOpcode width)
  op :: natToBytesBE n width

/-- Jumps use a fixed `PUSH2` so layout is stable (no width fixpoint) and PCs stay
small enough for compositional `bytecode_ok`. Contracts whose labels fall at
`≥ 2^16` are rejected at encode time. -/
def jumpImmBound : Nat := 2 ^ 16

def emitPush2 (n : Nat) : List UInt8 :=
  Opcode.toByte (.PUSH ⟨2, by decide⟩) :: natToBytesBE n 2

def emitPush4 (n : Nat) : List UInt8 :=
  Opcode.toByte (.PUSH ⟨4, by decide⟩) :: natToBytesBE n 4

def emitPush32 (n : Nat) : List UInt8 :=
  Opcode.toByte (.PUSH ⟨32, by decide⟩) :: natToBytesBE n 32

def emitJumpPush (pc : Nat) : Except String (List UInt8) :=
  if pc < jumpImmBound then
    .ok (emitPush2 pc)
  else
    .error s!"jump target {pc} exceeds PUSH2"

theorem emitJumpPush_of_lt {pc : Nat} (h : pc < jumpImmBound) :
    emitJumpPush pc = .ok (emitPush2 pc) := by
  unfold emitJumpPush
  exact if_pos h

def jumpDestLabels (instrs : List Asm) : List String :=
  instrs.filterMap fun
  | .jumpDest lbl => some lbl
  | _ => none

def checkDuplicateLabels (instrs : List Asm) : Except String Unit := do
  let labels := jumpDestLabels instrs
  unless labels.Nodup do
    throw s!"duplicate jump label in {labels}"

def instrByteSize (_labels : List (String × Nat)) : Asm → Nat
  | .op _ => 1
  | .push n => 1 + pushWidth n
  | .push4 _ => 5
  | .push32 _ => 33
  | .pushLabel _ => 3
  | .jump _ => 4
  | .jumpi _ => 4
  | .jumpDest _ => 1

def layoutLabelsFrom (pc : Nat) (instrs : List Asm) (acc : List (String × Nat)) :
    List (String × Nat) :=
  match instrs with
  | [] => acc
  | .jumpDest lbl :: tail => layoutLabelsFrom (pc + 1) tail ((lbl, pc) :: acc)
  | i :: tail => layoutLabelsFrom (pc + instrByteSize [] i) tail acc

def layoutLabels (instrs : List Asm) : List (String × Nat) :=
  layoutLabelsFrom 0 instrs []

def lookupLabel (labels : List (String × Nat)) (lbl : String) : Except String Nat :=
  match labels.find? (·.1 == lbl) with
  | some (_, pc) => .ok pc
  | none => .error s!"unknown jump label: {lbl}"

def emitOne (labels : List (String × Nat)) : Asm → Except String (List UInt8)
  | .op op => pure [Opcode.toByte op]
  | .push n => pure (emitPush n)
  | .push4 n => pure (emitPush4 n)
  | .push32 n => pure (emitPush32 n)
  | .pushLabel lbl => do
    let pc ← lookupLabel labels lbl
    emitJumpPush pc
  | .jump lbl => do
    let pc ← lookupLabel labels lbl
    let bytes ← emitJumpPush pc
    pure (bytes ++ [Opcode.toByte .JUMP])
  | .jumpi lbl => do
    let pc ← lookupLabel labels lbl
    let bytes ← emitJumpPush pc
    pure (bytes ++ [Opcode.toByte .JUMPI])
  | .jumpDest _ => pure [Opcode.toByte .JUMPDEST]

def emitInstrs (labels : List (String × Nat)) : List Asm → Except String (List UInt8)
  | [] => .ok []
  | i :: rest => do
    let b ← emitOne labels i
    let bs ← emitInstrs labels rest
    pure (b ++ bs)

@[simp] theorem emitInstrs_nil (labels : List (String × Nat)) :
    emitInstrs labels [] = .ok [] := rfl

theorem emitInstrs_cons (labels : List (String × Nat)) (i : Asm) (rest : List Asm) :
    emitInstrs labels (i :: rest) =
      emitOne labels i >>= fun b =>
        emitInstrs labels rest >>= fun bs => pure (b ++ bs) :=
  rfl

theorem emitInstrs_append (labels : List (String × Nat)) (as bs : List Asm) :
    emitInstrs labels (as ++ bs) =
      emitInstrs labels as >>= fun a =>
        emitInstrs labels bs >>= fun b => pure (a ++ b) := by
  induction as with
  | nil =>
    simp only [List.nil_append, emitInstrs_nil]
    cases emitInstrs labels bs <;> rfl
  | cons i as ih =>
    simp only [List.cons_append, emitInstrs_cons, ih]
    cases emitOne labels i <;> cases emitInstrs labels as <;>
      cases emitInstrs labels bs
    all_goals simp [bind, Except.bind, pure, Except.pure, List.append_assoc]

theorem emitOne_jumpi (labels : List (String × Nat)) (lbl : String) {pc : Nat}
    (h : lookupLabel labels lbl = .ok pc) (hlt : pc < jumpImmBound) :
    emitOne labels (.jumpi lbl) = .ok (emitPush2 pc ++ [Opcode.toByte .JUMPI]) := by
  change (lookupLabel labels lbl >>= fun p =>
      (fun a => a ++ [Opcode.toByte .JUMPI]) <$> emitJumpPush p) = _
  rw [h]
  simp only [bind, Except.bind, Functor.map, Except.map]
  rw [emitJumpPush_of_lt hlt]

theorem emitOne_jump (labels : List (String × Nat)) (lbl : String) {pc : Nat}
    (h : lookupLabel labels lbl = .ok pc) (hlt : pc < jumpImmBound) :
    emitOne labels (.jump lbl) = .ok (emitPush2 pc ++ [Opcode.toByte .JUMP]) := by
  change (lookupLabel labels lbl >>= fun p =>
      (fun a => a ++ [Opcode.toByte .JUMP]) <$> emitJumpPush p) = _
  rw [h]
  simp only [bind, Except.bind, Functor.map, Except.map]
  rw [emitJumpPush_of_lt hlt]

theorem emitOne_op (labels : List (String × Nat)) (op : Opcode) :
    emitOne labels (.op op) = .ok [Opcode.toByte op] :=
  rfl

theorem emitOne_push (labels : List (String × Nat)) (n : Word) :
    emitOne labels (.push n) = .ok (emitPush n) :=
  rfl

theorem emitOne_push4 (labels : List (String × Nat)) (n : Word) :
    emitOne labels (.push4 n) = .ok (emitPush4 n) :=
  rfl

theorem emitOne_push32 (labels : List (String × Nat)) (n : Word) :
    emitOne labels (.push32 n) = .ok (emitPush32 n) :=
  rfl

theorem emitOne_jumpDest (labels : List (String × Nat)) (lbl : String) :
    emitOne labels (.jumpDest lbl) = .ok [Opcode.toByte .JUMPDEST] :=
  rfl

/-- Small immediates used by the dispatcher and `get` body. -/
theorem emitPush_zero : emitPush 0 = [0x5f] := rfl
theorem emitPush_one : emitPush 1 = [0x60, 1] := rfl
theorem emitPush_four : emitPush 4 = [0x60, 4] := rfl
theorem emitPush_e0 : emitPush 0xE0 = [0x60, 0xE0] := rfl
theorem emitPush_thirtyTwo : emitPush 32 = [0x60, 0x20] := rfl
theorem emitPush_0x11 : emitPush 0x11 = [0x60, 0x11] := rfl
theorem emitPush_thirtysix : emitPush 36 = [0x60, 36] := rfl
theorem emitPush_0x80 : emitPush 0x80 = [0x60, 0x80] := rfl
theorem emitPush_0xA0 : emitPush 0xA0 = [0x60, 0xA0] := rfl

def encode (instrs : List Asm) : Except String (List UInt8) := do
  checkDuplicateLabels instrs
  let labels := layoutLabels instrs
  emitInstrs labels instrs

def paddedSelector (sel : Nat) : Nat := sel * (2 ^ 224)

/-- Byte size of `emitPush n` (PUSH0 is 1 byte). -/
def pushByteSize (n : Nat) : Nat := 1 + pushWidth n

/-- `CODECOPY`/`RETURN` preamble. The runtime offset is always a `PUSH32` so the preamble
size does not depend on the offset (no PUSH-width fixpoint). -/
def deployPreamble (rSize rOffset : Nat) : List UInt8 :=
  emitPush rSize ++ emitPush32 rOffset ++ emitPush 0 ++ [Opcode.toByte .CODECOPY] ++
    emitPush rSize ++ emitPush 0 ++ [Opcode.toByte .RETURN]

/-- Preamble byte size; independent of `rOffset` because that immediate is always 32 bytes. -/
def deployPreambleSize (rSize : Nat) : Nat :=
  pushByteSize rSize + 33 + pushByteSize 0 + 1 +
    pushByteSize rSize + pushByteSize 0 + 1

def deployRuntimeOffset (rSize : Nat) : Nat := deployPreambleSize rSize

/-- Standard creation bytecode: preamble ++ runtime (no constructor body). Running it
`RETURN`s the runtime, which is what `CREATE` installs. -/
def deployCode (runtime : List UInt8) : List UInt8 :=
  let rSize := runtime.length
  let rOffset := deployRuntimeOffset rSize
  deployPreamble rSize rOffset ++ runtime

def toHex (bytes : List UInt8) : String :=
  let hex b :=
    let s := (BitVec.ofNat 8 b.toNat).toHex
    if s.length = 1 then "0" ++ s else s
  "0x" ++ String.join (bytes.map hex)

/-! ## Layout lemmas (kernel-checked; used by deploy certificates) -/

@[simp] theorem natToBytesLE_length (n w : Nat) : (natToBytesLE n w).length = w := by
  induction w generalizing n with
  | zero => simp [natToBytesLE]
  | succ w ih => simp [natToBytesLE, ih]

theorem natToBytesLE_getElem (n w i : Nat) (hi : i < w) :
    (natToBytesLE n w)[i]'(by simp [natToBytesLE_length]; exact hi) =
      UInt8.ofNat ((n / 256 ^ i) % 256) := by
  induction w generalizing n i with
  | zero => omega
  | succ w ih =>
    cases i with
    | zero => simp [natToBytesLE, Nat.pow_zero, Nat.div_one]
    | succ j =>
      have hj : j < w := Nat.lt_of_succ_lt_succ hi
      simp only [natToBytesLE, List.getElem_cons_succ]
      rw [ih (n / 256) j hj, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

@[simp] theorem natToBytesBE_length (n w : Nat) : (natToBytesBE n w).length = w := by
  simp [natToBytesBE]

theorem natToBytesBE_getElem (n w i : Nat) (hi : i < w) :
    (natToBytesBE n w)[i]'(by simp [natToBytesBE_length]; exact hi) =
      UInt8.ofNat ((n / 256 ^ (w - 1 - i)) % 256) := by
  simp only [natToBytesBE]
  have hlen : (natToBytesLE n w).reverse.length = w := by simp [natToBytesLE_length]
  rw [List.getElem_reverse (h := by rw [hlen]; exact hi)]
  simp [natToBytesLE_length]
  rw [natToBytesLE_getElem n w (w - 1 - i) (by omega)]

@[simp] theorem emitPush_length (n : Nat) : (emitPush n).length = pushByteSize n := by
  simp [emitPush, pushByteSize, natToBytesBE]
  omega

@[simp] theorem emitPush2_length (n : Nat) : (emitPush2 n).length = 3 := by
  simp [emitPush2, natToBytesBE]

@[simp] theorem emitPush4_length (n : Nat) : (emitPush4 n).length = 5 := by
  simp [emitPush4, natToBytesBE]

@[simp] theorem emitPush32_length (n : Nat) : (emitPush32 n).length = 33 := by
  simp [emitPush32, natToBytesBE]

theorem drop_append_length {α : Type*} (as bs : List α) :
    (as ++ bs).drop as.length = bs := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih]

@[simp] theorem deployPreamble_length (rSize rOffset : Nat) :
    (deployPreamble rSize rOffset).length = deployPreambleSize rSize := by
  simp [deployPreamble, deployPreambleSize, pushByteSize]
  omega

/-- The runtime is exactly the suffix of creation bytecode after the preamble. -/
theorem deployCode_suffix (runtime : List UInt8) :
    (deployCode runtime).drop (deployRuntimeOffset runtime.length) = runtime := by
  simp [deployCode, deployRuntimeOffset]

/-- A self-jump encodes as `PUSH2 4 JUMPI JUMPDEST`. -/
theorem encode_jumpi_here :
    encode [.jumpi "t", .jumpDest "t"] =
      .ok (emitPush2 4 ++ [Opcode.toByte .JUMPI, Opcode.toByte .JUMPDEST]) :=
  rfl

theorem encode_push4_stop (n : Nat) :
    encode [.push4 n, .op .STOP] = .ok (emitPush4 n ++ [Opcode.toByte .STOP]) :=
  rfl

end Lsc3.Compile
