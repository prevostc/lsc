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

def emitPush32 (n : Nat) : List UInt8 :=
  Opcode.toByte (.PUSH ⟨32, by decide⟩) :: natToBytesBE n 32

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
  | .pushLabel _ => 33
  | .jump _ => 34
  | .jumpi _ => 34
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
  | .pushLabel lbl => do
    let pc ← lookupLabel labels lbl
    pure (emitPush32 pc)
  | .jump lbl => do
    let pc ← lookupLabel labels lbl
    pure (emitPush32 pc ++ [Opcode.toByte .JUMP])
  | .jumpi lbl => do
    let pc ← lookupLabel labels lbl
    pure (emitPush32 pc ++ [Opcode.toByte .JUMPI])
  | .jumpDest _ => pure [Opcode.toByte .JUMPDEST]

def emitInstrs (labels : List (String × Nat)) (instrs : List Asm) :
    Except String (List UInt8) := do
  instrs.foldlM (init := []) fun acc i => do
    let bytes ← emitOne labels i
    pure (acc ++ bytes)

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

@[simp] theorem emitPush_length (n : Nat) : (emitPush n).length = pushByteSize n := by
  simp [emitPush, pushByteSize, natToBytesBE]
  omega

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

end Lsc3.Compile
