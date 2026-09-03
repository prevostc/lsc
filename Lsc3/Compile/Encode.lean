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

def toHex (bytes : List UInt8) : String :=
  let hex b :=
    let s := (BitVec.ofNat 8 b.toNat).toHex
    if s.length = 1 then "0" ++ s else s
  "0x" ++ String.join (bytes.map hex)

end Lsc3.Compile
