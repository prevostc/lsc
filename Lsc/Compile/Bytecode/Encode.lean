import Lsc.Compile.Bytecode.Instr
import EvmYul.EVM.Instr
import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open EvmYul Operation EvmYul.EVM
open Instr

/-- Number of immediate bytes used by the canonical encoding of `PUSH n`. -/
def pushWidth (n : Nat) : Nat :=
  if n == 0 then 0 else Nat.div (Nat.log2 n) 8 + 1

def pushOp (width : Nat) : Operation .EVM :=
  match width with
  | 0 => PUSH0
  | 1 => PUSH1
  | 2 => PUSH2
  | 3 => PUSH3
  | 4 => PUSH4
  | 5 => PUSH5
  | 6 => PUSH6
  | 7 => PUSH7
  | 8 => PUSH8
  | 9 => PUSH9
  | 10 => PUSH10
  | 11 => PUSH11
  | 12 => PUSH12
  | 13 => PUSH13
  | 14 => PUSH14
  | 15 => PUSH15
  | 16 => PUSH16
  | 17 => PUSH17
  | 18 => PUSH18
  | 19 => PUSH19
  | 20 => PUSH20
  | 21 => PUSH21
  | 22 => PUSH22
  | 23 => PUSH23
  | 24 => PUSH24
  | 25 => PUSH25
  | 26 => PUSH26
  | 27 => PUSH27
  | 28 => PUSH28
  | 29 => PUSH29
  | 30 => PUSH30
  | 31 => PUSH31
  | _ => PUSH32

def natToLittleEndianBytes (n : Nat) : Nat → List UInt8
  | 0 => []
  | width + 1 =>
      UInt8.ofNat (n % 256) :: natToLittleEndianBytes (n / 256) width

def natToBigEndianBytes (n : Nat) (width : Nat) : ByteArray :=
  ByteArray.mk (natToLittleEndianBytes n width).reverse.toArray

def jumpDestLabelsRaw (instrs : List Instr) : List String :=
  instrs.filterMap fun
    | .jumpDest lbl => some lbl
    | _ => none

def checkDuplicateLabels (instrs : List Instr) : Except String Unit := do
  let labels := jumpDestLabelsRaw instrs
  if labels.Nodup then
    .ok ()
  else
    let dup? := labels.find? fun lbl => labels.count lbl > 1
    match dup? with
    | none => .error "duplicate jump label"
    | some lbl => .error s!"duplicate jump label: {lbl}"

def lookupLabel (labels : List (String × Nat)) (lbl : String) : Except String Nat := do
  let hits := labels.filter (·.1 == lbl)
  match hits with
  | [] => .error s!"unknown jump label: {lbl}"
  | (lbl', pc) :: rest =>
    if rest.any (·.1 == lbl') then
      .error s!"duplicate jump label in layout: {lbl}"
    else
      .ok pc

/-- Encoded byte length of one structured instruction. Label references always use PUSH32, so
their widths are independent of target PCs. The labels argument remains for API compatibility. -/
def instrByteSize (_labels : List (String × Nat)) (i : Instr) : Nat :=
  match i with
  | Instr.op _ => 1
  | .push n => 1 + pushWidth n
  | .push32 _ => 33
  | .pushLabel _ => 33
  | .jump _ => 34
  | .jumpi _ => 34
  | .jumpDest _ => 1

def instrsByteSize (instrs : List Instr) : Nat :=
  (instrs.map (instrByteSize [])).sum

def layoutLabelsFrom (sizeHints : List (String × Nat)) :
    Nat → List Instr → List (String × Nat) → List (String × Nat)
  | _, [], acc => acc
  | pc, .jumpDest lbl :: tail, acc =>
      layoutLabelsFrom sizeHints (pc + 1) tail ((lbl, pc) :: acc)
  | pc, i :: tail, acc =>
      layoutLabelsFrom sizeHints (pc + instrByteSize sizeHints i) tail acc

def layoutLabels (instrs : List Instr) (sizeHints : List (String × Nat)) :
    List (String × Nat) :=
  layoutLabelsFrom sizeHints 0 instrs []

/-- Compatibility wrapper: fixed-width label references make one layout pass exact. -/
def fixpointLabelsFrom (instrs : List Instr) :
    List (String × Nat) → Nat → List (String × Nat)
  | _, _ => layoutLabels instrs []

/-- Exact production label layout, computed in one deterministic pass. -/
def fixpointLabels (instrs : List Instr) : List (String × Nat) :=
  layoutLabels instrs []

def emitPush (n : Nat) : ByteArray :=
  let width := pushWidth n
  let header := ByteArray.mk #[serializeInstr (pushOp width)]
  header ++ natToBigEndianBytes n width

def emitPush32 (n : Nat) : ByteArray :=
  ByteArray.mk #[serializeInstr PUSH32] ++ natToBigEndianBytes n 32

def emitPushLabel (labels : List (String × Nat)) (lbl : String) : Except String ByteArray := do
  let pc ← lookupLabel labels lbl
  .ok (emitPush32 pc)

def emitInstrs (labels : List (String × Nat)) : List Instr → Except String ByteArray
  | [] => .ok ByteArray.empty
  | i :: rest => do
    let head ← match i with
      | Instr.op evmOp =>
        if Operation.isPush evmOp then
          .error "internal: use Instr.push"
        else
          .ok (ByteArray.mk #[serializeInstr evmOp])
      | .push n => .ok (emitPush n)
      | .push32 n => .ok (emitPush32 n)
      | .pushLabel lbl => emitPushLabel labels lbl
      | .jump lbl => do
        let push ← emitPushLabel labels lbl
        .ok (push ++ ByteArray.mk #[serializeInstr JUMP])
      | .jumpi lbl => do
        let push ← emitPushLabel labels lbl
        .ok (push ++ ByteArray.mk #[serializeInstr JUMPI])
      | .jumpDest _ => .ok (ByteArray.mk #[serializeInstr JUMPDEST])
    let tail ← emitInstrs labels rest
    .ok (head ++ tail)

/-- Resolve symbolic control-flow instructions to the label-free instruction stream represented
by `emitInstrs`. This is a proof-facing view of the production encoder, not another VM. -/
def resolveInstr (labels : List (String × Nat)) : Instr → Except String (List Instr)
  | .op evmOp => .ok [.op evmOp]
  | .push n => .ok [.push n]
  | .push32 n => .ok [.push32 n]
  | .pushLabel lbl => do
      let pc ← lookupLabel labels lbl
      .ok [.push32 pc]
  | .jump lbl => do
      let pc ← lookupLabel labels lbl
      .ok [.push32 pc, .op JUMP]
  | .jumpi lbl => do
      let pc ← lookupLabel labels lbl
      .ok [.push32 pc, .op JUMPI]
  | .jumpDest _ => .ok [.op JUMPDEST]

def resolveInstrs (labels : List (String × Nat)) : List Instr → Except String (List Instr)
  | [] => .ok []
  | instr :: rest => do
      let head ← resolveInstr labels instr
      .ok (head ++ (← resolveInstrs labels rest))

def jumpDestLabelList (instrs : List Instr) : List String :=
  jumpDestLabelsRaw instrs

def encode (instrs : List Instr) : Except String ByteArray := do
  checkDuplicateLabels instrs
  let labels := layoutLabels instrs []
  emitInstrs labels instrs

private def byteHex (b : UInt8) : String :=
  let s := (BitVec.ofNat 8 b.toNat).toHex
  if s.length == 1 then "0" ++ s else s

def toHex (bytes : ByteArray) : String :=
  "0x" ++ bytes.foldl (init := "") fun acc b => acc ++ byteHex b

end Lsc.Compile.Bytecode
