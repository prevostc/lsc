import LscV2.Compile.Bytecode.Instr
import EvmYul.EVM.Instr
import EvmYul.Operations

namespace LscV2.Compile.Bytecode

open EvmYul Operation EvmYul.EVM
open Instr

private def pushWidth (n : Nat) : Nat :=
  if n == 0 then 0 else Nat.div (Nat.log2 n) 8 + 1

private def pushOp (width : Nat) : Operation .EVM :=
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

private def natToBigEndianBytes (n : Nat) (width : Nat) : ByteArray :=
  ByteArray.mk ((List.range width).map fun i =>
    let shift := 8 * (width - 1 - i)
    UInt8.ofNat ((n / (2 ^ shift)) % 256)).toArray

private def lookupLabel (labels : List (String × Nat)) (lbl : String) : Nat :=
  labels.find? (·.1 == lbl) |>.map (·.2) |>.getD 0

private def labelPushSize (labels : List (String × Nat)) (lbl : String) : Nat :=
  1 + pushWidth (lookupLabel labels lbl)

private partial def instrByteSize (labels : List (String × Nat)) (i : Instr) : Nat :=
  match i with
  | Instr.op _ => 1
  | .push n => 1 + pushWidth n
  | .pushLabel lbl => labelPushSize labels lbl
  | .jump lbl => labelPushSize labels lbl + 1
  | .jumpi lbl => labelPushSize labels lbl + 1
  | .jumpDest _ => 1

private partial def layoutLabels (instrs : List Instr) (sizeHints : List (String × Nat)) :
    List (String × Nat) :=
  let rec go (pc : Nat) (rest : List Instr) (acc : List (String × Nat)) :
      List (String × Nat) :=
    match rest with
    | [] => acc
    | .jumpDest lbl :: tail =>
      go (pc + 1) tail ((lbl, pc) :: acc)
    | i :: tail =>
      go (pc + instrByteSize sizeHints i) tail acc
  go 0 instrs []

private def fixpointLabels (instrs : List Instr) : List (String × Nat) :=
  let rec iter (hints : List (String × Nat)) (fuel : Nat) :=
    if fuel = 0 then hints else
    let next := layoutLabels instrs hints
    if next == hints then next else iter next (fuel - 1)
  iter [] 12

private def emitPush (n : Nat) : ByteArray :=
  let width := pushWidth n
  let header := ByteArray.mk #[serializeInstr (pushOp width)]
  header ++ natToBigEndianBytes n width

private def emitPushLabel (labels : List (String × Nat)) (lbl : String) : ByteArray :=
  emitPush (lookupLabel labels lbl)

private partial def emitInstrs (labels : List (String × Nat)) : List Instr → ByteArray
  | [] => ByteArray.empty
  | i :: rest =>
    let head := match i with
      | Instr.op evmOp =>
        if Operation.isPush evmOp then panic! "internal: use Instr.push"
        else ByteArray.mk #[serializeInstr evmOp]
      | .push n => emitPush n
      | .pushLabel lbl => emitPushLabel labels lbl
      | .jump lbl =>
        emitPushLabel labels lbl ++ ByteArray.mk #[serializeInstr JUMP]
      | .jumpi lbl =>
        emitPushLabel labels lbl ++ ByteArray.mk #[serializeInstr JUMPI]
      | .jumpDest _ => ByteArray.mk #[serializeInstr JUMPDEST]
    head ++ emitInstrs labels rest

def encode (instrs : List Instr) : Except String ByteArray :=
  .ok (emitInstrs (fixpointLabels instrs) instrs)

private def byteHex (b : UInt8) : String :=
  let s := (BitVec.ofNat 8 b.toNat).toHex
  if s.length == 1 then "0" ++ s else s

def toHex (bytes : ByteArray) : String :=
  "0x" ++ bytes.foldl (init := "") fun acc b => acc ++ byteHex b

end LscV2.Compile.Bytecode
