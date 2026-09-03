import Lsc3.Examples.Counter
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode
import Lsc3.Compile.Exec
import Lsc3.Compile.Jump

/-!
# `bytecode_ok` for `increment` (no overflow)

`read count; write (count +? 1); emit Incremented(1)`. Locals live at `localBase`;
checked-add jumps over a Panic block; a LOG1 is emitted; then STOP.
-/

namespace Lsc3.Compile.IncBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Codegen Lsc3.Compile.Exec Lsc3.Compile.Jump Counter

def addR : String := "addR0"
def addO : String := "addO1"

def incTopic : Nat :=
  if h : 0 < contract.events.length then EventDef.topic0 contract.events[0] else 0

def checkedAddInstrs : List Asm :=
  [dup2, Asm.op .ADD, dup1, swap2, Asm.op .GT,
   Asm.jumpi addR, Asm.jump addO, Asm.jumpDest addR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest addO]

def incInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push localBase, Asm.op .MSTORE,
   Asm.push localBase, Asm.op .MLOAD, Asm.push 1] ++
  checkedAddInstrs ++
  [Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push 1, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

/-- Codegen of the increment Core term (no unfolding of `increment.core` or Keccak). -/
theorem increment_genCore :
    genCore {} contract
      (Core.letOp (.load 0)
        (Core.letOp (.addChecked (.var 0) (.lit 1))
          (Core.seq (.store 0 (.var 0))
            (Core.stmtTail (.emit 0 [.lit 1]))))) =
      .ok (incInstrs, { depth := 2, labelCounter := 2 }) :=
  rfl

def revPc : Nat := 23
def okPc : Nat := 68

theorem labels_inc : layoutLabels incInstrs = [(addO, okPc), (addR, revPc)] :=
  rfl

theorem lookup_addR :
    lookupLabel (layoutLabels incInstrs) addR = .ok revPc := by
  simp [labels_inc, lookupLabel, addR, addO]

theorem lookup_addO :
    lookupLabel (layoutLabels incInstrs) addO = .ok okPc := by
  simp [labels_inc, lookupLabel, addR, addO]

theorem dup_inc : checkDuplicateLabels incInstrs = .ok () := rfl

theorem revPc_lt : revPc < jumpImmBound := by decide
theorem okPc_lt : okPc < jumpImmBound := by decide

private theorem emit_cons_ok {labels : List (String × Nat)} {i : Asm} {rest : List Asm}
    {b bs : List UInt8}
    (h1 : emitOne labels i = .ok b) (h2 : emitInstrs labels rest = .ok bs) :
    emitInstrs labels (i :: rest) = .ok (b ++ bs) := by
  rw [emitInstrs_cons, h1, h2]
  rfl

private theorem emit_bind_ok {labels : List (String × Nat)} {as bs : List Asm}
    {a b : List UInt8}
    (h1 : emitInstrs labels as = .ok a) (h2 : emitInstrs labels bs = .ok b) :
    emitInstrs labels (as ++ bs) = .ok (a ++ b) := by
  rw [emitInstrs_append, h1, h2]
  rfl

def prefixInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push localBase, Asm.op .MSTORE,
   Asm.push localBase, Asm.op .MLOAD, Asm.push 1]

def tailInstrs : List Asm :=
  [Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push 1, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

theorem incInstrs_split :
    incInstrs = prefixInstrs ++ checkedAddInstrs ++ tailInstrs :=
  rfl

def prefixBytes : List UInt8 :=
  [0x5f, 0x54, 0x60, 0x80, 0x52, 0x60, 0x80, 0x51, 0x60, 1]

def panicBytes : List UInt8 :=
  emitPush32 (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224) ++
    [0x5f, 0x52, 0x60, 0x11, 0x60, 4, 0x52, 0x60, 36, 0x5f, 0xfd]

def checkedAddBytes : List UInt8 :=
  [0x81, 0x01, 0x80, 0x91, 0x11] ++
    emitPush2 revPc ++ [Opcode.toByte .JUMPI] ++
    emitPush2 okPc ++ [Opcode.toByte .JUMP] ++
    [Opcode.toByte .JUMPDEST] ++ panicBytes ++ [Opcode.toByte .JUMPDEST]

def tailBytes : List UInt8 :=
  [0x60, 0xA0, 0x52, 0x60, 0xA0, 0x51, 0x5f, 0x55, 0x60, 1, 0x5f, 0x52] ++
    emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00]

def code : List UInt8 := prefixBytes ++ checkedAddBytes ++ tailBytes

theorem emit_prefix (labels : List (String × Nat)) :
    emitInstrs labels prefixInstrs = .ok prefixBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.push 1] = .ok (emitPush 1) := by
    simpa using emit_cons_ok (emitOne_push labels 1) t0
  have t2 : emitInstrs labels [Asm.op .MLOAD, Asm.push 1] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 1) := by
    simpa using emit_cons_ok (emitOne_op labels .MLOAD) t1
  have t3 : emitInstrs labels [Asm.push localBase, Asm.op .MLOAD, Asm.push 1] =
      .ok (emitPush localBase ++ [Opcode.toByte .MLOAD] ++ emitPush 1) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels localBase) t2
  have t4 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push localBase, Asm.op .MLOAD, Asm.push 1] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush localBase ++ [Opcode.toByte .MLOAD] ++
        emitPush 1) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t3
  have t5 : emitInstrs labels
      [Asm.push localBase, Asm.op .MSTORE, Asm.push localBase, Asm.op .MLOAD, Asm.push 1] =
      .ok (emitPush localBase ++ [Opcode.toByte .MSTORE] ++ emitPush localBase ++
        [Opcode.toByte .MLOAD] ++ emitPush 1) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels localBase) t4
  have t6 : emitInstrs labels
      [Asm.op .SLOAD, Asm.push localBase, Asm.op .MSTORE, Asm.push localBase, Asm.op .MLOAD,
        Asm.push 1] =
      .ok ([Opcode.toByte .SLOAD] ++ emitPush localBase ++ [Opcode.toByte .MSTORE] ++
        emitPush localBase ++ [Opcode.toByte .MLOAD] ++ emitPush 1) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SLOAD) t5
  have t7 := emit_cons_ok (emitOne_push labels 0) t6
  simpa [prefixInstrs, prefixBytes, emitPush_zero, emitPush_one, emitPush_0x80, localBase,
    List.append_assoc] using t7

theorem emit_panic (labels : List (String × Nat)) :
    emitInstrs labels (emitPanic 0x11) = .ok panicBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .REVERT] = .ok [Opcode.toByte .REVERT] := by
    simpa using emit_cons_ok (emitOne_op labels .REVERT) t0
  have t2 : emitInstrs labels [Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa using emit_cons_ok (emitOne_push labels 0) t1
  have t3 : emitInstrs labels [Asm.push 36, Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 36 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 36) t2
  have t4 : emitInstrs labels [Asm.op .MSTORE, Asm.push 36, Asm.push 0, Asm.op .REVERT] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush 36 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t3
  have t5 : emitInstrs labels
      [Asm.push 4, Asm.op .MSTORE, Asm.push 36, Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 4 ++ [Opcode.toByte .MSTORE] ++ emitPush 36 ++ emitPush 0 ++
        [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 4) t4
  have t6 : emitInstrs labels
      [Asm.push 0x11, Asm.push 4, Asm.op .MSTORE, Asm.push 36, Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 0x11 ++ emitPush 4 ++ [Opcode.toByte .MSTORE] ++ emitPush 36 ++
        emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0x11) t5
  have t7 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push 0x11, Asm.push 4, Asm.op .MSTORE, Asm.push 36, Asm.push 0,
        Asm.op .REVERT] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush 0x11 ++ emitPush 4 ++ [Opcode.toByte .MSTORE] ++
        emitPush 36 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t6
  have t8 : emitInstrs labels
      [Asm.push 0, Asm.op .MSTORE, Asm.push 0x11, Asm.push 4, Asm.op .MSTORE, Asm.push 36,
        Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush 0x11 ++ emitPush 4 ++
        [Opcode.toByte .MSTORE] ++ emitPush 36 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t7
  have t9 := emit_cons_ok
    (emitOne_push32 labels (selectorOf "Panic" [{ name := "code", ty := .uint256 }] * 2 ^ 224)) t8
  simpa [emitPanic, panicBytes, emitPush_zero, emitPush_four, emitPush_0x11, emitPush_thirtysix,
    List.append_assoc] using t9

theorem emit_checkedAdd (labels : List (String × Nat))
    (hR : lookupLabel labels addR = .ok revPc)
    (hO : lookupLabel labels addO = .ok okPc) :
    emitInstrs labels checkedAddInstrs = .ok checkedAddBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have tjdO : emitInstrs labels [Asm.jumpDest addO] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels addO) t0
  have hPanicOk := emit_bind_ok (emit_panic labels) tjdO
  have tJump : emitInstrs labels [Asm.jump addO] =
      .ok (emitPush2 okPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump labels addO hO okPc_lt) t0
  have tJumpi : emitInstrs labels [Asm.jumpi addR] =
      .ok (emitPush2 revPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels addR hR revPc_lt) t0
  have tjdR : emitInstrs labels [Asm.jumpDest addR] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels addR) t0
  have tGt : emitInstrs labels [Asm.op .GT] = .ok [Opcode.toByte .GT] := by
    simpa using emit_cons_ok (emitOne_op labels .GT) t0
  have tSw : emitInstrs labels [swap2] = .ok [Opcode.toByte (.SWAP ⟨1, by decide⟩)] := by
    simpa [swap2] using emit_cons_ok (emitOne_op labels (.SWAP ⟨1, by decide⟩)) t0
  have tDup1 : emitInstrs labels [dup1] = .ok [Opcode.toByte (.DUP ⟨0, by decide⟩)] := by
    simpa [dup1] using emit_cons_ok (emitOne_op labels (.DUP ⟨0, by decide⟩)) t0
  have tAdd : emitInstrs labels [Asm.op .ADD] = .ok [Opcode.toByte .ADD] := by
    simpa using emit_cons_ok (emitOne_op labels .ADD) t0
  have tDup2 : emitInstrs labels [dup2] = .ok [Opcode.toByte (.DUP ⟨1, by decide⟩)] := by
    simpa [dup2] using emit_cons_ok (emitOne_op labels (.DUP ⟨1, by decide⟩)) t0
  have h1 := emit_bind_ok tDup2 tAdd
  have h2 := emit_bind_ok h1 tDup1
  have h3 := emit_bind_ok h2 tSw
  have h4 := emit_bind_ok h3 tGt
  have h5 := emit_bind_ok h4 tJumpi
  have h6 := emit_bind_ok h5 tJump
  have h7 := emit_bind_ok h6 tjdR
  have h8 := emit_bind_ok h7 hPanicOk
  simpa [checkedAddInstrs, checkedAddBytes, panicBytes, List.append_assoc] using h8

theorem emit_tail (labels : List (String × Nat)) :
    emitInstrs labels tailInstrs = .ok tailBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .STOP] = .ok [Opcode.toByte .STOP] := by
    simpa using emit_cons_ok (emitOne_op labels .STOP) t0
  have t2 : emitInstrs labels [Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa using emit_cons_ok (emitOne_op labels (.LOG ⟨1, by decide⟩)) t1
  have t3 : emitInstrs labels [Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t2
  have t4 : emitInstrs labels
      [Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush 32 ++ emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++
        [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 32) t3
  have t5 : emitInstrs labels
      [Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push32 labels incTopic) t4
  have t6 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t5
  have t7 : emitInstrs labels
      [Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++
        emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t6
  have t8 : emitInstrs labels
      [Asm.push 1, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush 1 ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++
        emitPush 32 ++ emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++
        [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 1) t7
  have t9 : emitInstrs labels
      [Asm.op .SSTORE, Asm.push 1, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32,
        Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .SSTORE] ++ emitPush 1 ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++
        emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SSTORE) t8
  have t10 : emitInstrs labels
      [Asm.push 0, Asm.op .SSTORE, Asm.push 1, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic,
        Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte .SSTORE] ++ emitPush 1 ++ emitPush 0 ++
        [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t9
  have t11 : emitInstrs labels
      [Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.push 1, Asm.push 0, Asm.op .MSTORE,
        Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
        Asm.op .STOP] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .SSTORE] ++ emitPush 1 ++
        emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++
        emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t10
  have t12 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.push 1,
        Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .SSTORE] ++ emitPush 1 ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++
        emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t11
  have t13 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
        Asm.push 1, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .SSTORE] ++ emitPush 1 ++ emitPush 0 ++
        [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t12
  have t14 := emit_cons_ok (emitOne_push labels (localBase + 32)) t13
  simpa [tailInstrs, tailBytes, emitPush_zero, emitPush_one, emitPush_thirtyTwo, emitPush_0xA0,
    localBase, List.append_assoc] using t14

theorem emit_inc :
    emitInstrs (layoutLabels incInstrs) incInstrs = .ok code := by
  have hR := lookup_addR
  have hO := lookup_addO
  have h := emit_bind_ok
    (emit_bind_ok (emit_prefix _) (emit_checkedAdd _ hR hO))
    (emit_tail _)
  simpa [incInstrs_split, code, List.append_assoc] using h

theorem encode_inc : encode incInstrs = .ok code := by
  simp only [encode, dup_inc, bind, Except.bind]
  exact emit_inc

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

theorem memLoad_memStore (m : Mem) (off v : Nat) :
    memLoad (memStore m off v) off = wrap v := by
  have hfold :
      (List.range 32).foldl
        (fun acc i => acc * 256 + (memGet (memStore m off v) (off + i)).toNat) 0 =
      (List.range 32).foldl
        (fun acc i => acc * 256 + wrap v / 256 ^ (31 - i) % 256) 0 := by
    refine foldl_range_eq 32 _ _ ?_ 0
    intro acc i hi
    rw [memGet_memStore m off v i hi, toNat_ofNat_mod256]
  simp only [memLoad]
  rw [hfold, packWord_high (wrap v) 32 (by decide), Nat.sub_self, Nat.pow_zero,
    Nat.div_one, pow256_32]
  simp [wrap]

@[simp] theorem prefixBytes_length : prefixBytes.length = 10 := rfl

@[simp] theorem panicBytes_length : panicBytes.length = 44 := by
  simp [panicBytes, emitPush32, natToBytesBE_length]

@[simp] theorem checkedAddBytes_length : checkedAddBytes.length = 59 := by
  simp [checkedAddBytes, emitPush2, natToBytesBE_length]

theorem code_spine :
    code =
      prefixBytes ++ ([0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 revPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 okPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes)))))))) := by
  simp [code, checkedAddBytes, List.append_assoc]

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_drop10 : code.drop 10 =
    [0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 revPc ++
      (Opcode.toByte .JUMPI :: (emitPush2 okPc ++ (Opcode.toByte .JUMP ::
        (Opcode.toByte .JUMPDEST :: (panicBytes ++ (Opcode.toByte .JUMPDEST ::
          tailBytes))))))) := by
  rw [code_spine, List.drop_left' prefixBytes_length]

theorem decode_pc0 :
    decodeAt code 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  have h : code.drop 0 = 0x5f :: code.drop 1 := by simp [code, prefixBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc1 :
    decodeAt code 1 = some ({ op := .SLOAD }, 2) := by
  have h : code.drop 1 = Opcode.toByte .SLOAD :: code.drop 2 := by
    simp [code, prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem decode_pc2 :
    decodeAt code 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 4) := by
  have hdrop : code.drop 2 = 0x60 :: 0x80 :: code.drop 4 := by
    simp [code, prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 4))
  simpa [wrap, localBase] using h

theorem decode_pc4 :
    decodeAt code 4 = some ({ op := .MSTORE }, 5) := by
  have h : code.drop 4 = Opcode.toByte .MSTORE :: code.drop 5 := by
    simp [code, prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc5 :
    decodeAt code 5 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 7) := by
  have hdrop : code.drop 5 = 0x60 :: 0x80 :: code.drop 7 := by
    simp [code, prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (code.drop 7))
  simpa [wrap, localBase] using h

theorem decode_pc7 :
    decodeAt code 7 = some ({ op := .MLOAD }, 8) := by
  have h : code.drop 7 = Opcode.toByte .MLOAD :: code.drop 8 := by
    simp [code, prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc8 :
    decodeAt code 8 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 10) := by
  have hdrop : code.drop 8 = 0x60 :: 1 :: code.drop 10 := by
    simp [code, prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (code.drop 10))
  simpa [wrap] using h

theorem decode_pc10 :
    decodeAt code 10 = some ({ op := .DUP ⟨1, by decide⟩ }, 11) := by
  have h : code.drop 10 = 0x81 :: code.drop 11 := by
    rw [code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem decode_pc11 :
    decodeAt code 11 = some ({ op := .ADD }, 12) := by
  have h : code.drop 11 = 0x01 :: code.drop 12 := by
    rw [show 11 = 10 + 1 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_add_head _)

theorem decode_pc12 :
    decodeAt code 12 = some ({ op := .DUP ⟨0, by decide⟩ }, 13) := by
  have h : code.drop 12 = 0x80 :: code.drop 13 := by
    rw [show 12 = 10 + 2 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup1_head _)

theorem decode_pc13 :
    decodeAt code 13 = some ({ op := .SWAP ⟨1, by decide⟩ }, 14) := by
  have h : code.drop 13 = 0x91 :: code.drop 14 := by
    rw [show 13 = 10 + 3 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_swap2_head _)

theorem decode_pc14 :
    decodeAt code 14 = some ({ op := .GT }, 15) := by
  have h : code.drop 14 = 0x11 :: code.drop 15 := by
    rw [show 14 = 10 + 4 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_gt_head _)

theorem decode_pc15 :
    decodeAt code 15 = some ({ op := .PUSH ⟨2, by decide⟩, imm := revPc }, 18) := by
  have hdrop : code.drop 15 =
      emitPush2 revPc ++ (Opcode.toByte .JUMPI :: (emitPush2 okPc ++
        (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
          (panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))))) := by
    rw [show 15 = 10 + 5 from rfl, drop_add, code_drop10]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 revPc _)
  have hmod : revPc % 2 ^ 16 = revPc := Nat.mod_eq_of_lt (by decide)
  simpa [hmod] using h

theorem decode_pc18 :
    decodeAt code 18 = some ({ op := .JUMPI }, 19) := by
  have h : code.drop 18 = Opcode.toByte .JUMPI :: code.drop 19 := by
    rw [show 18 = 10 + 8 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jumpi_head _)

theorem decode_pc19 :
    decodeAt code 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := okPc }, 22) := by
  have hdrop : code.drop 19 =
      emitPush2 okPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))) := by
    rw [show 19 = 10 + 9 from rfl, drop_add, code_drop10]
    rw [show 9 = 5 + 4 from rfl, drop_add]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
    rw [show 4 = 3 + 1 from rfl, drop_add]
    rw [List.drop_left' (emitPush2_length revPc)]
    rw [List.drop_succ_cons]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push2 okPc _)
  have hmod : okPc % 2 ^ 16 = okPc := Nat.mod_eq_of_lt (by decide)
  simpa [hmod] using h

theorem decode_pc22 :
    decodeAt code 22 = some ({ op := .JUMP }, 23) := by
  have h : code.drop 22 = Opcode.toByte .JUMP :: code.drop 23 := by
    rw [show 22 = 10 + 12 from rfl, drop_add, code_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem code_drop68 : code.drop 68 = Opcode.toByte .JUMPDEST :: tailBytes := by
  rw [show 68 = 10 + 58 from rfl, drop_add, code_drop10]
  rw [show 58 = 5 + 53 from rfl, drop_add]
  rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  rw [show 53 = 3 + 50 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length revPc)]
  rw [show 50 = 49 + 1 from rfl, List.drop_succ_cons]
  rw [show 49 = 3 + 46 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length okPc)]
  rw [show 46 = 45 + 1 from rfl, List.drop_succ_cons]
  rw [show 45 = 44 + 1 from rfl, List.drop_succ_cons]
  rw [List.drop_left' panicBytes_length]

theorem decode_pc68 :
    decodeAt code 68 = some ({ op := .JUMPDEST }, 69) := by
  exact decodeAt_of_drop code_drop68 (decodeAt_jumpdest_head _)

theorem code_drop69 : code.drop 69 = tailBytes := by
  rw [show 69 = 68 + 1 from rfl, drop_add, code_drop68]
  rfl

theorem tailBytes_drop12 :
    tailBytes.drop 12 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] :=
  rfl

theorem code_drop81 : code.drop 81 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] := by
  rw [show 81 = 69 + 12 from rfl, drop_add, code_drop69, tailBytes_drop12]

theorem decode_pc69 :
    decodeAt code 69 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 71) := by
  have hdrop : code.drop 69 = 0x60 :: 0xA0 :: code.drop 71 := by
    rw [code_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 71))
  simpa [wrap, localBase] using h

theorem decode_pc71 :
    decodeAt code 71 = some ({ op := .MSTORE }, 72) := by
  have h : code.drop 71 = Opcode.toByte .MSTORE :: code.drop 72 := by
    rw [show 71 = 69 + 2 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc72 :
    decodeAt code 72 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 74) := by
  have hdrop : code.drop 72 = 0x60 :: 0xA0 :: code.drop 74 := by
    rw [show 72 = 69 + 3 from rfl, drop_add, code_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (code.drop 74))
  simpa [wrap, localBase] using h

theorem decode_pc74 :
    decodeAt code 74 = some ({ op := .MLOAD }, 75) := by
  have h : code.drop 74 = Opcode.toByte .MLOAD :: code.drop 75 := by
    rw [show 74 = 69 + 5 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem decode_pc75 :
    decodeAt code 75 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 76) := by
  have h : code.drop 75 = 0x5f :: code.drop 76 := by
    rw [show 75 = 69 + 6 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc76 :
    decodeAt code 76 = some ({ op := .SSTORE }, 77) := by
  have h : code.drop 76 = Opcode.toByte .SSTORE :: code.drop 77 := by
    rw [show 76 = 69 + 7 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_sstore_head _)

theorem decode_pc77 :
    decodeAt code 77 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 79) := by
  have hdrop : code.drop 77 = 0x60 :: 1 :: code.drop 79 := by
    rw [show 77 = 69 + 8 from rfl, drop_add, code_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (code.drop 79))
  simpa [wrap] using h

theorem decode_pc79 :
    decodeAt code 79 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 80) := by
  have h : code.drop 79 = 0x5f :: code.drop 80 := by
    rw [show 79 = 69 + 10 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc80 :
    decodeAt code 80 = some ({ op := .MSTORE }, 81) := by
  have h : code.drop 80 = Opcode.toByte .MSTORE :: code.drop 81 := by
    rw [show 80 = 69 + 11 from rfl, drop_add, code_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem decode_pc81 :
    decodeAt code 81 = some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 114) := by
  have h := decodeAt_of_drop code_drop81 (decodeAt_push32 incTopic _)
  simpa using h

theorem decode_pc114 :
    decodeAt code 114 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 116) := by
  have h114 : code.drop 114 = [0x60, 0x20, 0x5f, 0xa1, 0x00] := by
    rw [show 114 = 81 + 33 from rfl, drop_add, code_drop81]
    rw [List.drop_left' (emitPush32_length incTopic)]
  have h116 : code.drop 116 = [0x5f, 0xa1, 0x00] := by
    rw [show 116 = 81 + 35 from rfl, drop_add, code_drop81]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  have hdrop : code.drop 114 = 0x60 :: 0x20 :: code.drop 116 := by
    rw [h114, h116]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x20 : UInt8) (code.drop 116))
  simpa [wrap] using h

theorem decode_pc116 :
    decodeAt code 116 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 117) := by
  have h : code.drop 116 = 0x5f :: code.drop 117 := by
    rw [show 116 = 81 + 35 from rfl, drop_add, code_drop81]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc117 :
    decodeAt code 117 = some ({ op := .LOG ⟨1, by decide⟩ }, 118) := by
  have h : code.drop 117 = 0xa1 :: code.drop 118 := by
    rw [show 117 = 81 + 36 from rfl, drop_add, code_drop81]
    rw [show 36 = 33 + 3 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_log1_head _)

theorem decode_pc118 :
    decodeAt code 118 = some ({ op := .STOP }, 119) := by
  have h : code.drop 118 = 0x00 :: code.drop 119 := by
    rw [show 118 = 81 + 37 from rfl, drop_add, code_drop81]
    rw [show 37 = 33 + 4 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_stop_head _)

theorem decode_suffix (pre : List UInt8) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt code pc = some (instr, next0)) :
    decodeAt (pre ++ code) (pre.length + pc) = some (instr, pre.length + next0) := by
  rw [decodeAt_append, hd]
  simp [Nat.add_comm]

theorem isJumpDest_ok : isJumpDest code okPc = true := by
  simpa [okPc] using isJumpDest_of_decode decode_pc68

def env : Env :=
  { code := code, calldata := [], address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

abbrev mem1 (n : Nat) : Mem := memStore (st0 n).mem localBase n

abbrev mem2 (n : Nat) (v : Nat) : Mem := memStore (mem1 n) (localBase + 32) v

abbrev mem3 (n : Nat) (v : Nat) : Mem := memStore (mem2 n v) 0 1

abbrev stor1 (n : Nat) : EVM.Storage := fun k => if k = 0 then n + 1 else (st0 n).storage k

abbrev log1 (n v : Nat) : List Log :=
  [{ topics := [wrap incTopic]
     data := (List.range 32).map fun i => memGet (mem3 n v) (0 + i) }]

/-- No-overflow `increment` body: STOP with storage slot 0 equal to `n + 1`. -/
theorem incBody_hit (n : Nat) (h : n + 1 < wordBound) :
    (match run 48 env (st0 n) with
    | some (Halt.stop, s) => s.storage 0 = n + 1
    | _ => False) := by
  have hn : n < wordBound := Nat.lt_of_succ_lt h
  have hwrap : wrap n = n := Nat.mod_eq_of_lt hn
  have hadd : addW (wrap n) 1 = n + 1 := by rw [hwrap]; exact addW_succ_of_lt h
  have hval : wrap (addW (wrap n) 1) = n + 1 := by rw [hadd]; exact Nat.mod_eq_of_lt h
  have s0 : step env (st0 n) =
      StepResult.next { st0 n with stack := [0], pc := 1 } := by
    have hs := step_push env (st0 n) 0 decode_pc0
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 47 env (st0 n) _ s0]
  have s1 : step env { st0 n with stack := [0], pc := 1 } =
      StepResult.next { st0 n with stack := [n], pc := 2 } := by
    have hs := step_sload env { st0 n with stack := [0], pc := 1 } 0 []
      decode_pc1 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 46 env _ _ s1]
  have s2 : step env { st0 n with stack := [n], pc := 2 } =
      StepResult.next { st0 n with stack := [localBase, n], pc := 4 } := by
    have hs := step_push env { st0 n with stack := [n], pc := 2 } localBase decode_pc2
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 45 env _ _ s2]
  have s4 : step env { st0 n with stack := [localBase, n], pc := 4 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 5 } :=
    step_mstore env { st0 n with stack := [localBase, n], pc := 4 } localBase n []
      decode_pc4 rfl
  rw [run_of_next 44 env _ _ s4]
  have s5 : step env { st0 n with mem := mem1 n, stack := [], pc := 5 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 7 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [], pc := 5 }
      localBase decode_pc5 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 43 env _ _ s5]
  have s7 : step env { st0 n with mem := mem1 n, stack := [localBase], pc := 7 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 } := by
    have hs := step_mload env { st0 n with mem := mem1 n, stack := [localBase], pc := 7 }
      localBase [] decode_pc7 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [memLoad_memStore] using hs
  rw [run_of_next 42 env _ _ s7]
  have s8 : step env { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 10 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [wrap n], pc := 8 }
      1 decode_pc8 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 41 env _ _ s8]
  have s10 : step env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 10 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 11 } := by
    have hs := step_dup2 env { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 10 }
      1 (wrap n) [] decode_pc10 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 40 env _ _ s10]
  have s11 : step env { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 11 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 12 } := by
    have hs := step_add env { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 11 }
      (wrap n) 1 [wrap n] decode_pc11 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 39 env _ _ s11]
  have s12 : step env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 12 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 13 } := by
    have hs := step_dup1 env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 12 }
      (addW (wrap n) 1) [wrap n] decode_pc12 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 38 env _ _ s12]
  have s13 : step env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 13 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 14 } := by
    have hs := step_swap2 env
      { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 13 }
      (addW (wrap n) 1) (addW (wrap n) 1) (wrap n) [] decode_pc13 rfl
    simpa using hs
  rw [run_of_next 37 env _ _ s13]
  have s14 : step env { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 14 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 15 } := by
    have hs := step_gt env
      { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 14 }
      (wrap n) (addW (wrap n) 1) [addW (wrap n) 1] decode_pc14 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) 1) = 0 := by
      rw [hwrap]; exact gtW_add_no_overflow h
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 36 env _ _ s14]
  have s15 : step env { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 15 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [revPc, 0, addW (wrap n) 1], pc := 18 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 15 }
      revPc decode_pc15 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 35 env _ _ s15]
  have s18 : step env { st0 n with mem := mem1 n, stack := [revPc, 0, addW (wrap n) 1], pc := 18 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 19 } := by
    have hs := step_jumpi_zero env
      { st0 n with mem := mem1 n, stack := [revPc, 0, addW (wrap n) 1], pc := 18 }
      revPc [addW (wrap n) 1] decode_pc18 rfl
    simpa using hs
  rw [run_of_next 34 env _ _ s18]
  have s19 : step env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 19 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [okPc, addW (wrap n) 1], pc := 22 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 19 }
      okPc decode_pc19 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 33 env _ _ s19]
  have s22 : step env { st0 n with mem := mem1 n, stack := [okPc, addW (wrap n) 1], pc := 22 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := okPc } := by
    have hs := step_jump env { st0 n with mem := mem1 n, stack := [okPc, addW (wrap n) 1], pc := 22 }
      okPc [addW (wrap n) 1] decode_pc22 rfl isJumpDest_ok
    simpa [env] using hs
  rw [run_of_next 32 env _ _ s22]
  have s68 : step env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := okPc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 69 } := by
    have hdec : decodeAt env.code okPc = some ({ op := .JUMPDEST }, 69) := by
      simpa [env, okPc] using decode_pc68
    exact step_jumpdest env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := okPc } hdec
  rw [run_of_next 31 env _ _ s68]
  have s69 : step env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 69 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 71 } := by
    have hs := step_push env { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 69 }
      (localBase + 32) decode_pc69 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 30 env _ _ s69]
  have s71 : step env { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 71 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 72 } :=
    step_mstore env { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 71 }
      (localBase + 32) (addW (wrap n) 1) [] decode_pc71 rfl
  rw [run_of_next 29 env _ _ s71]
  have s72 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 72 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 74 } := by
    have hs := step_push env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 72 }
      (localBase + 32) decode_pc72 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 28 env _ _ s72]
  have s74 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 74 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 75 } := by
    have hs := step_mload env
      { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 74 }
      (localBase + 32) [] decode_pc74 rfl (list_length_lt_1024 (k := 0) rfl)
    simp only [memLoad_memStore] at hs
    rw [hval] at hs
    exact hs
  rw [run_of_next 27 env _ _ s74]
  have s75 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 75 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 76 } := by
    have hs := step_push env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 75 }
      0 decode_pc75 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 26 env _ _ s75]
  have s76 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 76 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 77 } :=
    step_sstore env { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 76 }
      0 (n + 1) [] decode_pc76 rfl
  rw [run_of_next 25 env _ _ s76]
  have s77 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 77 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 79 } := by
    have hs := step_push env
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 77 }
      1 decode_pc77 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 24 env _ _ s77]
  have s79 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 79 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 80 } := by
    have hs := step_push env
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 79 }
      0 decode_pc79 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 23 env _ _ s79]
  have s80 : step env { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 80 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 81 } :=
    step_mstore env
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 80 }
      0 1 [] decode_pc80 rfl
  rw [run_of_next 22 env _ _ s80]
  have s81 : step env { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 81 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 114 } := by
    have hs := step_push env
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 81 }
      (wrap incTopic) decode_pc81 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 21 env _ _ s81]
  have s114 : step env { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 114 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 116 } := by
    have hs := step_push env
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 114 }
      32 decode_pc114 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 20 env _ _ s114]
  have s116 : step env { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 116 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 117 } := by
    have hs := step_push env
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 116 }
      0 decode_pc116 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 19 env _ _ s116]
  have s117 : step env { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 117 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 118 } := by
    have hs := step_log1 env
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 117 }
      0 32 (wrap incTopic) [] decode_pc117 rfl
    simpa [log1] using hs
  rw [run_of_next 18 env _ _ s117]
  have s118 : step env { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 118 } =
      StepResult.halt Halt.stop { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 118 } :=
    step_stop env _ decode_pc118
  rw [run_of_halt 17 env _ _ _ s118]
  simp [stor1]

end Lsc3.Compile.IncBody
