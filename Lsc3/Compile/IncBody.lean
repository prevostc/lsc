import Lsc3.Examples.Counter
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode

/-!
# `bytecode_ok` for `increment` (no overflow)

`read count; write (count +? 1); emit Incremented(1)`. Locals live at `localBase`;
checked-add jumps over a Panic block; a LOG1 is emitted; then STOP.
-/

namespace Lsc3.Compile.IncBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Codegen Counter

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

end Lsc3.Compile.IncBody
