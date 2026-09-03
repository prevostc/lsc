import Lsc3.Examples.Counter
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode
import Lsc3.Compile.Contract
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# Codegen of `incrementBy` (calldata argument + require + checked add)

`loadParams 1`, `require n ≠ 0` (Error.Zero), load slot 0, checked-add `n`,
store, emit `Incremented(n)`, STOP. Jump labels are those of
`Ctx.forFunction {} "incrementBy" 1`.
-/

namespace Lsc3.Compile.IncByBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Codegen Counter

def incByFn : FnDef where
  name := "incrementBy"
  decl := .anonymous
  kind := .tx
  params := [{ name := "n", ty := .uint256 }]
  ret := .unit
  core := .seq (.require (.ne (.var 0) (.lit 0)) 0 [])
    (.letOp (.load 0)
      (.letOp (.addChecked (.var 0) (.var 1))
        (.seq (.store 0 (.var 0))
          (.stmtTail (.emit 0 [.var 2])))))

theorem incByFn_core :
    incByFn.core =
      Core.seq (.require (.ne (.var 0) (.lit 0)) 0 [])
        (Core.letOp (.load 0)
          (Core.letOp (.addChecked (.var 0) (.var 1))
            (Core.seq (.store 0 (.var 0))
              (Core.stmtTail (.emit 0 [.var 2]))))) :=
  rfl

def reqR : String := "incrementBy.reqR0"
def reqO : String := "incrementBy.reqO1"
def addR : String := "incrementBy.addR2"
def addO : String := "incrementBy.addO3"

def zeroSel : Nat :=
  if h : 0 < contract.errors.length then ErrorDef.selector contract.errors[0] else 0

def incTopic : Nat :=
  if h : 0 < contract.events.length then EventDef.topic0 contract.events[0] else 0

def loadParamInstrs : List Asm :=
  [Asm.push 4, Asm.op .CALLDATALOAD, Asm.push localBase, Asm.op .MSTORE]

def requireInstrs : List Asm :=
  [Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .EQ, Asm.op .ISZERO,
   Asm.op .ISZERO, Asm.jumpi reqR, Asm.jump reqO, Asm.jumpDest reqR] ++
  emitRevert zeroSel ++
  [Asm.jumpDest reqO]

def prefixInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD]

def checkedAddInstrs : List Asm :=
  [dup2, Asm.op .ADD, dup1, swap2, Asm.op .GT,
   Asm.jumpi addR, Asm.jump addO, Asm.jumpDest addR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest addO]

def tailInstrs : List Asm :=
  [Asm.push (localBase + 64), Asm.op .MSTORE,
   Asm.push (localBase + 64), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

def incByInstrs : List Asm :=
  loadParamInstrs ++ requireInstrs ++ prefixInstrs ++ checkedAddInstrs ++ tailInstrs

set_option maxRecDepth 20000 in
theorem incrementBy_genFunction :
    genFunction contract incByFn {} =
      .ok (incByInstrs, { depth := 0, labelCounter := 4, labelPrefix := "" }) :=
  rfl

def reqRPc : Nat := 21
def reqOPc : Nat := 61
def addRPc : Nat := 86
def addOPc : Nat := 131

set_option maxRecDepth 20000 in
theorem labels_incBy :
    layoutLabels incByInstrs =
      [(addO, addOPc), (addR, addRPc), (reqO, reqOPc), (reqR, reqRPc)] :=
  rfl

theorem lookup_reqR :
    lookupLabel (layoutLabels incByInstrs) reqR = .ok reqRPc := by
  simp [labels_incBy, lookupLabel, addO, addR, reqO, reqR]

theorem lookup_reqO :
    lookupLabel (layoutLabels incByInstrs) reqO = .ok reqOPc := by
  simp [labels_incBy, lookupLabel, addO, addR, reqO, reqR]

theorem lookup_addR :
    lookupLabel (layoutLabels incByInstrs) addR = .ok addRPc := by
  simp [labels_incBy, lookupLabel, addO, addR, reqO, reqR]

theorem lookup_addO :
    lookupLabel (layoutLabels incByInstrs) addO = .ok addOPc := by
  simp [labels_incBy, lookupLabel, addO, addR, reqO, reqR]

theorem dup_incBy : checkDuplicateLabels incByInstrs = .ok () := rfl

theorem reqRPc_lt : reqRPc < jumpImmBound := by decide
theorem reqOPc_lt : reqOPc < jumpImmBound := by decide
theorem addRPc_lt : addRPc < jumpImmBound := by decide
theorem addOPc_lt : addOPc < jumpImmBound := by decide
theorem reqRPc_mod : reqRPc % 2 ^ 16 = reqRPc := Nat.mod_eq_of_lt (by decide)
theorem reqOPc_mod : reqOPc % 2 ^ 16 = reqOPc := Nat.mod_eq_of_lt (by decide)
theorem addRPc_mod : addRPc % 2 ^ 16 = addRPc := Nat.mod_eq_of_lt (by decide)
theorem addOPc_mod : addOPc % 2 ^ 16 = addOPc := Nat.mod_eq_of_lt (by decide)

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

def loadParamBytes : List UInt8 :=
  [0x60, 4, Opcode.toByte .CALLDATALOAD, 0x60, 0x80, Opcode.toByte .MSTORE]

def zeroRevertBytes : List UInt8 :=
  emitPush32 (zeroSel * 2 ^ 224) ++ [0x5f, 0x52, 0x60, 4, 0x5f, 0xfd]

def requireHeadBytes : List UInt8 :=
  [0x60, 0x80, Opcode.toByte .MLOAD, 0x5f, Opcode.toByte .EQ, Opcode.toByte .ISZERO,
    Opcode.toByte .ISZERO]

/-- Right-associated so `drop_left'` applies without unfolding `zeroSel`. -/
def requireBytes : List UInt8 :=
  requireHeadBytes ++ (emitPush2 reqRPc ++ ([Opcode.toByte .JUMPI] ++
    (emitPush2 reqOPc ++ ([Opcode.toByte .JUMP] ++ ([Opcode.toByte .JUMPDEST] ++
      (zeroRevertBytes ++ [Opcode.toByte .JUMPDEST]))))))

def prefixBytes : List UInt8 :=
  [0x5f, Opcode.toByte .SLOAD, 0x60, 0xA0, Opcode.toByte .MSTORE,
    0x60, 0xA0, Opcode.toByte .MLOAD, 0x60, 0x80, Opcode.toByte .MLOAD]

def checkedAddBytes : List UInt8 :=
  [0x81, 0x01, 0x80, 0x91, 0x11] ++
    emitPush2 addRPc ++ [Opcode.toByte .JUMPI] ++
    emitPush2 addOPc ++ [Opcode.toByte .JUMP] ++
    [Opcode.toByte .JUMPDEST] ++ IncBody.panicBytes ++ [Opcode.toByte .JUMPDEST]

def tailBytes : List UInt8 :=
  [0x60, 0xC0, Opcode.toByte .MSTORE, 0x60, 0xC0, Opcode.toByte .MLOAD, 0x5f, Opcode.toByte .SSTORE,
    0x60, 0x80, Opcode.toByte .MLOAD, 0x5f, Opcode.toByte .MSTORE] ++
    emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00]

def code : List UInt8 :=
  loadParamBytes ++ requireBytes ++ prefixBytes ++ checkedAddBytes ++ tailBytes

theorem emit_loadParam (labels : List (String × Nat)) :
    emitInstrs labels loadParamInstrs = .ok loadParamBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .MSTORE] = .ok [Opcode.toByte .MSTORE] := by
    simpa using emit_cons_ok (emitOne_op labels .MSTORE) t0
  have t2 : emitInstrs labels [Asm.push localBase, Asm.op .MSTORE] =
      .ok (emitPush localBase ++ [Opcode.toByte .MSTORE]) := by
    simpa using emit_cons_ok (emitOne_push labels localBase) t1
  have t3 : emitInstrs labels [Asm.op .CALLDATALOAD, Asm.push localBase, Asm.op .MSTORE] =
      .ok ([Opcode.toByte .CALLDATALOAD] ++ emitPush localBase ++ [Opcode.toByte .MSTORE]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .CALLDATALOAD) t2
  have t4 := emit_cons_ok (emitOne_push labels 4) t3
  simpa [loadParamInstrs, loadParamBytes, emitPush_four, emitPush_0x80, localBase,
    List.append_assoc] using t4

theorem emit_zeroRevert (labels : List (String × Nat)) :
    emitInstrs labels (emitRevert zeroSel) = .ok zeroRevertBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .REVERT] = .ok [Opcode.toByte .REVERT] := by
    simpa using emit_cons_ok (emitOne_op labels .REVERT) t0
  have t2 : emitInstrs labels [Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa using emit_cons_ok (emitOne_push labels 0) t1
  have t3 : emitInstrs labels [Asm.push 4, Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 4 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 4) t2
  have t4 : emitInstrs labels [Asm.op .MSTORE, Asm.push 4, Asm.push 0, Asm.op .REVERT] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush 4 ++ emitPush 0 ++ [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t3
  have t5 : emitInstrs labels
      [Asm.push 0, Asm.op .MSTORE, Asm.push 4, Asm.push 0, Asm.op .REVERT] =
      .ok (emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush 4 ++ emitPush 0 ++
        [Opcode.toByte .REVERT]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t4
  have t6 := emit_cons_ok (emitOne_push32 labels (zeroSel * 2 ^ 224)) t5
  simpa [emitRevert, zeroRevertBytes, emitPush_zero, emitPush_four, List.append_assoc] using t6

theorem emit_require (labels : List (String × Nat))
    (hR : lookupLabel labels reqR = .ok reqRPc)
    (hO : lookupLabel labels reqO = .ok reqOPc) :
    emitInstrs labels requireInstrs = .ok requireBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have tjdO : emitInstrs labels [Asm.jumpDest reqO] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels reqO) t0
  have hRevOk := emit_bind_ok (emit_zeroRevert labels) tjdO
  have tjdR : emitInstrs labels [Asm.jumpDest reqR] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels reqR) t0
  have tJump : emitInstrs labels [Asm.jump reqO] =
      .ok (emitPush2 reqOPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump labels reqO hO reqOPc_lt) t0
  have tJumpi : emitInstrs labels [Asm.jumpi reqR] =
      .ok (emitPush2 reqRPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels reqR hR reqRPc_lt) t0
  have tIz : emitInstrs labels [Asm.op .ISZERO] = .ok [Opcode.toByte .ISZERO] := by
    simpa using emit_cons_ok (emitOne_op labels .ISZERO) t0
  have tEq : emitInstrs labels [Asm.op .EQ] = .ok [Opcode.toByte .EQ] := by
    simpa using emit_cons_ok (emitOne_op labels .EQ) t0
  have tMLoad : emitInstrs labels [Asm.op .MLOAD] = .ok [Opcode.toByte .MLOAD] := by
    simpa using emit_cons_ok (emitOne_op labels .MLOAD) t0
  have h1 := emit_bind_ok tMLoad (emit_cons_ok (emitOne_push labels 0) tEq)
  have h2 := emit_bind_ok (emit_cons_ok (emitOne_push labels localBase) h1)
    (emit_bind_ok tIz (emit_bind_ok tIz (emit_bind_ok tJumpi (emit_bind_ok tJump
      (emit_bind_ok tjdR hRevOk)))))
  simpa [requireInstrs, requireBytes, emitPush_zero, emitPush_0x80, localBase,
    List.append_assoc] using h2

theorem emit_prefix (labels : List (String × Nat)) :
    emitInstrs labels prefixInstrs = .ok prefixBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .MLOAD] = .ok [Opcode.toByte .MLOAD] := by
    simpa using emit_cons_ok (emitOne_op labels .MLOAD) t0
  have t2 : emitInstrs labels [Asm.push localBase, Asm.op .MLOAD] =
      .ok (emitPush localBase ++ [Opcode.toByte .MLOAD]) := by
    simpa using emit_cons_ok (emitOne_push labels localBase) t1
  have t3 : emitInstrs labels [Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush localBase ++ [Opcode.toByte .MLOAD]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t2
  have t4 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++ emitPush localBase ++
        [Opcode.toByte .MLOAD]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t3
  have t5 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++
        emitPush localBase ++ [Opcode.toByte .MLOAD]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t4
  have t6 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD,
        Asm.push localBase, Asm.op .MLOAD] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++
        [Opcode.toByte .MLOAD] ++ emitPush localBase ++ [Opcode.toByte .MLOAD]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t5
  have t7 : emitInstrs labels
      [Asm.op .SLOAD, Asm.push (localBase + 32), Asm.op .MSTORE, Asm.push (localBase + 32),
        Asm.op .MLOAD, Asm.push localBase, Asm.op .MLOAD] =
      .ok ([Opcode.toByte .SLOAD] ++ emitPush (localBase + 32) ++ [Opcode.toByte .MSTORE] ++
        emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++ emitPush localBase ++
        [Opcode.toByte .MLOAD]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SLOAD) t6
  have t8 := emit_cons_ok (emitOne_push labels 0) t7
  simpa [prefixInstrs, prefixBytes, emitPush_zero, emitPush_0x80, emitPush_0xA0, localBase,
    List.append_assoc] using t8

theorem emit_checkedAdd (labels : List (String × Nat))
    (hR : lookupLabel labels addR = .ok addRPc)
    (hO : lookupLabel labels addO = .ok addOPc) :
    emitInstrs labels checkedAddInstrs = .ok checkedAddBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have tjdO : emitInstrs labels [Asm.jumpDest addO] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels addO) t0
  have hPanicOk := emit_bind_ok (IncBody.emit_panic labels) tjdO
  have tJump : emitInstrs labels [Asm.jump addO] =
      .ok (emitPush2 addOPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump labels addO hO addOPc_lt) t0
  have tJumpi : emitInstrs labels [Asm.jumpi addR] =
      .ok (emitPush2 addRPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels addR hR addRPc_lt) t0
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
  simpa [checkedAddInstrs, checkedAddBytes, IncBody.panicBytes, List.append_assoc] using h8

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
      [Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++
        emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t7
  have t9 : emitInstrs labels
      [Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic,
        Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush localBase ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels localBase) t8
  have t10 : emitInstrs labels
      [Asm.op .SSTORE, Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE,
        Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
        Asm.op .STOP] =
      .ok ([Opcode.toByte .SSTORE] ++ emitPush localBase ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++
        emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SSTORE) t9
  have t11 : emitInstrs labels
      [Asm.push 0, Asm.op .SSTORE, Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE,
        Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
        Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte .SSTORE] ++ emitPush localBase ++
        [Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++
        emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t10
  have t12 : emitInstrs labels
      [Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.push localBase, Asm.op .MLOAD,
        Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic, Asm.push 32, Asm.push 0,
        Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .SSTORE] ++
        emitPush localBase ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t11
  have t13 : emitInstrs labels
      [Asm.push (localBase + 64), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
        Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic,
        Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok (emitPush (localBase + 64) ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .SSTORE] ++ emitPush localBase ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++
        emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 64)) t12
  have t14 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push (localBase + 64), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
        Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push32 incTopic,
        Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩), Asm.op .STOP] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush (localBase + 64) ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .SSTORE] ++ emitPush localBase ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush32 incTopic ++ emitPush 32 ++
        emitPush 0 ++ [Opcode.toByte (.LOG ⟨1, by decide⟩)] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t13
  have t15 := emit_cons_ok (emitOne_push labels (localBase + 64)) t14
  simpa [tailInstrs, tailBytes, emitPush_zero, emitPush_thirtyTwo, emitPush_0x80, emitPush_0xC0,
    localBase, List.append_assoc] using t15

theorem incByInstrs_split :
    incByInstrs = loadParamInstrs ++ requireInstrs ++ prefixInstrs ++ checkedAddInstrs ++
      tailInstrs :=
  rfl

theorem emit_incBy :
    emitInstrs (layoutLabels incByInstrs) incByInstrs = .ok code := by
  have hR := lookup_reqR
  have hO := lookup_reqO
  have hAR := lookup_addR
  have hAO := lookup_addO
  have h := emit_bind_ok
    (emit_bind_ok
      (emit_bind_ok
        (emit_bind_ok (emit_loadParam _) (emit_require _ hR hO))
        (emit_prefix _))
      (emit_checkedAdd _ hAR hAO))
    (emit_tail _)
  simpa [incByInstrs_split, code, List.append_assoc] using h

theorem encode_incBy : encode incByInstrs = .ok code := by
  simp only [encode, dup_incBy, bind, Except.bind]
  exact emit_incBy

@[simp] theorem loadParamBytes_length : loadParamBytes.length = 6 := rfl

@[simp] theorem requireHeadBytes_length : requireHeadBytes.length = 7 := rfl

@[simp] theorem zeroRevertBytes_length : zeroRevertBytes.length = 39 := by
  simp [zeroRevertBytes, emitPush32, natToBytesBE_length]

@[simp] theorem requireBytes_length : requireBytes.length = 56 := by
  simp [requireBytes, emitPush2, natToBytesBE_length]

@[simp] theorem prefixBytes_length : prefixBytes.length = 11 := rfl

@[simp] theorem checkedAddBytes_length : checkedAddBytes.length = 59 := by
  simp [checkedAddBytes, emitPush2, natToBytesBE_length]

end Lsc3.Compile.IncByBody
