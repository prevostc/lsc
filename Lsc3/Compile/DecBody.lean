import Lsc3.Examples.Counter
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Codegen
import Lsc3.Compile.Encode
import Lsc3.Compile.Contract
import Lsc3.Compile.IncBody
import Lsc3.Compile.Jump

/-!
# Codegen of `decrement` (saturating: `if count = 0 then 0 else count -? 1`)

No calldata arguments. Jump labels are those of `Ctx.forFunction {} "decrement" 0`.
-/

namespace Lsc3.Compile.DecBody

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Codegen Counter

def decFn : FnDef where
  name := "decrement"
  decl := .anonymous
  kind := .tx
  params := []
  ret := .unit
  core := .letOp (.load 0)
    (.ite (.eq (.var 0) (.lit 0))
      (.letOp (.pure (.lit 0)) (.stmtTail (.store 0 (.var 0))))
      (.letOp (.subChecked (.var 0) (.lit 1)) (.stmtTail (.store 0 (.var 0)))))

theorem decFn_core :
    decFn.core =
      Core.letOp (.load 0)
        (Core.ite (.eq (.var 0) (.lit 0))
          (Core.letOp (.pure (.lit 0)) (Core.stmtTail (.store 0 (.var 0))))
          (Core.letOp (.subChecked (.var 0) (.lit 1))
            (Core.stmtTail (.store 0 (.var 0))))) :=
  rfl

def elseL : String := "decrement.else0"
def endL : String := "decrement.end1"
def subR : String := "decrement.subR2"
def subO : String := "decrement.subO3"

def loadInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push localBase, Asm.op .MSTORE]

def condInstrs : List Asm :=
  [Asm.push localBase, Asm.op .MLOAD, Asm.push 0, Asm.op .EQ]

def thenInstrs : List Asm :=
  [Asm.push 0, Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.op .STOP]

def checkedSubInstrs : List Asm :=
  [dup2, dup2, Asm.op .GT,
   Asm.jumpi subR, Asm.jump subO, Asm.jumpDest subR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest subO, swap1, Asm.op .SUB]

def elseInstrs : List Asm :=
  [Asm.push localBase, Asm.op .MLOAD, Asm.push 1] ++
  checkedSubInstrs ++
  [Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.op .STOP]

def decInstrs : List Asm :=
  loadInstrs ++ condInstrs ++
    [Asm.op .ISZERO, Asm.jumpi elseL] ++
    thenInstrs ++
    [Asm.jump endL, Asm.jumpDest elseL] ++
    elseInstrs ++
    [Asm.jumpDest endL]

set_option maxRecDepth 20000 in
theorem decrement_genFunction :
    genFunction contract decFn {} =
      .ok (decInstrs, { depth := 0, labelCounter := 4, labelPrefix := "" }) :=
  rfl

def elsePc : Nat := 29
def endPc : Nat := 103
def subRPc : Nat := 46
def subOPc : Nat := 91

set_option maxRecDepth 20000 in
theorem labels_dec :
    layoutLabels decInstrs =
      [(endL, endPc), (subO, subOPc), (subR, subRPc), (elseL, elsePc)] :=
  rfl

theorem lookup_else :
    lookupLabel (layoutLabels decInstrs) elseL = .ok elsePc := by
  simp [labels_dec, lookupLabel, subO, subR, endL, elseL]

theorem lookup_end :
    lookupLabel (layoutLabels decInstrs) endL = .ok endPc := by
  simp [labels_dec, lookupLabel, subO, subR, endL, elseL]

theorem lookup_subR :
    lookupLabel (layoutLabels decInstrs) subR = .ok subRPc := by
  simp [labels_dec, lookupLabel, subO, subR, endL, elseL]

theorem lookup_subO :
    lookupLabel (layoutLabels decInstrs) subO = .ok subOPc := by
  simp [labels_dec, lookupLabel, subO, subR, endL, elseL]

theorem dup_dec : checkDuplicateLabels decInstrs = .ok () := rfl

theorem elsePc_lt : elsePc < jumpImmBound := by decide
theorem endPc_lt : endPc < jumpImmBound := by decide
theorem subRPc_lt : subRPc < jumpImmBound := by decide
theorem subOPc_lt : subOPc < jumpImmBound := by decide

theorem elsePc_mod : elsePc % 2 ^ 16 = elsePc := Nat.mod_eq_of_lt (by decide)
theorem endPc_mod : endPc % 2 ^ 16 = endPc := Nat.mod_eq_of_lt (by decide)
theorem subRPc_mod : subRPc % 2 ^ 16 = subRPc := Nat.mod_eq_of_lt (by decide)
theorem subOPc_mod : subOPc % 2 ^ 16 = subOPc := Nat.mod_eq_of_lt (by decide)

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

def loadBytes : List UInt8 :=
  [0x5f, Opcode.toByte .SLOAD, 0x60, 0x80, Opcode.toByte .MSTORE]

def condBytes : List UInt8 :=
  [0x60, 0x80, Opcode.toByte .MLOAD, 0x5f, Opcode.toByte .EQ]

def thenBytes : List UInt8 :=
  [0x5f, 0x60, 0xA0, Opcode.toByte .MSTORE, 0x60, 0xA0, Opcode.toByte .MLOAD, 0x5f,
    Opcode.toByte .SSTORE, Opcode.toByte .STOP]

def checkedSubBytes : List UInt8 :=
  [0x81, 0x81, 0x11] ++
    emitPush2 subRPc ++ [Opcode.toByte .JUMPI] ++
    emitPush2 subOPc ++ [Opcode.toByte .JUMP] ++
    [Opcode.toByte .JUMPDEST] ++ IncBody.panicBytes ++
    [Opcode.toByte .JUMPDEST, 0x90, Opcode.toByte .SUB]

def elseTailBytes : List UInt8 :=
  [0x60, 0xA0, Opcode.toByte .MSTORE, 0x60, 0xA0, Opcode.toByte .MLOAD, 0x5f,
    Opcode.toByte .SSTORE, Opcode.toByte .STOP]

def elseBytes : List UInt8 :=
  [0x60, 0x80, Opcode.toByte .MLOAD, 0x60, 1] ++ checkedSubBytes ++ elseTailBytes

/-- Right-associated so later `drop_left'` proofs do not unfold the panic payload. -/
def code : List UInt8 :=
  loadBytes ++ (condBytes ++ ([Opcode.toByte .ISZERO] ++ (emitPush2 elsePc ++
    ([Opcode.toByte .JUMPI] ++ (thenBytes ++ (emitPush2 endPc ++ ([Opcode.toByte .JUMP] ++
      ([Opcode.toByte .JUMPDEST] ++ (elseBytes ++ [Opcode.toByte .JUMPDEST])))))))))

theorem emit_load (labels : List (String × Nat)) :
    emitInstrs labels loadInstrs = .ok loadBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .MSTORE] = .ok [Opcode.toByte .MSTORE] := by
    simpa using emit_cons_ok (emitOne_op labels .MSTORE) t0
  have t2 : emitInstrs labels [Asm.push localBase, Asm.op .MSTORE] =
      .ok (emitPush localBase ++ [Opcode.toByte .MSTORE]) := by
    simpa using emit_cons_ok (emitOne_push labels localBase) t1
  have t3 : emitInstrs labels [Asm.op .SLOAD, Asm.push localBase, Asm.op .MSTORE] =
      .ok ([Opcode.toByte .SLOAD] ++ emitPush localBase ++ [Opcode.toByte .MSTORE]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SLOAD) t2
  have t4 := emit_cons_ok (emitOne_push labels 0) t3
  simpa [loadInstrs, loadBytes, emitPush_zero, emitPush_0x80, localBase,
    List.append_assoc] using t4

theorem emit_cond (labels : List (String × Nat)) :
    emitInstrs labels condInstrs = .ok condBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .EQ] = .ok [Opcode.toByte .EQ] := by
    simpa using emit_cons_ok (emitOne_op labels .EQ) t0
  have t2 : emitInstrs labels [Asm.push 0, Asm.op .EQ] =
      .ok (emitPush 0 ++ [Opcode.toByte .EQ]) := by
    simpa using emit_cons_ok (emitOne_push labels 0) t1
  have t3 : emitInstrs labels [Asm.op .MLOAD, Asm.push 0, Asm.op .EQ] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .EQ]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t2
  have t4 := emit_cons_ok (emitOne_push labels localBase) t3
  simpa [condInstrs, condBytes, emitPush_zero, emitPush_0x80, localBase,
    List.append_assoc] using t4

theorem emit_then (labels : List (String × Nat)) :
    emitInstrs labels thenInstrs = .ok thenBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .STOP] = .ok [Opcode.toByte .STOP] := by
    simpa using emit_cons_ok (emitOne_op labels .STOP) t0
  have t2 : emitInstrs labels [Asm.op .SSTORE, Asm.op .STOP] =
      .ok ([Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa using emit_cons_ok (emitOne_op labels .SSTORE) t1
  have t3 : emitInstrs labels [Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t2
  have t4 : emitInstrs labels [Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .SSTORE] ++
        [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t3
  have t5 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t4
  have t6 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
        Asm.op .STOP] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t5
  have t7 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD,
        Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++
        [Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .SSTORE] ++
        [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t6
  have t8 := emit_cons_ok (emitOne_push labels 0) t7
  simpa [thenInstrs, thenBytes, emitPush_zero, emitPush_0xA0, localBase,
    List.append_assoc] using t8

theorem emit_checkedSub (labels : List (String × Nat))
    (hR : lookupLabel labels subR = .ok subRPc)
    (hO : lookupLabel labels subO = .ok subOPc) :
    emitInstrs labels checkedSubInstrs = .ok checkedSubBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have tSub : emitInstrs labels [Asm.op .SUB] = .ok [Opcode.toByte .SUB] := by
    simpa using emit_cons_ok (emitOne_op labels .SUB) t0
  have tSw : emitInstrs labels [swap1, Asm.op .SUB] =
      .ok ([Opcode.toByte (.SWAP ⟨0, by decide⟩)] ++ [Opcode.toByte .SUB]) := by
    simpa using emit_cons_ok (emitOne_op labels (.SWAP ⟨0, by decide⟩)) tSub
  have tjdO : emitInstrs labels [Asm.jumpDest subO, swap1, Asm.op .SUB] =
      .ok ([Opcode.toByte .JUMPDEST] ++ [Opcode.toByte (.SWAP ⟨0, by decide⟩)] ++
        [Opcode.toByte .SUB]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_jumpDest labels subO) tSw
  have hPanic := emit_bind_ok (IncBody.emit_panic labels) tjdO
  have tjdR : emitInstrs labels [Asm.jumpDest subR] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels subR) t0
  have tJump : emitInstrs labels [Asm.jump subO] =
      .ok (emitPush2 subOPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump labels subO hO subOPc_lt) t0
  have tJumpi : emitInstrs labels [Asm.jumpi subR] =
      .ok (emitPush2 subRPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels subR hR subRPc_lt) t0
  have tGt : emitInstrs labels [Asm.op .GT] = .ok [Opcode.toByte .GT] := by
    simpa using emit_cons_ok (emitOne_op labels .GT) t0
  have tDup : emitInstrs labels [dup2] = .ok [Opcode.toByte (.DUP ⟨1, by decide⟩)] := by
    simpa using emit_cons_ok (emitOne_op labels (.DUP ⟨1, by decide⟩)) t0
  have h1 := emit_bind_ok tDup (emit_bind_ok tDup tGt)
  have h2 := emit_bind_ok h1 (emit_bind_ok tJumpi (emit_bind_ok tJump
    (emit_bind_ok tjdR hPanic)))
  simpa [checkedSubInstrs, checkedSubBytes, List.append_assoc] using h2

theorem emit_elseTail (labels : List (String × Nat)) :
    emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MSTORE,
       Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
       Asm.op .STOP] = .ok elseTailBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .STOP] = .ok [Opcode.toByte .STOP] := by
    simpa using emit_cons_ok (emitOne_op labels .STOP) t0
  have t2 : emitInstrs labels [Asm.op .SSTORE, Asm.op .STOP] =
      .ok ([Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa using emit_cons_ok (emitOne_op labels .SSTORE) t1
  have t3 : emitInstrs labels [Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok (emitPush 0 ++ [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t2
  have t4 : emitInstrs labels [Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 0 ++ [Opcode.toByte .SSTORE] ++
        [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t3
  have t5 : emitInstrs labels
      [Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE, Asm.op .STOP] =
      .ok (emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++ emitPush 0 ++
        [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels (localBase + 32)) t4
  have t6 : emitInstrs labels
      [Asm.op .MSTORE, Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
        Asm.op .STOP] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush (localBase + 32) ++ [Opcode.toByte .MLOAD] ++
        emitPush 0 ++ [Opcode.toByte .SSTORE] ++ [Opcode.toByte .STOP]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t5
  have t7 := emit_cons_ok (emitOne_push labels (localBase + 32)) t6
  simpa [elseTailBytes, emitPush_zero, emitPush_0xA0, localBase, List.append_assoc] using t7

theorem emit_else (labels : List (String × Nat))
    (hR : lookupLabel labels subR = .ok subRPc)
    (hO : lookupLabel labels subO = .ok subOPc) :
    emitInstrs labels elseInstrs = .ok elseBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have hTail := emit_elseTail labels
  have hChk := emit_checkedSub labels hR hO
  have t1 : emitInstrs labels [Asm.push 1] = .ok (emitPush 1) := by
    simpa using emit_cons_ok (emitOne_push labels 1) t0
  have t2 : emitInstrs labels [Asm.op .MLOAD, Asm.push 1] =
      .ok ([Opcode.toByte .MLOAD] ++ emitPush 1) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MLOAD) t1
  have t3 := emit_cons_ok (emitOne_push labels localBase) t2
  have hHead : emitInstrs labels [Asm.push localBase, Asm.op .MLOAD, Asm.push 1] =
      .ok ([0x60, 0x80, Opcode.toByte .MLOAD, 0x60, 1]) := by
    simpa [emitPush_0x80, emitPush_one, localBase, List.append_assoc] using t3
  have h := emit_bind_ok (emit_bind_ok hHead hChk) hTail
  simpa [elseInstrs, elseBytes, List.append_assoc] using h

theorem emit_dec :
    emitInstrs (layoutLabels decInstrs) decInstrs = .ok code := by
  have hE := lookup_else
  have hN := lookup_end
  have hR := lookup_subR
  have hO := lookup_subO
  have t0 : emitInstrs (layoutLabels decInstrs) ([] : List Asm) = .ok [] :=
    emitInstrs_nil _
  have tjdEnd : emitInstrs (layoutLabels decInstrs) [Asm.jumpDest endL] =
      .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest (layoutLabels decInstrs) endL) t0
  have tJumpEnd : emitInstrs (layoutLabels decInstrs) [Asm.jump endL] =
      .ok (emitPush2 endPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump (layoutLabels decInstrs) endL hN endPc_lt) t0
  have tjdElse : emitInstrs (layoutLabels decInstrs) [Asm.jumpDest elseL] =
      .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest (layoutLabels decInstrs) elseL) t0
  have tJumpi : emitInstrs (layoutLabels decInstrs) [Asm.jumpi elseL] =
      .ok (emitPush2 elsePc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok
      (emitOne_jumpi (layoutLabels decInstrs) elseL hE elsePc_lt) t0
  have tIz : emitInstrs (layoutLabels decInstrs) [Asm.op .ISZERO] =
      .ok [Opcode.toByte .ISZERO] := by
    simpa using emit_cons_ok (emitOne_op (layoutLabels decInstrs) .ISZERO) t0
  have hElse := emit_else (layoutLabels decInstrs) hR hO
  have h := emit_bind_ok (emit_load _) (emit_bind_ok (emit_cond _)
    (emit_bind_ok tIz (emit_bind_ok tJumpi (emit_bind_ok (emit_then _)
      (emit_bind_ok tJumpEnd (emit_bind_ok tjdElse (emit_bind_ok hElse tjdEnd)))))))
  simpa [decInstrs, code, List.append_assoc] using h

theorem encode_dec : encode decInstrs = .ok code := by
  simp only [encode, dup_dec, bind, Except.bind]
  exact emit_dec

@[simp] theorem loadBytes_length : loadBytes.length = 5 := rfl
@[simp] theorem condBytes_length : condBytes.length = 5 := rfl
@[simp] theorem thenBytes_length : thenBytes.length = 10 := rfl
@[simp] theorem elseTailBytes_length : elseTailBytes.length = 9 := rfl

@[simp] theorem checkedSubBytes_length : checkedSubBytes.length = 59 := by
  simp [checkedSubBytes, emitPush2, natToBytesBE_length, IncBody.panicBytes_length]

@[simp] theorem elseBytes_length : elseBytes.length = 73 := by
  simp [elseBytes, checkedSubBytes_length, elseTailBytes_length]

end Lsc3.Compile.DecBody
