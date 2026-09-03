import Lsc3.Core
import Lsc3.Contract
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Contract
import Lsc3.Compile.IncBody
import Lsc3.Compile.GetContract
import Lsc3.Compile.DispatchGet
import Lsc3.Compile.Jump

/-!
# Compiler `increment` — one function, production encoding

Same dispatcher as the get-only compiler (PUSH2 jumps, PUSH4 selector, PUSH32 revert).
The body is `IncBody` shifted to PC 68, so checked-add destinations are 91 and 136.
`compile_incOnly` is the encode certificate; `incOnly_hit` is the matching-selector
machine certificate (apply it; do not instantiate at `selectorOf "increment" []`).
-/

namespace Lsc3.Compile.IncContract

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Codegen
open Lsc3.Compile.Jump
open Lsc3.Compile.GetContract (revLbl invalidSel)
open Lsc3.Compile.DispatchGet (push4Bytes decodeAt_push4)

def incFn : FnDef where
  name := "increment"
  decl := .anonymous
  kind := .tx
  params := []
  ret := .unit
  core := .letOp (.load 0)
    (.letOp (.addChecked (.var 0) (.lit 1))
      (.seq (.store 0 (.var 0))
        (.stmtTail (.emit 0 [.lit 1]))))

@[irreducible] def incEvents : List EventDef :=
  [{ name := "Incremented", params := [{ name := "by_", ty := .uint256 }] }]

def incOnly : ContractDef where
  name := "Inc"
  fields := [{ name := "count", kind := .scalar, ty := .uint256 }]
  functions := [incFn]
  ctor := none
  events := incEvents
  errors := []

def incTopic : Nat :=
  if h : 0 < incOnly.events.length then EventDef.topic0 incOnly.events[0] else 0

def checkInstrs : List Asm :=
  [Asm.push 4, Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl]

def fallInstrs : List Asm := [Asm.jump revLbl]

def addR : String := "increment.addR1"
def addO : String := "increment.addO2"
def incPc : Nat := 67
def bodyRevPc : Nat := 91
def bodyOkPc : Nat := 136

abbrev checkBytes : List UInt8 := GetContract.checkBytes
abbrev loadSelBytes : List UInt8 := GetContract.loadSelBytes
abbrev fallBytes : List UInt8 := GetContract.fallBytes
abbrev revertBytes : List UInt8 := GetContract.revertBytes

def branchInstrs (sel : Nat) : List Asm :=
  loadSelector ++ [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "increment"]

def bodyInstrs : List Asm :=
  IncBody.prefixInstrs ++
  [dup2, Asm.op .ADD, dup1, swap2, Asm.op .GT,
   Asm.jumpi addR, Asm.jump addO, Asm.jumpDest addR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest addO] ++
  [Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push 1, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

def expectedInstrs (sel : Nat) : List Asm :=
  checkInstrs ++ branchInstrs sel ++ fallInstrs ++
    [Asm.jumpDest revLbl] ++ emitRevert invalidSel ++
    [Asm.jumpDest "increment"] ++ bodyInstrs

theorem incFn_core :
    incFn.core =
      Core.letOp (.load 0)
        (Core.letOp (.addChecked (.var 0) (.lit 1))
          (Core.seq (.store 0 (.var 0))
            (Core.stmtTail (.emit 0 [.lit 1])))) :=
  rfl

-- `contractInstrs`/`genCore` equality is not `rfl`'d: the emit topic is an `if` over
-- `events.length` that must not be reduced (Keccak). Encode of `expectedInstrs` is certified.

set_option maxRecDepth 20000 in
theorem labels_expected (sel : Nat) :
    layoutLabels (expectedInstrs sel) =
      [(addO, bodyOkPc), (addR, bodyRevPc), ("increment", incPc), (revLbl, GetContract.revPc)] :=
  rfl

theorem lookup_inc (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) "increment" = .ok incPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_rev (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) revLbl = .ok GetContract.revPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_addR (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) addR = .ok bodyRevPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_addO (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) addO = .ok bodyOkPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem dup_expected (sel : Nat) :
    checkDuplicateLabels (expectedInstrs sel) = .ok () :=
  rfl

theorem incPc_lt : incPc < jumpImmBound := by decide
theorem bodyRevPc_lt : bodyRevPc < jumpImmBound := by decide
theorem bodyOkPc_lt : bodyOkPc < jumpImmBound := by decide

def branchBytes (sel : Nat) : List UInt8 :=
  loadSelBytes ++ emitPush4 sel ++ [Opcode.toByte .EQ] ++
    emitPush2 incPc ++ [Opcode.toByte .JUMPI]

def preBytes (sel : Nat) : List UInt8 :=
  checkBytes ++ branchBytes sel ++ fallBytes

def tailInstrs : List Asm :=
  [Asm.push (localBase + 32), Asm.op .MSTORE,
   Asm.push (localBase + 32), Asm.op .MLOAD, Asm.push 0, Asm.op .SSTORE,
   Asm.push 1, Asm.push 0, Asm.op .MSTORE,
   Asm.push32 incTopic, Asm.push 32, Asm.push 0, Asm.op (.LOG ⟨1, by decide⟩),
   Asm.op .STOP]

def tailBytes : List UInt8 :=
  [0x60, 0xA0, 0x52, 0x60, 0xA0, 0x51, 0x5f, 0x55, 0x60, 1, 0x5f, 0x52] ++
    emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00]

def checkedAddBytes : List UInt8 :=
  [0x81, 0x01, 0x80, 0x91, 0x11] ++
    emitPush2 bodyRevPc ++ [Opcode.toByte .JUMPI] ++
    emitPush2 bodyOkPc ++ [Opcode.toByte .JUMP] ++
    [Opcode.toByte .JUMPDEST] ++ IncBody.panicBytes ++ [Opcode.toByte .JUMPDEST]

def bodyBytes : List UInt8 :=
  IncBody.prefixBytes ++ checkedAddBytes ++ tailBytes

def code (sel : Nat) : List UInt8 :=
  preBytes sel ++ [Opcode.toByte .JUMPDEST] ++ revertBytes ++
    [Opcode.toByte .JUMPDEST] ++ bodyBytes

@[simp] theorem branchBytes_length (sel : Nat) : (branchBytes sel).length = 15 := by
  simp [branchBytes, emitPush2, emitPush4, natToBytesBE_length]

@[simp] theorem preBytes_length (sel : Nat) : (preBytes sel).length = GetContract.revPc := by
  simp [preBytes, GetContract.revPc]

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

def checkedAddInstrs : List Asm :=
  [dup2, Asm.op .ADD, dup1, swap2, Asm.op .GT,
   Asm.jumpi addR, Asm.jump addO, Asm.jumpDest addR] ++
  emitPanic 0x11 ++
  [Asm.jumpDest addO]

theorem bodyInstrs_split :
    bodyInstrs = IncBody.prefixInstrs ++ checkedAddInstrs ++ tailInstrs :=
  rfl

theorem emit_checkedAdd (labels : List (String × Nat))
    (hR : lookupLabel labels addR = .ok bodyRevPc)
    (hO : lookupLabel labels addO = .ok bodyOkPc) :
    emitInstrs labels checkedAddInstrs = .ok checkedAddBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have tjdO : emitInstrs labels [Asm.jumpDest addO] = .ok [Opcode.toByte .JUMPDEST] := by
    simpa using emit_cons_ok (emitOne_jumpDest labels addO) t0
  have hPanicOk := emit_bind_ok (IncBody.emit_panic labels) tjdO
  have tJump : emitInstrs labels [Asm.jump addO] =
      .ok (emitPush2 bodyOkPc ++ [Opcode.toByte .JUMP]) := by
    simpa using emit_cons_ok (emitOne_jump labels addO hO bodyOkPc_lt) t0
  have tJumpi : emitInstrs labels [Asm.jumpi addR] =
      .ok (emitPush2 bodyRevPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels addR hR bodyRevPc_lt) t0
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

theorem emit_bodyInstrs (labels : List (String × Nat))
    (hR : lookupLabel labels addR = .ok bodyRevPc)
    (hO : lookupLabel labels addO = .ok bodyOkPc) :
    emitInstrs labels bodyInstrs = .ok bodyBytes := by
  have h := emit_bind_ok
    (emit_bind_ok (IncBody.emit_prefix labels) (emit_checkedAdd labels hR hO))
    (emit_tail labels)
  simpa [bodyInstrs_split, bodyBytes, List.append_assoc] using h

theorem emit_branchTail (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "increment" = .ok incPc) :
    emitInstrs labels [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "increment"] =
      .ok (emitPush4 sel ++ [Opcode.toByte .EQ] ++ emitPush2 incPc ++ [Opcode.toByte .JUMPI]) := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.jumpi "increment"] =
      .ok (emitPush2 incPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels "increment" h incPc_lt) t0
  have t2 : emitInstrs labels [Asm.op .EQ, Asm.jumpi "increment"] =
      .ok ([Opcode.toByte .EQ] ++ emitPush2 incPc ++ [Opcode.toByte .JUMPI]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .EQ) t1
  have t3 := emit_cons_ok (emitOne_push4 labels sel) t2
  simpa [List.append_assoc] using t3

theorem emit_branchInstrs (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "increment" = .ok incPc) :
    emitInstrs labels (branchInstrs sel) = .ok (branchBytes sel) := by
  have h1 := emit_bind_ok (GetContract.emit_loadSelector labels) (emit_branchTail labels sel h)
  simpa [branchInstrs, branchBytes, List.append_assoc] using h1

theorem emit_expected (sel : Nat) :
    emitInstrs (layoutLabels (expectedInstrs sel)) (expectedInstrs sel) = .ok (code sel) := by
  set L := layoutLabels (expectedInstrs sel)
  have hrev : lookupLabel L revLbl = .ok GetContract.revPc := lookup_rev sel
  have hinc : lookupLabel L "increment" = .ok incPc := lookup_inc sel
  have hR : lookupLabel L addR = .ok bodyRevPc := lookup_addR sel
  have hO : lookupLabel L addO = .ok bodyOkPc := lookup_addO sel
  have h6 :=
    emit_bind_ok
      (emit_bind_ok
        (emit_bind_ok
          (emit_bind_ok
            (emit_bind_ok
              (emit_bind_ok (GetContract.emit_checkInstrs L hrev) (emit_branchInstrs L sel hinc))
              (GetContract.emit_fallInstrs L hrev))
            (GetContract.emit_jumpDest L revLbl))
          (GetContract.emit_revertInstrs L))
        (GetContract.emit_jumpDest L "increment"))
      (emit_bodyInstrs L hR hO)
  simpa [expectedInstrs, code, preBytes, List.append_assoc] using h6

theorem encode_expected (sel : Nat) :
    encode (expectedInstrs sel) = .ok (code sel) := by
  simp only [encode, dup_expected, bind, Except.bind]
  exact emit_expected sel

set_option maxRecDepth 20000 in
theorem incOnly_instrs :
    contractInstrs incOnly = .ok (expectedInstrs (FnDef.selector incFn)) :=
  rfl

theorem compile_incOnly :
    compileContract incOnly = .ok (code (FnDef.selector incFn)) := by
  simp only [compileContract, incOnly_instrs, bind, Except.bind]
  exact encode_expected (FnDef.selector incFn)

theorem incPc_mod : incPc % 2 ^ 16 = incPc := Nat.mod_eq_of_lt (by decide)
theorem bodyRevPc_mod : bodyRevPc % 2 ^ 16 = bodyRevPc := Nat.mod_eq_of_lt (by decide)
theorem bodyOkPc_mod : bodyOkPc % 2 ^ 16 = bodyOkPc := Nat.mod_eq_of_lt (by decide)

@[simp] theorem checkedAddBytes_length : checkedAddBytes.length = 59 := by
  simp [checkedAddBytes, emitPush2, natToBytesBE_length]

@[simp] theorem tailBytes_length : tailBytes.length = 50 := by
  simp [tailBytes, emitPush32, natToBytesBE_length]

@[simp] theorem bodyBytes_length : bodyBytes.length = 119 := by
  simp [bodyBytes]

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

theorem code_spine (sel : Nat) :
    code sel =
      checkBytes ++ (loadSelBytes ++ (emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))))) := by
  simp [code, preBytes, branchBytes, List.append_assoc]

theorem code_drop8 (sel : Nat) :
    (code sel).drop 8 =
      loadSelBytes ++ (emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))))) := by
  rw [code_spine, List.drop_left' GetContract.checkBytes_length]

theorem code_drop13 (sel : Nat) :
    (code sel).drop 13 =
      emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))))) := by
  rw [show 13 = 8 + 5 from rfl, drop_add, code_drop8, List.drop_left' GetContract.loadSelBytes_length]

theorem code_drop18 (sel : Nat) :
    (code sel).drop 18 =
      [Opcode.toByte .EQ] ++
        (emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))))) := by
  rw [show 18 = 13 + 5 from rfl, drop_add, code_drop13, List.drop_left' (emitPush4_length sel)]

theorem code_drop19 (sel : Nat) :
    (code sel).drop 19 =
      emitPush2 incPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ bodyBytes))))) := by
  rw [show 19 = 18 + 1 from rfl, drop_add, code_drop18]; rfl

theorem code_drop22 (sel : Nat) :
    (code sel).drop 22 =
      [Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ bodyBytes)))) := by
  rw [show 22 = 19 + 3 from rfl, drop_add, code_drop19, List.drop_left' (emitPush2_length incPc)]

theorem code_drop23 (sel : Nat) :
    (code sel).drop 23 =
      fallBytes ++ ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ bodyBytes))) := by
  rw [show 23 = 22 + 1 from rfl, drop_add, code_drop22]; rfl

theorem code_drop27 (sel : Nat) :
    (code sel).drop 27 =
      [Opcode.toByte .JUMPDEST] ++ (revertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ bodyBytes)) := by
  rw [show 27 = 23 + 4 from rfl, drop_add, code_drop23, List.drop_left' GetContract.fallBytes_length]

theorem code_drop28 (sel : Nat) :
    (code sel).drop 28 =
      revertBytes ++ ([Opcode.toByte .JUMPDEST] ++ bodyBytes) := by
  rw [show 28 = 27 + 1 from rfl, drop_add, code_drop27]; rfl

theorem code_drop67 (sel : Nat) :
    (code sel).drop 67 = [Opcode.toByte .JUMPDEST] ++ bodyBytes := by
  rw [show 67 = 28 + 39 from rfl, drop_add, code_drop28, List.drop_left' GetContract.revertBytes_length]

theorem code_drop68 (sel : Nat) :
    (code sel).drop 68 = bodyBytes := by
  rw [show 68 = 67 + 1 from rfl, drop_add, code_drop67]; rfl

theorem code_after4 (sel : Nat) :
    code sel =
      [0x60, 4, 0x36, 0x10] ++
        (emitPush2 GetContract.revPc ++ Opcode.toByte .JUMPI :: (code sel).drop 8) := by
  rw [code_drop8]
  simp [code, preBytes, checkBytes, GetContract.checkBytes, branchBytes, List.append_assoc]

theorem code_drop4 (sel : Nat) :
    (code sel).drop 4 =
      emitPush2 GetContract.revPc ++ (Opcode.toByte .JUMPI :: (code sel).drop 8) := by
  rw [code_after4]
  exact List.drop_left' (by decide : ([0x60, 4, 0x36, 0x10] : List UInt8).length = 4)

theorem code_drop7 (sel : Nat) :
    (code sel).drop 7 = Opcode.toByte .JUMPI :: (code sel).drop 8 := by
  rw [show 7 = 4 + 3 from rfl, drop_add, code_drop4]
  exact List.drop_left' (emitPush2_length GetContract.revPc)

def bodyPre (sel : Nat) : List UInt8 :=
  preBytes sel ++ [Opcode.toByte .JUMPDEST] ++ revertBytes ++ [Opcode.toByte .JUMPDEST]

@[simp] theorem bodyPre_length (sel : Nat) : (bodyPre sel).length = 68 := by
  simp [bodyPre, GetContract.revPc]

theorem code_bodyPre (sel : Nat) : code sel = bodyPre sel ++ bodyBytes := rfl

theorem emitPush4_eq_push4 (sel : Nat) : emitPush4 sel = push4Bytes sel := rfl

theorem decode_pc0 (sel : Nat) :
    decodeAt (code sel) 0 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 2) := by
  have h : (code sel).drop 0 = 0x60 :: 4 :: (code sel).drop 2 := by
    simp [code, preBytes, checkBytes, GetContract.checkBytes]
  have h' := decodeAt_of_drop h (decodeAt_push1_head (4 : UInt8) ((code sel).drop 2))
  simpa [wrap] using h'

theorem decode_pc2 (sel : Nat) :
    decodeAt (code sel) 2 = some ({ op := .CALLDATASIZE }, 3) := by
  have h : (code sel).drop 2 = Opcode.toByte .CALLDATASIZE :: (code sel).drop 3 := by
    simp [code, preBytes, checkBytes, GetContract.checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATASIZE _ rfl)

theorem decode_pc3 (sel : Nat) :
    decodeAt (code sel) 3 = some ({ op := .LT }, 4) := by
  have h : (code sel).drop 3 = Opcode.toByte .LT :: (code sel).drop 4 := by
    simp [code, preBytes, checkBytes, GetContract.checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .LT _ rfl)

theorem decode_pc4 (sel : Nat) :
    decodeAt (code sel) 4 =
      some ({ op := .PUSH ⟨2, by decide⟩, imm := GetContract.revPc }, 7) := by
  have hdrop : (code sel).drop 4 = emitPush2 GetContract.revPc ++ (code sel).drop 7 := by
    rw [code_drop4, code_drop7]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 GetContract.revPc _)
  simpa [GetContract.revPc_mod] using h

theorem decode_pc7 (sel : Nat) :
    decodeAt (code sel) 7 = some ({ op := .JUMPI }, 8) := by
  have h : (code sel).drop 7 = Opcode.toByte .JUMPI :: (code sel).drop 8 := code_drop7 sel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc8 (sel : Nat) :
    decodeAt (code sel) 8 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 9) := by
  have h : (code sel).drop 8 = 0x5f :: (code sel).drop 9 := by
    rw [show 9 = 8 + 1 from rfl, drop_add, code_drop8]
    simp [loadSelBytes, GetContract.loadSelBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc9 (sel : Nat) :
    decodeAt (code sel) 9 = some ({ op := .CALLDATALOAD }, 10) := by
  have h : (code sel).drop 9 = Opcode.toByte .CALLDATALOAD :: (code sel).drop 10 := by
    rw [show 9 = 8 + 1 from rfl, show 10 = 8 + 2 from rfl, drop_add, drop_add, code_drop8]
    simp [loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc10 (sel : Nat) :
    decodeAt (code sel) 10 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 12) := by
  have hdrop : (code sel).drop 10 = 0x60 :: 0xE0 :: (code sel).drop 12 := by
    rw [show 10 = 8 + 2 from rfl, show 12 = 8 + 4 from rfl, drop_add, drop_add, code_drop8]
    simp [loadSelBytes, GetContract.loadSelBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) ((code sel).drop 12))
  simpa [wrap] using h

theorem decode_pc12 (sel : Nat) :
    decodeAt (code sel) 12 = some ({ op := .SHR }, 13) := by
  have h : (code sel).drop 12 = Opcode.toByte .SHR :: (code sel).drop 13 := by
    rw [show 12 = 8 + 4 from rfl, drop_add, code_drop8, code_drop13]
    simp [loadSelBytes, GetContract.loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .SHR _ rfl)

theorem decode_pc13 (sel : Nat) :
    decodeAt (code sel) 13 =
      some ({ op := .PUSH ⟨4, by decide⟩, imm := sel % 2 ^ 32 }, 18) := by
  have hdrop : (code sel).drop 13 = emitPush4 sel ++ (code sel).drop 18 := by
    rw [code_drop13, code_drop18]
  rw [emitPush4_eq_push4] at hdrop
  have h := decodeAt_of_drop hdrop (decodeAt_push4 sel _)
  simpa using h

theorem decode_pc18 (sel : Nat) :
    decodeAt (code sel) 18 = some ({ op := .EQ }, 19) := by
  have h : (code sel).drop 18 = Opcode.toByte .EQ :: (code sel).drop 19 := by
    rw [code_drop18, code_drop19]
    rfl
  exact decodeAt_of_drop h (decodeAt_op_head .EQ _ rfl)

theorem decode_pc19 (sel : Nat) :
    decodeAt (code sel) 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := incPc }, 22) := by
  have hdrop : (code sel).drop 19 = emitPush2 incPc ++ (code sel).drop 22 := by
    rw [code_drop19, code_drop22]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 incPc _)
  simpa [incPc_mod] using h

theorem decode_pc22 (sel : Nat) :
    decodeAt (code sel) 22 = some ({ op := .JUMPI }, 23) := by
  have h : (code sel).drop 22 = Opcode.toByte .JUMPI :: (code sel).drop 23 := code_drop22 sel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc67 (sel : Nat) :
    decodeAt (code sel) 67 = some ({ op := .JUMPDEST }, 68) := by
  have h : (code sel).drop 67 = Opcode.toByte .JUMPDEST :: bodyBytes := by
    rw [code_drop67]
    rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem isJumpDest_inc (sel : Nat) : isJumpDest (code sel) incPc = true := by
  simpa [incPc] using isJumpDest_of_decode (decode_pc67 sel)

theorem body_spine :
    bodyBytes =
      IncBody.prefixBytes ++ ([0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 bodyRevPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes)))))))) := by
  simp [bodyBytes, checkedAddBytes, List.append_assoc]

theorem body_drop10 :
    bodyBytes.drop 10 =
      [0x81, 0x01, 0x80, 0x91, 0x11] ++ (emitPush2 bodyRevPc ++
        (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP ::
          (Opcode.toByte .JUMPDEST :: (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST ::
            tailBytes))))))) := by
  rw [body_spine, List.drop_left' IncBody.prefixBytes_length]

theorem bdec0 :
    decodeAt bodyBytes 0 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 1) := by
  have h : bodyBytes.drop 0 = 0x5f :: bodyBytes.drop 1 := by
    simp [bodyBytes, IncBody.prefixBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem bdec1 :
    decodeAt bodyBytes 1 = some ({ op := .SLOAD }, 2) := by
  have h : bodyBytes.drop 1 = Opcode.toByte .SLOAD :: bodyBytes.drop 2 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_sload_head _)

theorem bdec2 :
    decodeAt bodyBytes 2 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 4) := by
  have hdrop : bodyBytes.drop 2 = 0x60 :: 0x80 :: bodyBytes.drop 4 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (bodyBytes.drop 4))
  simpa [wrap, localBase] using h

theorem bdec4 :
    decodeAt bodyBytes 4 = some ({ op := .MSTORE }, 5) := by
  have h : bodyBytes.drop 4 = Opcode.toByte .MSTORE :: bodyBytes.drop 5 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem bdec5 :
    decodeAt bodyBytes 5 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 7) := by
  have hdrop : bodyBytes.drop 5 = 0x60 :: 0x80 :: bodyBytes.drop 7 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x80 : UInt8) (bodyBytes.drop 7))
  simpa [wrap, localBase] using h

theorem bdec7 :
    decodeAt bodyBytes 7 = some ({ op := .MLOAD }, 8) := by
  have h : bodyBytes.drop 7 = Opcode.toByte .MLOAD :: bodyBytes.drop 8 := by
    simp [bodyBytes, IncBody.prefixBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem bdec8 :
    decodeAt bodyBytes 8 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 10) := by
  have hdrop : bodyBytes.drop 8 = 0x60 :: 1 :: bodyBytes.drop 10 := by
    simp [bodyBytes, IncBody.prefixBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (bodyBytes.drop 10))
  simpa [wrap] using h

theorem bdec10 :
    decodeAt bodyBytes 10 = some ({ op := .DUP ⟨1, by decide⟩ }, 11) := by
  have h : bodyBytes.drop 10 = 0x81 :: bodyBytes.drop 11 := by
    rw [body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup2_head _)

theorem bdec11 :
    decodeAt bodyBytes 11 = some ({ op := .ADD }, 12) := by
  have h : bodyBytes.drop 11 = 0x01 :: bodyBytes.drop 12 := by
    rw [show 11 = 10 + 1 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_add_head _)

theorem bdec12 :
    decodeAt bodyBytes 12 = some ({ op := .DUP ⟨0, by decide⟩ }, 13) := by
  have h : bodyBytes.drop 12 = 0x80 :: bodyBytes.drop 13 := by
    rw [show 12 = 10 + 2 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_dup1_head _)

theorem bdec13 :
    decodeAt bodyBytes 13 = some ({ op := .SWAP ⟨1, by decide⟩ }, 14) := by
  have h : bodyBytes.drop 13 = 0x91 :: bodyBytes.drop 14 := by
    rw [show 13 = 10 + 3 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_swap2_head _)

theorem bdec14 :
    decodeAt bodyBytes 14 = some ({ op := .GT }, 15) := by
  have h : bodyBytes.drop 14 = 0x11 :: bodyBytes.drop 15 := by
    rw [show 14 = 10 + 4 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_gt_head _)

theorem bdec15 :
    decodeAt bodyBytes 15 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyRevPc }, 18) := by
  have hdrop : bodyBytes.drop 15 =
      emitPush2 bodyRevPc ++ (Opcode.toByte .JUMPI :: (emitPush2 bodyOkPc ++
        (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
          (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))))) := by
    rw [show 15 = 10 + 5 from rfl, drop_add, body_drop10]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 bodyRevPc _)
  simpa [bodyRevPc_mod] using h

theorem bdec18 :
    decodeAt bodyBytes 18 = some ({ op := .JUMPI }, 19) := by
  have h : bodyBytes.drop 18 = Opcode.toByte .JUMPI :: bodyBytes.drop 19 := by
    rw [show 18 = 10 + 8 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jumpi_head _)

theorem bdec19 :
    decodeAt bodyBytes 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyOkPc }, 22) := by
  have hdrop : bodyBytes.drop 19 =
      emitPush2 bodyOkPc ++ (Opcode.toByte .JUMP :: (Opcode.toByte .JUMPDEST ::
        (IncBody.panicBytes ++ (Opcode.toByte .JUMPDEST :: tailBytes)))) := by
    rw [show 19 = 10 + 9 from rfl, drop_add, body_drop10]
    rw [show 9 = 5 + 4 from rfl, drop_add]
    rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
    rw [show 4 = 3 + 1 from rfl, drop_add]
    rw [List.drop_left' (emitPush2_length bodyRevPc)]
    rw [List.drop_succ_cons]
    rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push2 bodyOkPc _)
  simpa [bodyOkPc_mod] using h

theorem bdec22 :
    decodeAt bodyBytes 22 = some ({ op := .JUMP }, 23) := by
  have h : bodyBytes.drop 22 = Opcode.toByte .JUMP :: bodyBytes.drop 23 := by
    rw [show 22 = 10 + 12 from rfl, drop_add, body_drop10]; rfl
  exact decodeAt_of_drop h (decodeAt_jump_head _)

theorem body_drop68 :
    bodyBytes.drop 68 = Opcode.toByte .JUMPDEST :: tailBytes := by
  rw [show 68 = 10 + 58 from rfl, drop_add, body_drop10]
  rw [show 58 = 5 + 53 from rfl, drop_add]
  rw [List.drop_left' (by decide : ([0x81, 0x01, 0x80, 0x91, 0x11] : List UInt8).length = 5)]
  rw [show 53 = 3 + 50 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length bodyRevPc)]
  rw [show 50 = 49 + 1 from rfl, List.drop_succ_cons]
  rw [show 49 = 3 + 46 from rfl, drop_add]
  rw [List.drop_left' (emitPush2_length bodyOkPc)]
  rw [show 46 = 45 + 1 from rfl, List.drop_succ_cons]
  rw [show 45 = 44 + 1 from rfl, List.drop_succ_cons]
  rw [List.drop_left' IncBody.panicBytes_length]

theorem bdec68 :
    decodeAt bodyBytes 68 = some ({ op := .JUMPDEST }, 69) := by
  exact decodeAt_of_drop body_drop68 (decodeAt_jumpdest_head _)

theorem body_drop69 : bodyBytes.drop 69 = tailBytes := by
  rw [show 69 = 68 + 1 from rfl, drop_add, body_drop68]
  rfl

theorem tailBytes_drop12 :
    tailBytes.drop 12 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] :=
  rfl

theorem body_drop81 :
    bodyBytes.drop 81 = emitPush32 incTopic ++ [0x60, 0x20, 0x5f, 0xa1, 0x00] := by
  rw [show 81 = 69 + 12 from rfl, drop_add, body_drop69, tailBytes_drop12]

theorem bdec69 :
    decodeAt bodyBytes 69 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 71) := by
  have hdrop : bodyBytes.drop 69 = 0x60 :: 0xA0 :: bodyBytes.drop 71 := by
    rw [body_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (bodyBytes.drop 71))
  simpa [wrap, localBase] using h

theorem bdec71 :
    decodeAt bodyBytes 71 = some ({ op := .MSTORE }, 72) := by
  have h : bodyBytes.drop 71 = Opcode.toByte .MSTORE :: bodyBytes.drop 72 := by
    rw [show 71 = 69 + 2 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem bdec72 :
    decodeAt bodyBytes 72 = some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 74) := by
  have hdrop : bodyBytes.drop 72 = 0x60 :: 0xA0 :: bodyBytes.drop 74 := by
    rw [show 72 = 69 + 3 from rfl, drop_add, body_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xA0 : UInt8) (bodyBytes.drop 74))
  simpa [wrap, localBase] using h

theorem bdec74 :
    decodeAt bodyBytes 74 = some ({ op := .MLOAD }, 75) := by
  have h : bodyBytes.drop 74 = Opcode.toByte .MLOAD :: bodyBytes.drop 75 := by
    rw [show 74 = 69 + 5 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mload_head _)

theorem bdec75 :
    decodeAt bodyBytes 75 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 76) := by
  have h : bodyBytes.drop 75 = 0x5f :: bodyBytes.drop 76 := by
    rw [show 75 = 69 + 6 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem bdec76 :
    decodeAt bodyBytes 76 = some ({ op := .SSTORE }, 77) := by
  have h : bodyBytes.drop 76 = Opcode.toByte .SSTORE :: bodyBytes.drop 77 := by
    rw [show 76 = 69 + 7 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_sstore_head _)

theorem bdec77 :
    decodeAt bodyBytes 77 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 79) := by
  have hdrop : bodyBytes.drop 77 = 0x60 :: 1 :: bodyBytes.drop 79 := by
    rw [show 77 = 69 + 8 from rfl, drop_add, body_drop69]; rfl
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (1 : UInt8) (bodyBytes.drop 79))
  simpa [wrap] using h

theorem bdec79 :
    decodeAt bodyBytes 79 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 80) := by
  have h : bodyBytes.drop 79 = 0x5f :: bodyBytes.drop 80 := by
    rw [show 79 = 69 + 10 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem bdec80 :
    decodeAt bodyBytes 80 = some ({ op := .MSTORE }, 81) := by
  have h : bodyBytes.drop 80 = Opcode.toByte .MSTORE :: bodyBytes.drop 81 := by
    rw [show 80 = 69 + 11 from rfl, drop_add, body_drop69]; rfl
  exact decodeAt_of_drop h (decodeAt_mstore_head _)

theorem bdec81 :
    decodeAt bodyBytes 81 = some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 114) := by
  have h := decodeAt_of_drop body_drop81 (decodeAt_push32 incTopic _)
  simpa using h

theorem bdec114 :
    decodeAt bodyBytes 114 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 116) := by
  have h114 : bodyBytes.drop 114 = [0x60, 0x20, 0x5f, 0xa1, 0x00] := by
    rw [show 114 = 81 + 33 from rfl, drop_add, body_drop81]
    rw [List.drop_left' (emitPush32_length incTopic)]
  have h116 : bodyBytes.drop 116 = [0x5f, 0xa1, 0x00] := by
    rw [show 116 = 81 + 35 from rfl, drop_add, body_drop81]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  have hdrop : bodyBytes.drop 114 = 0x60 :: 0x20 :: bodyBytes.drop 116 := by
    rw [h114, h116]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0x20 : UInt8) (bodyBytes.drop 116))
  simpa [wrap] using h

theorem bdec116 :
    decodeAt bodyBytes 116 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 117) := by
  have h : bodyBytes.drop 116 = 0x5f :: bodyBytes.drop 117 := by
    rw [show 116 = 81 + 35 from rfl, drop_add, body_drop81]
    rw [show 35 = 33 + 2 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem bdec117 :
    decodeAt bodyBytes 117 = some ({ op := .LOG ⟨1, by decide⟩ }, 118) := by
  have h : bodyBytes.drop 117 = 0xa1 :: bodyBytes.drop 118 := by
    rw [show 117 = 81 + 36 from rfl, drop_add, body_drop81]
    rw [show 36 = 33 + 3 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_log1_head _)

theorem bdec118 :
    decodeAt bodyBytes 118 = some ({ op := .STOP }, 119) := by
  have h : bodyBytes.drop 118 = 0x00 :: bodyBytes.drop 119 := by
    rw [show 118 = 81 + 37 from rfl, drop_add, body_drop81]
    rw [show 37 = 33 + 4 from rfl, drop_add]
    rw [List.drop_left' (emitPush32_length incTopic)]
    rfl
  exact decodeAt_of_drop h (decodeAt_stop_head _)

theorem decode_body (sel : Nat) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt bodyBytes pc = some (instr, next0)) :
    decodeAt (code sel) ((bodyPre sel).length + pc) =
      some (instr, next0 + (bodyPre sel).length) := by
  rw [code_bodyPre, decodeAt_append, hd]
  rfl

theorem isJumpDest_ok (sel : Nat) : isJumpDest (code sel) bodyOkPc = true := by
  have h := isJumpDest_of_decode (decode_body sel bdec68)
  simpa [bodyOkPc] using h

theorem decode_at (sel : Nat) {pc next0 : Nat} {instr : Instr}
    (hd : decodeAt bodyBytes pc = some (instr, next0)) :
    decodeAt (code sel) (68 + pc) = some (instr, next0 + 68) := by
  have h := decode_body sel hd
  simpa [bodyPre_length] using h

def env (sel : Nat) (args : List Nat) : Env :=
  { code := code sel, calldata := packCall sel args, address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

abbrev mem1 (n : Nat) : Mem := memStore (st0 n).mem localBase n
abbrev mem2 (n : Nat) (v : Nat) : Mem := memStore (mem1 n) (localBase + 32) v
abbrev mem3 (n : Nat) (v : Nat) : Mem := memStore (mem2 n v) 0 1
abbrev stor1 (n : Nat) : EVM.Storage := fun k => if k = 0 then n + 1 else (st0 n).storage k
abbrev log1 (n v : Nat) : List Log :=
  [{ topics := [wrap incTopic]
     data := (List.range 32).map fun i => memGet (mem3 n v) (0 + i) }]

/-- Matching selector: STOP with storage slot 0 equal to `n + 1` (no overflow). -/
theorem incOnly_hit (sel : Nat) (n : Nat) (h : n + 1 < wordBound) :
    (match run 50 (env sel []) (st0 n) with
    | some (Halt.stop, s) => s.storage 0 = n + 1
    | _ => False) := by
  have hn : n < wordBound := Nat.lt_of_succ_lt h
  have hwrap : wrap n = n := Nat.mod_eq_of_lt hn
  have hadd : addW (wrap n) 1 = n + 1 := by rw [hwrap]; exact addW_succ_of_lt h
  have hval : wrap (addW (wrap n) 1) = n + 1 := by rw [hadd]; exact Nat.mod_eq_of_lt h
  let e := env sel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have hs := step_push e (st0 n) 4 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using hs
  rw [run_of_next 49 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have hs := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 48 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have hs := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at hs
    exact hs
  rw [run_of_next 47 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [GetContract.revPc, 0], pc := 7 } := by
    have hs := step_push e { st0 n with stack := [0], pc := 4 } GetContract.revPc (decode_pc4 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 46 e _ _ s4]
  have s7 : step e { st0 n with stack := [GetContract.revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have hs := step_jumpi_zero e { st0 n with stack := [GetContract.revPc, 0], pc := 7 }
      GetContract.revPc [] (decode_pc7 sel) rfl
    simpa using hs
  rw [run_of_next 45 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have hs := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 sel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 44 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } := by
    have hs := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using hs
  rw [run_of_next 43 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } := by
    have hs := step_push e
      { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } 0xE0 (decode_pc10 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 42 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } := by
    have hs := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall sel []) 0) [] (decode_pc12 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 41 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)],
            pc := 18 } := by
    have hs := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 }
      (sel % 2 ^ 32) (decode_pc13 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 40 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [1], pc := 19 } := by
    have hs := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall sel []) 0)) []
      (decode_pc18 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at hs ⊢
    exact hs
  rw [run_of_next 39 e _ _ s18]
  have s19 : step e { st0 n with stack := [1], pc := 19 } =
      StepResult.next { st0 n with stack := [incPc, 1], pc := 22 } := by
    have hs := step_push e { st0 n with stack := [1], pc := 19 } incPc (decode_pc19 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 38 e _ _ s19]
  have s22 : step e { st0 n with stack := [incPc, 1], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := incPc } := by
    have hs := step_jumpi_nz e { st0 n with stack := [incPc, 1], pc := 22 } incPc 1 []
      (decode_pc22 sel) rfl (by decide) (isJumpDest_inc sel)
    simpa [env] using hs
  rw [run_of_next 37 e _ _ s22]
  have s67 : step e { st0 n with stack := [], pc := incPc } =
      StepResult.next { st0 n with stack := [], pc := 68 } := by
    have hdec : decodeAt e.code incPc = some ({ op := .JUMPDEST }, 68) := by
      simpa [env, incPc] using decode_pc67 sel
    exact step_jumpdest e { st0 n with stack := [], pc := incPc } hdec
  rw [run_of_next 36 e _ _ s67]
  have d68 : decodeAt e.code 68 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 69) := by
    simpa [env] using decode_at sel bdec0
  have s68 : step e { st0 n with stack := [], pc := 68 } =
      StepResult.next { st0 n with stack := [0], pc := 69 } := by
    have hs := step_push e { st0 n with stack := [], pc := 68 } 0 d68
      (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 35 e _ _ s68]
  have d69 : decodeAt e.code 69 = some ({ op := .SLOAD }, 70) := by
    simpa [env] using decode_at sel bdec1
  have s69 : step e { st0 n with stack := [0], pc := 69 } =
      StepResult.next { st0 n with stack := [n], pc := 70 } := by
    have hs := step_sload e { st0 n with stack := [0], pc := 69 } 0 [] d69 rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using hs
  rw [run_of_next 34 e _ _ s69]
  have d70 : decodeAt e.code 70 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 72) := by
    simpa [env] using decode_at sel bdec2
  have s70 : step e { st0 n with stack := [n], pc := 70 } =
      StepResult.next { st0 n with stack := [localBase, n], pc := 72 } := by
    have hs := step_push e { st0 n with stack := [n], pc := 70 } localBase d70
      (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 33 e _ _ s70]
  have d72 : decodeAt e.code 72 = some ({ op := .MSTORE }, 73) := by
    simpa [env] using decode_at sel bdec4
  have s72 : step e { st0 n with stack := [localBase, n], pc := 72 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [], pc := 73 } :=
    step_mstore e { st0 n with stack := [localBase, n], pc := 72 } localBase n [] d72 rfl
  rw [run_of_next 32 e _ _ s72]
  have d73 : decodeAt e.code 73 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase }, 75) := by
    simpa [env] using decode_at sel bdec5
  have s73 : step e { st0 n with mem := mem1 n, stack := [], pc := 73 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase], pc := 75 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [], pc := 73 }
      localBase d73 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 31 e _ _ s73]
  have d75 : decodeAt e.code 75 = some ({ op := .MLOAD }, 76) := by
    simpa [env] using decode_at sel bdec7
  have s75 : step e { st0 n with mem := mem1 n, stack := [localBase], pc := 75 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 } := by
    have hs := step_mload e { st0 n with mem := mem1 n, stack := [localBase], pc := 75 }
      localBase [] d75 rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [IncBody.memLoad_memStore] using hs
  rw [run_of_next 30 e _ _ s75]
  have d76 : decodeAt e.code 76 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 78) := by
    simpa [env] using decode_at sel bdec8
  have s76 : step e { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [wrap n], pc := 76 }
      1 d76 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 29 e _ _ s76]
  have d78 : decodeAt e.code 78 = some ({ op := .DUP ⟨1, by decide⟩ }, 79) := by
    simpa [env] using decode_at sel bdec10
  have s78 : step e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 } := by
    have hs := step_dup2 e { st0 n with mem := mem1 n, stack := [1, wrap n], pc := 78 }
      1 (wrap n) [] d78 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 28 e _ _ s78]
  have d79 : decodeAt e.code 79 = some ({ op := .ADD }, 80) := by
    simpa [env] using decode_at sel bdec11
  have s79 : step e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 } := by
    have hs := step_add e { st0 n with mem := mem1 n, stack := [wrap n, 1, wrap n], pc := 79 }
      (wrap n) 1 [wrap n] d79 rfl (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 27 e _ _ s79]
  have d80 : decodeAt e.code 80 = some ({ op := .DUP ⟨0, by decide⟩ }, 81) := by
    simpa [env] using decode_at sel bdec12
  have s80 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 } := by
    have hs := step_dup1 e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, wrap n], pc := 80 }
      (addW (wrap n) 1) [wrap n] d80 rfl (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 26 e _ _ s80]
  have d81 : decodeAt e.code 81 = some ({ op := .SWAP ⟨1, by decide⟩ }, 82) := by
    simpa [env] using decode_at sel bdec13
  have s81 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 } := by
    have hs := step_swap2 e
      { st0 n with mem := mem1 n, stack := [addW (wrap n) 1, addW (wrap n) 1, wrap n], pc := 81 }
      (addW (wrap n) 1) (addW (wrap n) 1) (wrap n) [] d81 rfl
    simpa using hs
  rw [run_of_next 25 e _ _ s81]
  have d82 : decodeAt e.code 82 = some ({ op := .GT }, 83) := by
    simpa [env] using decode_at sel bdec14
  have s82 : step e { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 83 } := by
    have hs := step_gt e
      { st0 n with mem := mem1 n, stack := [wrap n, addW (wrap n) 1, addW (wrap n) 1], pc := 82 }
      (wrap n) (addW (wrap n) 1) [addW (wrap n) 1] d82 rfl
      (list_length_lt_1024 (k := 1) rfl)
    have hgt : gtW (wrap n) (addW (wrap n) 1) = 0 := by
      rw [hwrap]; exact gtW_add_no_overflow h
    simp only [hgt] at hs
    exact hs
  rw [run_of_next 24 e _ _ s82]
  have d83 : decodeAt e.code 83 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyRevPc }, 86) := by
    simpa [env] using decode_at sel bdec15
  have s83 : step e { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 83 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 86 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [0, addW (wrap n) 1], pc := 83 }
      bodyRevPc d83 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 23 e _ _ s83]
  have d86 : decodeAt e.code 86 = some ({ op := .JUMPI }, 87) := by
    simpa [env] using decode_at sel bdec18
  have s86 : step e { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 86 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 87 } := by
    have hs := step_jumpi_zero e
      { st0 n with mem := mem1 n, stack := [bodyRevPc, 0, addW (wrap n) 1], pc := 86 }
      bodyRevPc [addW (wrap n) 1] d86 rfl
    simpa using hs
  rw [run_of_next 22 e _ _ s86]
  have d87 : decodeAt e.code 87 = some ({ op := .PUSH ⟨2, by decide⟩, imm := bodyOkPc }, 90) := by
    simpa [env] using decode_at sel bdec19
  have s87 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 87 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 90 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 87 }
      bodyOkPc d87 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 21 e _ _ s87]
  have d90 : decodeAt e.code 90 = some ({ op := .JUMP }, 91) := by
    simpa [env] using decode_at sel bdec22
  have s90 : step e { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 90 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } := by
    have hs := step_jump e { st0 n with mem := mem1 n, stack := [bodyOkPc, addW (wrap n) 1], pc := 90 }
      bodyOkPc [addW (wrap n) 1] d90 rfl (isJumpDest_ok sel)
    simpa [env] using hs
  rw [run_of_next 20 e _ _ s90]
  have d136 : decodeAt e.code bodyOkPc = some ({ op := .JUMPDEST }, 137) := by
    simpa [env, bodyOkPc] using decode_at sel bdec68
  have s136 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } =
      StepResult.next { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 137 } :=
    step_jumpdest e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := bodyOkPc } d136
  rw [run_of_next 19 e _ _ s136]
  have d137 : decodeAt e.code 137 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 139) := by
    simpa [env] using decode_at sel bdec69
  have s137 : step e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 137 } =
      StepResult.next { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 139 } := by
    have hs := step_push e { st0 n with mem := mem1 n, stack := [addW (wrap n) 1], pc := 137 }
      (localBase + 32) d137 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 18 e _ _ s137]
  have d139 : decodeAt e.code 139 = some ({ op := .MSTORE }, 140) := by
    simpa [env] using decode_at sel bdec71
  have s139 : step e { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 139 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 140 } :=
    step_mstore e { st0 n with mem := mem1 n, stack := [localBase + 32, addW (wrap n) 1], pc := 139 }
      (localBase + 32) (addW (wrap n) 1) [] d139 rfl
  rw [run_of_next 17 e _ _ s139]
  have d140 : decodeAt e.code 140 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := localBase + 32 }, 142) := by
    simpa [env] using decode_at sel bdec72
  have s140 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 140 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 142 } := by
    have hs := step_push e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [], pc := 140 }
      (localBase + 32) d140 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 16 e _ _ s140]
  have d142 : decodeAt e.code 142 = some ({ op := .MLOAD }, 143) := by
    simpa [env] using decode_at sel bdec74
  have s142 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 142 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 143 } := by
    have hs := step_mload e
      { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [localBase + 32], pc := 142 }
      (localBase + 32) [] d142 rfl (list_length_lt_1024 (k := 0) rfl)
    simp only [IncBody.memLoad_memStore] at hs
    rw [hval] at hs
    exact hs
  rw [run_of_next 15 e _ _ s142]
  have d143 : decodeAt e.code 143 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 144) := by
    simpa [env] using decode_at sel bdec75
  have s143 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 143 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 144 } := by
    have hs := step_push e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [n + 1], pc := 143 }
      0 d143 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 14 e _ _ s143]
  have d144 : decodeAt e.code 144 = some ({ op := .SSTORE }, 145) := by
    simpa [env] using decode_at sel bdec76
  have s144 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 144 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 145 } :=
    step_sstore e { st0 n with mem := mem2 n (addW (wrap n) 1), stack := [0, n + 1], pc := 144 }
      0 (n + 1) [] d144 rfl
  rw [run_of_next 13 e _ _ s144]
  have d145 : decodeAt e.code 145 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 1 }, 147) := by
    simpa [env] using decode_at sel bdec77
  have s145 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 145 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 147 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 145 }
      1 d145 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 12 e _ _ s145]
  have d147 : decodeAt e.code 147 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 148) := by
    simpa [env] using decode_at sel bdec79
  have s147 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 147 } =
      StepResult.next { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 148 } := by
    have hs := step_push e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [1], pc := 147 }
      0 d147 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 11 e _ _ s147]
  have d148 : decodeAt e.code 148 = some ({ op := .MSTORE }, 149) := by
    simpa [env] using decode_at sel bdec80
  have s148 : step e { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 148 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 149 } :=
    step_mstore e
      { st0 n with mem := mem2 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 1], pc := 148 }
      0 1 [] d148 rfl
  rw [run_of_next 10 e _ _ s148]
  have d149 : decodeAt e.code 149 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap incTopic }, 182) := by
    simpa [env] using decode_at sel bdec81
  have s149 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 149 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 182 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [], pc := 149 }
      (wrap incTopic) d149 (list_length_lt_1024 (k := 0) rfl)
    simpa using hs
  rw [run_of_next 9 e _ _ s149]
  have d182 : decodeAt e.code 182 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 184) := by
    simpa [env] using decode_at sel bdec114
  have s182 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 182 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 184 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [wrap incTopic], pc := 182 }
      32 d182 (list_length_lt_1024 (k := 1) rfl)
    simpa using hs
  rw [run_of_next 8 e _ _ s182]
  have d184 : decodeAt e.code 184 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 185) := by
    simpa [env] using decode_at sel bdec116
  have s184 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 184 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 185 } := by
    have hs := step_push e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [32, wrap incTopic], pc := 184 }
      0 d184 (list_length_lt_1024 (k := 2) rfl)
    simpa using hs
  rw [run_of_next 7 e _ _ s184]
  have d185 : decodeAt e.code 185 = some ({ op := .LOG ⟨1, by decide⟩ }, 186) := by
    simpa [env] using decode_at sel bdec117
  have s185 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 185 } =
      StepResult.next { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 186 } := by
    have hs := step_log1 e
      { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, stack := [0, 32, wrap incTopic], pc := 185 }
      0 32 (wrap incTopic) [] d185 rfl
    simpa [log1] using hs
  rw [run_of_next 6 e _ _ s185]
  have d186 : decodeAt e.code 186 = some ({ op := .STOP }, 187) := by
    simpa [env] using decode_at sel bdec118
  have s186 : step e { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 186 } =
      StepResult.halt Halt.stop { st0 n with mem := mem3 n (addW (wrap n) 1), storage := stor1 n, logs := log1 n (addW (wrap n) 1), stack := [], pc := 186 } :=
    step_stop e _ d186
  rw [run_of_halt 5 e _ _ _ s186]
  simp [stor1]

end Lsc3.Compile.IncContract
