import Lsc3.Core
import Lsc3.Contract
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Contract
import Lsc3.Compile.GetBody
import Lsc3.Compile.GetContract
import Lsc3.Compile.IncBody
import Lsc3.Compile.IncContract
import Lsc3.Compile.DispatchGet
import Lsc3.Compile.Jump

/-!
# Compiler `get` + `increment` — two functions, production encoding

Dispatcher: calldata check, get branch, increment branch, fallthrough revert.
`get` body is position-independent (`GetBody`). `increment` is `IncContract.bodyInstrs`
shifted to PC `incPc + 1`; checked-add destinations are that base plus the isolated
body's local PCs (`bodyRevPc_eq`, `lookup_addR_relocate`).
-/

namespace Lsc3.Compile.GetInc

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Codegen
open Lsc3.Compile.Jump
open Lsc3.Compile.GetContract (revLbl invalidSel)
open Lsc3.Compile.DispatchGet (push4Bytes decodeAt_push4)
open Lsc3.Compile.IncContract (addR addO incFn incEvents incTopic tailInstrs tailBytes
  checkedAddInstrs bodyInstrs)

def getInc : ContractDef where
  name := "GetInc"
  fields := [{ name := "count", kind := .scalar, ty := .uint256 }]
  functions := [GetContract.getFn, incFn]
  ctor := none
  events := incEvents
  errors := []

def revPc : Nat := 42
def getPc : Nat := 82
def incPc : Nat := 91
def bodyRevPc : Nat := 115
def bodyOkPc : Nat := 160

theorem getPc_eq_dispatch : getPc = dispatchByteSize 2 := rfl
theorem incPc_eq_after_get : incPc = getPc + 1 + 8 := rfl
theorem bodyRevPc_eq : bodyRevPc = incPc + 1 + IncBody.revPc := rfl
theorem bodyOkPc_eq : bodyOkPc = incPc + 1 + IncBody.okPc := rfl

abbrev checkInstrs : List Asm := GetContract.checkInstrs
abbrev fallInstrs : List Asm := GetContract.fallInstrs

def branchGet (sel : Nat) : List Asm :=
  loadSelector ++ [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "get"]

def branchInc (sel : Nat) : List Asm :=
  loadSelector ++ [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "increment"]

def expectedInstrs (getSel incSel : Nat) : List Asm :=
  checkInstrs ++ branchGet getSel ++ branchInc incSel ++ fallInstrs ++
    [Asm.jumpDest revLbl] ++ emitRevert invalidSel ++
    [Asm.jumpDest "get"] ++ GetContract.bodyInstrs ++
    [Asm.jumpDest "increment"] ++ bodyInstrs

/-- Prefix of `expectedInstrs` before the increment body (ends at the `increment` JUMPDEST). -/
def expectedPre (getSel incSel : Nat) : List Asm :=
  checkInstrs ++ branchGet getSel ++ branchInc incSel ++ fallInstrs ++
    [Asm.jumpDest revLbl] ++ emitRevert invalidSel ++
    [Asm.jumpDest "get"] ++ GetContract.bodyInstrs ++
    [Asm.jumpDest "increment"]

set_option maxRecDepth 20000 in
theorem labels_expected (getSel incSel : Nat) :
    layoutLabels (expectedInstrs getSel incSel) =
      [(addO, bodyOkPc), (addR, bodyRevPc), ("increment", incPc), ("get", getPc),
        (revLbl, revPc)] :=
  rfl

theorem lookup_rev (getSel incSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs getSel incSel)) revLbl = .ok revPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_get (getSel incSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs getSel incSel)) "get" = .ok getPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_inc (getSel incSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs getSel incSel)) "increment" = .ok incPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_addR (getSel incSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs getSel incSel)) addR = .ok bodyRevPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem lookup_addO (getSel incSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs getSel incSel)) addO = .ok bodyOkPc := by
  simp [labels_expected, lookupLabel, addR, addO, revLbl]

theorem expected_pre_append (gSel iSel : Nat) :
    expectedInstrs gSel iSel = expectedPre gSel iSel ++ bodyInstrs := by
  simp [expectedInstrs, expectedPre]

theorem checkInstrs_size : asmListSize checkInstrs = 8 := rfl
theorem branchGet_size (sel : Nat) : asmListSize (branchGet sel) = 15 := rfl
theorem branchInc_size (sel : Nat) : asmListSize (branchInc sel) = 15 := rfl
theorem fallInstrs_size : asmListSize fallInstrs = 4 := rfl
theorem jumpDest_size (lbl : String) : asmListSize [Asm.jumpDest lbl] = 1 := rfl

theorem expectedPre_size (gSel iSel : Nat) :
    asmListSize (expectedPre gSel iSel) = incPc + 1 := by
  simp only [expectedPre, asmListSize_append, checkInstrs_size, branchGet_size,
    branchInc_size, fallInstrs_size, jumpDest_size, GetContract.bodyInstrs_size,
    asmListSize_emitRevert]
  simp [incPc]

theorem addR_local :
    lookupLabel (layoutLabels bodyInstrs) addR = .ok IncBody.revPc :=
  rfl

theorem addO_local :
    lookupLabel (layoutLabels bodyInstrs) addO = .ok IncBody.okPc :=
  rfl

/-- Relocate the increment body's overflow JUMPDEST: local PC + placement. -/
theorem lookup_addR_at (base : Nat) :
    lookupLabel (layoutLabelsFrom base bodyInstrs []) addR = .ok (base + IncBody.revPc) := by
  rw [layoutLabelsFrom_offset, lookupLabel_shift, addR_local]
  simp [Nat.add_comm]

/-- Same destination as `lookup_addR`, derived from layout rather than a magic numeral. -/
theorem lookup_addR_relocate (gSel iSel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs gSel iSel)) addR =
      .ok (incPc + 1 + IncBody.revPc) := by
  rw [expected_pre_append, layoutLabels, layoutLabelsFrom_append, Nat.zero_add,
    expectedPre_size, layoutLabelsFrom_acc]
  apply lookupLabel_append_ok
  exact lookup_addR_at (incPc + 1)

theorem dup_expected (getSel incSel : Nat) :
    checkDuplicateLabels (expectedInstrs getSel incSel) = .ok () :=
  rfl

theorem revPc_lt : revPc < jumpImmBound := by decide
theorem getPc_lt : getPc < jumpImmBound := by decide
theorem incPc_lt : incPc < jumpImmBound := by decide
theorem bodyRevPc_lt : bodyRevPc < jumpImmBound := by decide
theorem bodyOkPc_lt : bodyOkPc < jumpImmBound := by decide
theorem revPc_mod : revPc % 2 ^ 16 = revPc := Nat.mod_eq_of_lt (by decide)
theorem getPc_mod : getPc % 2 ^ 16 = getPc := Nat.mod_eq_of_lt (by decide)
theorem incPc_mod : incPc % 2 ^ 16 = incPc := Nat.mod_eq_of_lt (by decide)
theorem bodyRevPc_mod : bodyRevPc % 2 ^ 16 = bodyRevPc := Nat.mod_eq_of_lt (by decide)
theorem bodyOkPc_mod : bodyOkPc % 2 ^ 16 = bodyOkPc := Nat.mod_eq_of_lt (by decide)

def checkBytes : List UInt8 :=
  [0x60, 4, 0x36, 0x10] ++ emitPush2 revPc ++ [Opcode.toByte .JUMPI]

abbrev loadSelBytes : List UInt8 := GetContract.loadSelBytes
abbrev revertBytes : List UInt8 := GetContract.revertBytes

def branchGetBytes (sel : Nat) : List UInt8 :=
  loadSelBytes ++ emitPush4 sel ++ [Opcode.toByte .EQ] ++
    emitPush2 getPc ++ [Opcode.toByte .JUMPI]

def branchIncBytes (sel : Nat) : List UInt8 :=
  loadSelBytes ++ emitPush4 sel ++ [Opcode.toByte .EQ] ++
    emitPush2 incPc ++ [Opcode.toByte .JUMPI]

def fallBytes : List UInt8 :=
  emitPush2 revPc ++ [Opcode.toByte .JUMP]

def checkedAddBytes : List UInt8 :=
  [0x81, 0x01, 0x80, 0x91, 0x11] ++
    emitPush2 bodyRevPc ++ [Opcode.toByte .JUMPI] ++
    emitPush2 bodyOkPc ++ [Opcode.toByte .JUMP] ++
    [Opcode.toByte .JUMPDEST] ++ IncBody.panicBytes ++ [Opcode.toByte .JUMPDEST]

def bodyBytes : List UInt8 :=
  IncBody.prefixBytes ++ checkedAddBytes ++ tailBytes

def code (getSel incSel : Nat) : List UInt8 :=
  checkBytes ++ branchGetBytes getSel ++ branchIncBytes incSel ++ fallBytes ++
    [Opcode.toByte .JUMPDEST] ++ revertBytes ++
    [Opcode.toByte .JUMPDEST] ++ GetBody.code ++
    [Opcode.toByte .JUMPDEST] ++ bodyBytes

@[simp] theorem checkBytes_length : checkBytes.length = 8 := by
  simp [checkBytes, emitPush2, natToBytesBE_length]

@[simp] theorem branchGetBytes_length (sel : Nat) : (branchGetBytes sel).length = 15 := by
  simp [branchGetBytes, emitPush2, emitPush4, natToBytesBE_length]

@[simp] theorem branchIncBytes_length (sel : Nat) : (branchIncBytes sel).length = 15 := by
  simp [branchIncBytes, emitPush2, emitPush4, natToBytesBE_length]

@[simp] theorem fallBytes_length : fallBytes.length = 4 := by
  simp [fallBytes, emitPush2, natToBytesBE_length]

@[simp] theorem getBody_code_length : GetBody.code.length = 8 := rfl

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

theorem emit_checkInstrs (labels : List (String × Nat))
    (h : lookupLabel labels revLbl = .ok revPc) :
    emitInstrs labels checkInstrs = .ok checkBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.jumpi revLbl] =
      .ok (emitPush2 revPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels revLbl h revPc_lt) t0
  have t2 : emitInstrs labels [Asm.op .LT, Asm.jumpi revLbl] =
      .ok ([Opcode.toByte .LT] ++ emitPush2 revPc ++ [Opcode.toByte .JUMPI]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .LT) t1
  have t3 : emitInstrs labels [Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl] =
      .ok ([Opcode.toByte .CALLDATASIZE, Opcode.toByte .LT] ++
        emitPush2 revPc ++ [Opcode.toByte .JUMPI]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .CALLDATASIZE) t2
  have t4 := emit_cons_ok (emitOne_push labels 4) t3
  simpa [checkInstrs, GetContract.checkInstrs, checkBytes, emitPush_four, List.append_assoc] using t4

theorem emit_fallInstrs (labels : List (String × Nat))
    (h : lookupLabel labels revLbl = .ok revPc) :
    emitInstrs labels fallInstrs = .ok fallBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 := emit_cons_ok (emitOne_jump labels revLbl h revPc_lt) t0
  simpa [fallInstrs, GetContract.fallInstrs, fallBytes] using t1

theorem emit_branchGetTail (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "get" = .ok getPc) :
    emitInstrs labels [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "get"] =
      .ok (emitPush4 sel ++ [Opcode.toByte .EQ] ++ emitPush2 getPc ++ [Opcode.toByte .JUMPI]) := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.jumpi "get"] =
      .ok (emitPush2 getPc ++ [Opcode.toByte .JUMPI]) := by
    simpa using emit_cons_ok (emitOne_jumpi labels "get" h getPc_lt) t0
  have t2 : emitInstrs labels [Asm.op .EQ, Asm.jumpi "get"] =
      .ok ([Opcode.toByte .EQ] ++ emitPush2 getPc ++ [Opcode.toByte .JUMPI]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .EQ) t1
  have t3 := emit_cons_ok (emitOne_push4 labels sel) t2
  simpa [List.append_assoc] using t3

theorem emit_branchGet (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "get" = .ok getPc) :
    emitInstrs labels (branchGet sel) = .ok (branchGetBytes sel) := by
  have h1 := emit_bind_ok (GetContract.emit_loadSelector labels) (emit_branchGetTail labels sel h)
  simpa [branchGet, branchGetBytes, List.append_assoc] using h1

theorem emit_branchIncTail (labels : List (String × Nat)) (sel : Nat)
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

theorem emit_branchInc (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "increment" = .ok incPc) :
    emitInstrs labels (branchInc sel) = .ok (branchIncBytes sel) := by
  have h1 := emit_bind_ok (GetContract.emit_loadSelector labels) (emit_branchIncTail labels sel h)
  simpa [branchInc, branchIncBytes, List.append_assoc] using h1

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
  simpa [checkedAddInstrs, IncContract.checkedAddInstrs, checkedAddBytes, IncBody.panicBytes,
    List.append_assoc] using h8

theorem emit_incBody (labels : List (String × Nat))
    (hR : lookupLabel labels addR = .ok bodyRevPc)
    (hO : lookupLabel labels addO = .ok bodyOkPc) :
    emitInstrs labels bodyInstrs = .ok bodyBytes := by
  have h := emit_bind_ok
    (emit_bind_ok (IncBody.emit_prefix labels) (emit_checkedAdd labels hR hO))
    (IncContract.emit_tail labels)
  simpa [IncContract.bodyInstrs_split, bodyBytes, List.append_assoc] using h

theorem emit_expected (getSel incSel : Nat) :
    emitInstrs (layoutLabels (expectedInstrs getSel incSel)) (expectedInstrs getSel incSel) =
      .ok (code getSel incSel) := by
  set L := layoutLabels (expectedInstrs getSel incSel)
  have hrev : lookupLabel L revLbl = .ok revPc := lookup_rev getSel incSel
  have hget : lookupLabel L "get" = .ok getPc := lookup_get getSel incSel
  have hinc : lookupLabel L "increment" = .ok incPc := lookup_inc getSel incSel
  have hR : lookupLabel L addR = .ok bodyRevPc := lookup_addR getSel incSel
  have hO : lookupLabel L addO = .ok bodyOkPc := lookup_addO getSel incSel
  have h8 :=
    emit_bind_ok
      (emit_bind_ok
        (emit_bind_ok
          (emit_bind_ok
            (emit_bind_ok
              (emit_bind_ok
                (emit_bind_ok
                  (emit_bind_ok (emit_checkInstrs L hrev) (emit_branchGet L getSel hget))
                  (emit_branchInc L incSel hinc))
                (emit_fallInstrs L hrev))
              (GetContract.emit_jumpDest L revLbl))
            (GetContract.emit_revertInstrs L))
          (GetContract.emit_jumpDest L "get"))
        (GetContract.emit_bodyInstrs L))
      (emit_bind_ok (GetContract.emit_jumpDest L "increment") (emit_incBody L hR hO))
  simpa [expectedInstrs, code, List.append_assoc] using h8

theorem encode_expected (getSel incSel : Nat) :
    encode (expectedInstrs getSel incSel) = .ok (code getSel incSel) := by
  simp only [encode, dup_expected, bind, Except.bind]
  exact emit_expected getSel incSel

set_option maxRecDepth 40000 in
theorem getInc_instrs :
    contractInstrs getInc =
      .ok (expectedInstrs (FnDef.selector GetContract.getFn) (FnDef.selector incFn)) :=
  rfl

theorem compile_getInc :
    compileContract getInc =
      .ok (code (FnDef.selector GetContract.getFn) (FnDef.selector incFn)) := by
  simp only [compileContract, getInc_instrs, bind, Except.bind]
  exact encode_expected (FnDef.selector GetContract.getFn) (FnDef.selector incFn)

end Lsc3.Compile.GetInc
