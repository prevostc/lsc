import Lsc3.Core
import Lsc3.Contract
import Lsc3.EVM.Lemmas
import Lsc3.Compile.Contract
import Lsc3.Compile.GetBody
import Lsc3.Compile.Jump
import Lsc3.Compile.DispatchGet

/-!
# Compiler `get` — one function, production encoding

Jumps are `PUSH2`, selectors `PUSH4`, revert words `PUSH32`. Layout does not depend
on Keccak. `contractInstrs` of this contract is the assembly below (by `rfl`).
Machine execution of the encoded bytes is certified for a matching selector.
-/

namespace Lsc3.Compile.GetContract

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec Lsc3.Compile.Codegen
open Lsc3.Compile.Jump
open Lsc3.Compile.DispatchGet (push4Bytes decodeAt_push4)

def getFn : FnDef where
  name := "get"
  decl := .anonymous
  kind := .view
  params := []
  ret := .word
  core := .opTail (.load 0)

def getOnly : ContractDef where
  name := "Get"
  fields := [{ name := "count", kind := .scalar, ty := .uint256 }]
  functions := [getFn]
  ctor := none
  events := []
  errors := []

def revLbl : String := "dispR0"
def invalidSel : Nat := selectorOf "InvalidSelector" []
def revPc : Nat := 27
def getPc : Nat := 67

theorem getPc_eq_dispatch : getPc = dispatchByteSize 1 := rfl

def checkInstrs : List Asm :=
  [Asm.push 4, Asm.op .CALLDATASIZE, Asm.op .LT, Asm.jumpi revLbl]

def branchInstrs (sel : Nat) : List Asm :=
  loadSelector ++ [Asm.push4 sel, Asm.op .EQ, Asm.jumpi "get"]

def fallInstrs : List Asm := [Asm.jump revLbl]

def bodyInstrs : List Asm :=
  [Asm.push 0, Asm.op .SLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push 32, Asm.push 0, Asm.op .RETURN]

theorem bodyInstrs_size : asmListSize bodyInstrs = 8 := rfl

theorem bodyInstrs_all_no_label :
    bodyInstrs.all (fun i => !i.usesLabel) = true :=
  rfl

def expectedInstrs (sel : Nat) : List Asm :=
  checkInstrs ++ branchInstrs sel ++ fallInstrs ++
    [Asm.jumpDest revLbl] ++ emitRevert invalidSel ++
    [Asm.jumpDest "get"] ++ bodyInstrs

theorem getFn_selector : FnDef.selector getFn = selectorOf "get" [] := rfl

theorem getFn_core : getFn.core = Core.opTail (.load 0) := rfl

/-- The real compiler's assembly for a one-function `get`. -/
theorem getOnly_instrs :
    contractInstrs getOnly = .ok (expectedInstrs (FnDef.selector getFn)) :=
  rfl

/-- Any contract's copy of this `get` function compiles to the same body. -/
theorem genFunction_getFn (c : ContractDef) (ctx : Ctx) :
    genFunction c getFn ctx =
      .ok (bodyInstrs, Ctx.afterFunction (Ctx.forFunction ctx getFn.name 0)) := by
  simp [genFunction, getFn, GetBody.genCore_opTail_load0, GetBody.loadParams_zero, bodyInstrs,
    bind, Except.bind]

theorem labels_expected (sel : Nat) :
    layoutLabels (expectedInstrs sel) = [("get", getPc), (revLbl, revPc)] :=
  rfl

theorem lookup_get (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) "get" = .ok getPc := by
  simp [labels_expected, lookupLabel]

theorem lookup_rev (sel : Nat) :
    lookupLabel (layoutLabels (expectedInstrs sel)) revLbl = .ok revPc := by
  simp [labels_expected, lookupLabel, revLbl]

theorem dup_expected (sel : Nat) :
    checkDuplicateLabels (expectedInstrs sel) = .ok () :=
  rfl

theorem revPc_lt : revPc < jumpImmBound := by decide
theorem getPc_lt : getPc < jumpImmBound := by decide
theorem revPc_mod : revPc % 2 ^ 16 = revPc := Nat.mod_eq_of_lt (by decide)
theorem getPc_mod : getPc % 2 ^ 16 = getPc := Nat.mod_eq_of_lt (by decide)

def checkBytes : List UInt8 :=
  [0x60, 4, 0x36, 0x10] ++ emitPush2 revPc ++ [Opcode.toByte .JUMPI]

def loadSelBytes : List UInt8 := [0x5f, 0x35, 0x60, 0xE0, 0x1c]

def branchBytes (sel : Nat) : List UInt8 :=
  loadSelBytes ++ emitPush4 sel ++ [Opcode.toByte .EQ] ++
    emitPush2 getPc ++ [Opcode.toByte .JUMPI]

def fallBytes : List UInt8 :=
  emitPush2 revPc ++ [Opcode.toByte .JUMP]

def preBytes (sel : Nat) : List UInt8 :=
  checkBytes ++ branchBytes sel ++ fallBytes

def revertBytes : List UInt8 :=
  emitPush32 (invalidSel * 2 ^ 224) ++ [0x5f, 0x52, 0x60, 4, 0x5f, 0xfd]

def code (sel : Nat) : List UInt8 :=
  preBytes sel ++ [Opcode.toByte .JUMPDEST] ++ revertBytes ++
    [Opcode.toByte .JUMPDEST] ++ GetBody.code

@[simp] theorem checkBytes_length : checkBytes.length = 8 := by
  simp [checkBytes, emitPush2, natToBytesBE_length]

@[simp] theorem loadSelBytes_length : loadSelBytes.length = 5 := rfl

@[simp] theorem branchBytes_length (sel : Nat) : (branchBytes sel).length = 15 := by
  simp [branchBytes, emitPush2, emitPush4, natToBytesBE_length]

@[simp] theorem fallBytes_length : fallBytes.length = 4 := by
  simp [fallBytes, emitPush2, natToBytesBE_length]

@[simp] theorem preBytes_length (sel : Nat) : (preBytes sel).length = revPc := by
  simp [preBytes, revPc]

@[simp] theorem revertBytes_length : revertBytes.length = 39 := by
  simp [revertBytes, emitPush32, natToBytesBE_length]

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
  simpa [checkInstrs, checkBytes, emitPush_four, List.append_assoc] using t4

theorem emit_loadSelector (labels : List (String × Nat)) :
    emitInstrs labels loadSelector = .ok loadSelBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .SHR] = .ok [Opcode.toByte .SHR] := by
    simpa using emit_cons_ok (emitOne_op labels .SHR) t0
  have t2 : emitInstrs labels [Asm.push 0xE0, Asm.op .SHR] =
      .ok (emitPush 0xE0 ++ [Opcode.toByte .SHR]) := by
    simpa using emit_cons_ok (emitOne_push labels 0xE0) t1
  have t3 : emitInstrs labels [Asm.op .CALLDATALOAD, Asm.push 0xE0, Asm.op .SHR] =
      .ok ([Opcode.toByte .CALLDATALOAD] ++ emitPush 0xE0 ++ [Opcode.toByte .SHR]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .CALLDATALOAD) t2
  have t4 := emit_cons_ok (emitOne_push labels 0) t3
  simpa [loadSelector, loadSelBytes, emitPush_zero, emitPush_e0, List.append_assoc] using t4

theorem emit_branchTail (labels : List (String × Nat)) (sel : Nat)
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

theorem emit_branchInstrs (labels : List (String × Nat)) (sel : Nat)
    (h : lookupLabel labels "get" = .ok getPc) :
    emitInstrs labels (branchInstrs sel) = .ok (branchBytes sel) := by
  have h1 := emit_bind_ok (emit_loadSelector labels) (emit_branchTail labels sel h)
  simpa [branchInstrs, branchBytes, List.append_assoc] using h1

theorem emit_fallInstrs (labels : List (String × Nat))
    (h : lookupLabel labels revLbl = .ok revPc) :
    emitInstrs labels fallInstrs = .ok fallBytes := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 := emit_cons_ok (emitOne_jump labels revLbl h revPc_lt) t0
  simpa [fallInstrs, fallBytes] using t1

theorem emit_bodyInstrs (labels : List (String × Nat)) :
    emitInstrs labels bodyInstrs = .ok GetBody.code := by
  have t0 : emitInstrs labels ([] : List Asm) = .ok [] := emitInstrs_nil labels
  have t1 : emitInstrs labels [Asm.op .RETURN] = .ok [Opcode.toByte .RETURN] := by
    simpa using emit_cons_ok (emitOne_op labels .RETURN) t0
  have t2 : emitInstrs labels [Asm.push 0, Asm.op .RETURN] =
      .ok (emitPush 0 ++ [Opcode.toByte .RETURN]) := by
    simpa using emit_cons_ok (emitOne_push labels 0) t1
  have t3 : emitInstrs labels [Asm.push 32, Asm.push 0, Asm.op .RETURN] =
      .ok (emitPush 32 ++ emitPush 0 ++ [Opcode.toByte .RETURN]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 32) t2
  have t4 : emitInstrs labels [Asm.op .MSTORE, Asm.push 32, Asm.push 0, Asm.op .RETURN] =
      .ok ([Opcode.toByte .MSTORE] ++ emitPush 32 ++ emitPush 0 ++ [Opcode.toByte .RETURN]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .MSTORE) t3
  have t5 : emitInstrs labels
      [Asm.push 0, Asm.op .MSTORE, Asm.push 32, Asm.push 0, Asm.op .RETURN] =
      .ok (emitPush 0 ++ [Opcode.toByte .MSTORE] ++ emitPush 32 ++ emitPush 0 ++
        [Opcode.toByte .RETURN]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_push labels 0) t4
  have t6 : emitInstrs labels
      [Asm.op .SLOAD, Asm.push 0, Asm.op .MSTORE, Asm.push 32, Asm.push 0, Asm.op .RETURN] =
      .ok ([Opcode.toByte .SLOAD] ++ emitPush 0 ++ [Opcode.toByte .MSTORE] ++
        emitPush 32 ++ emitPush 0 ++ [Opcode.toByte .RETURN]) := by
    simpa [List.append_assoc] using emit_cons_ok (emitOne_op labels .SLOAD) t5
  have t7 := emit_cons_ok (emitOne_push labels 0) t6
  simpa [bodyInstrs, GetBody.code, emitPush_zero, emitPush_thirtyTwo, List.append_assoc] using t7

theorem emit_revertInstrs (labels : List (String × Nat)) :
    emitInstrs labels (emitRevert invalidSel) = .ok revertBytes := by
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
  have t6 := emit_cons_ok (emitOne_push32 labels (invalidSel * 2 ^ 224)) t5
  simpa [emitRevert, revertBytes, emitPush_zero, emitPush_four, List.append_assoc] using t6

theorem emit_jumpDest (labels : List (String × Nat)) (lbl : String) :
    emitInstrs labels [Asm.jumpDest lbl] = .ok [Opcode.toByte .JUMPDEST] := by
  simpa using emit_cons_ok (emitOne_jumpDest labels lbl) (emitInstrs_nil labels)

theorem emit_expected (sel : Nat) :
    emitInstrs (layoutLabels (expectedInstrs sel)) (expectedInstrs sel) = .ok (code sel) := by
  set L := layoutLabels (expectedInstrs sel)
  have hrev : lookupLabel L revLbl = .ok revPc := lookup_rev sel
  have hget : lookupLabel L "get" = .ok getPc := lookup_get sel
  have h6 :=
    emit_bind_ok
      (emit_bind_ok
        (emit_bind_ok
          (emit_bind_ok
            (emit_bind_ok
              (emit_bind_ok (emit_checkInstrs L hrev) (emit_branchInstrs L sel hget))
              (emit_fallInstrs L hrev))
            (emit_jumpDest L revLbl))
          (emit_revertInstrs L))
        (emit_jumpDest L "get"))
      (emit_bodyInstrs L)
  simpa [expectedInstrs, code, preBytes, List.append_assoc] using h6

/-- Encoding of the compiler's `get`-only assembly is exactly `code`. -/
theorem encode_expected (sel : Nat) :
    encode (expectedInstrs sel) = .ok (code sel) := by
  simp only [encode, dup_expected, bind, Except.bind]
  exact emit_expected sel

theorem compile_getOnly :
    compileContract getOnly = .ok (code (FnDef.selector getFn)) := by
  simp only [compileContract, getOnly_instrs, bind, Except.bind]
  exact encode_expected (FnDef.selector getFn)

def env (sel : Nat) (args : List Nat) : Env :=
  { code := code sel, calldata := packCall sel args, address := 0, caller := 0, callvalue := 0,
    timestamp := 0, number := 0 }

def st0 (n : Nat) : State := { storage := fun k => if k = 0 then n else 0 }

private theorem drop_add {α} (l : List α) (n k : Nat) :
    l.drop (n + k) = (l.drop n).drop k :=
  (List.drop_drop (i := k) (j := n) (l := l)).symm

/-- Right-associated spine so `drop_left'` applies at each chunk. -/
theorem code_spine (sel : Nat) :
    code sel =
      checkBytes ++ (loadSelBytes ++ (emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ GetBody.code))))))))) := by
  simp [code, preBytes, branchBytes, List.append_assoc]

theorem code_drop8 (sel : Nat) :
    (code sel).drop 8 =
      loadSelBytes ++ (emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ GetBody.code)))))))) := by
  rw [code_spine, List.drop_left' checkBytes_length]

theorem code_drop13 (sel : Nat) :
    (code sel).drop 13 =
      emitPush4 sel ++ ([Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ GetBody.code))))))) := by
  rw [show 13 = 8 + 5 from rfl, drop_add, code_drop8, List.drop_left' loadSelBytes_length]

theorem code_drop18 (sel : Nat) :
    (code sel).drop 18 =
      [Opcode.toByte .EQ] ++
        (emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
          ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
            ([Opcode.toByte .JUMPDEST] ++ GetBody.code)))))) := by
  rw [show 18 = 13 + 5 from rfl, drop_add, code_drop13, List.drop_left' (emitPush4_length sel)]

theorem code_drop19 (sel : Nat) :
    (code sel).drop 19 =
      emitPush2 getPc ++ ([Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ GetBody.code))))) := by
  rw [show 19 = 18 + 1 from rfl, drop_add, code_drop18]; rfl

theorem code_drop22 (sel : Nat) :
    (code sel).drop 22 =
      [Opcode.toByte .JUMPI] ++ (fallBytes ++
        ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
          ([Opcode.toByte .JUMPDEST] ++ GetBody.code)))) := by
  rw [show 22 = 19 + 3 from rfl, drop_add, code_drop19, List.drop_left' (emitPush2_length getPc)]

theorem code_drop23 (sel : Nat) :
    (code sel).drop 23 =
      fallBytes ++ ([Opcode.toByte .JUMPDEST] ++ (revertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ GetBody.code))) := by
  rw [show 23 = 22 + 1 from rfl, drop_add, code_drop22]; rfl

theorem code_drop27 (sel : Nat) :
    (code sel).drop 27 =
      [Opcode.toByte .JUMPDEST] ++ (revertBytes ++
        ([Opcode.toByte .JUMPDEST] ++ GetBody.code)) := by
  rw [show 27 = 23 + 4 from rfl, drop_add, code_drop23, List.drop_left' fallBytes_length]

theorem code_drop28 (sel : Nat) :
    (code sel).drop 28 =
      revertBytes ++ ([Opcode.toByte .JUMPDEST] ++ GetBody.code) := by
  rw [show 28 = 27 + 1 from rfl, drop_add, code_drop27]; rfl

theorem code_drop67 (sel : Nat) :
    (code sel).drop 67 = [Opcode.toByte .JUMPDEST] ++ GetBody.code := by
  rw [show 67 = 28 + 39 from rfl, drop_add, code_drop28, List.drop_left' revertBytes_length]

theorem code_drop68 (sel : Nat) :
    (code sel).drop 68 = GetBody.code := by
  rw [show 68 = 67 + 1 from rfl, drop_add, code_drop67]; rfl

theorem code_after4 (sel : Nat) :
    code sel =
      [0x60, 4, 0x36, 0x10] ++
        (emitPush2 revPc ++ Opcode.toByte .JUMPI :: (code sel).drop 8) := by
  rw [code_drop8]
  simp [code, preBytes, checkBytes, branchBytes, List.append_assoc]

theorem code_drop4 (sel : Nat) :
    (code sel).drop 4 =
      emitPush2 revPc ++ (Opcode.toByte .JUMPI :: (code sel).drop 8) := by
  rw [code_after4]
  exact List.drop_left' (by decide : ([0x60, 4, 0x36, 0x10] : List UInt8).length = 4)

theorem code_drop7 (sel : Nat) :
    (code sel).drop 7 = Opcode.toByte .JUMPI :: (code sel).drop 8 := by
  rw [show 7 = 4 + 3 from rfl, drop_add, code_drop4]
  exact List.drop_left' (emitPush2_length revPc)

def bodyPre (sel : Nat) : List UInt8 :=
  preBytes sel ++ [Opcode.toByte .JUMPDEST] ++ revertBytes ++ [Opcode.toByte .JUMPDEST]

@[simp] theorem bodyPre_length (sel : Nat) : (bodyPre sel).length = 68 := by
  simp [bodyPre, revPc]

theorem code_bodyPre (sel : Nat) : code sel = bodyPre sel ++ GetBody.code := rfl

theorem emitPush4_eq_push4 (sel : Nat) : emitPush4 sel = push4Bytes sel := rfl

theorem decode_pc0 (sel : Nat) :
    decodeAt (code sel) 0 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 4 }, 2) := by
  have h : (code sel).drop 0 = 0x60 :: 4 :: (code sel).drop 2 := by
    simp [code, preBytes, checkBytes]
  have h' := decodeAt_of_drop h (decodeAt_push1_head (4 : UInt8) ((code sel).drop 2))
  simpa [wrap] using h'

theorem decode_pc2 (sel : Nat) :
    decodeAt (code sel) 2 = some ({ op := .CALLDATASIZE }, 3) := by
  have h : (code sel).drop 2 = Opcode.toByte .CALLDATASIZE :: (code sel).drop 3 := by
    simp [code, preBytes, checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATASIZE _ rfl)

theorem decode_pc3 (sel : Nat) :
    decodeAt (code sel) 3 = some ({ op := .LT }, 4) := by
  have h : (code sel).drop 3 = Opcode.toByte .LT :: (code sel).drop 4 := by
    simp [code, preBytes, checkBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .LT _ rfl)

theorem decode_pc4 (sel : Nat) :
    decodeAt (code sel) 4 = some ({ op := .PUSH ⟨2, by decide⟩, imm := revPc }, 7) := by
  have hdrop : (code sel).drop 4 = emitPush2 revPc ++ (code sel).drop 7 := by
    rw [code_drop4, code_drop7]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 revPc _)
  simpa [revPc_mod] using h

theorem decode_pc7 (sel : Nat) :
    decodeAt (code sel) 7 = some ({ op := .JUMPI }, 8) := by
  have h : (code sel).drop 7 = Opcode.toByte .JUMPI :: (code sel).drop 8 := code_drop7 sel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc8 (sel : Nat) :
    decodeAt (code sel) 8 = some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 9) := by
  have h : (code sel).drop 8 = 0x5f :: (code sel).drop 9 := by
    rw [show 9 = 8 + 1 from rfl, drop_add, code_drop8]
    simp [loadSelBytes]
  exact decodeAt_of_drop h (decodeAt_push0_head _)

theorem decode_pc9 (sel : Nat) :
    decodeAt (code sel) 9 = some ({ op := .CALLDATALOAD }, 10) := by
  have h : (code sel).drop 9 = Opcode.toByte .CALLDATALOAD :: (code sel).drop 10 := by
    rw [show 9 = 8 + 1 from rfl, show 10 = 8 + 2 from rfl, drop_add, drop_add, code_drop8]
    simp [loadSelBytes, Opcode.toByte]
  exact decodeAt_of_drop h (decodeAt_op_head .CALLDATALOAD _ rfl)

theorem decode_pc10 (sel : Nat) :
    decodeAt (code sel) 10 = some ({ op := .PUSH ⟨1, by decide⟩, imm := 0xE0 }, 12) := by
  have hdrop : (code sel).drop 10 = 0x60 :: 0xE0 :: (code sel).drop 12 := by
    rw [show 10 = 8 + 2 from rfl, show 12 = 8 + 4 from rfl, drop_add, drop_add, code_drop8]
    simp [loadSelBytes]
  have h := decodeAt_of_drop hdrop (decodeAt_push1_head (0xE0 : UInt8) ((code sel).drop 12))
  simpa [wrap] using h

theorem decode_pc12 (sel : Nat) :
    decodeAt (code sel) 12 = some ({ op := .SHR }, 13) := by
  have h : (code sel).drop 12 = Opcode.toByte .SHR :: (code sel).drop 13 := by
    rw [show 12 = 8 + 4 from rfl, drop_add, code_drop8, code_drop13]
    simp [loadSelBytes, Opcode.toByte]
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
    decodeAt (code sel) 19 = some ({ op := .PUSH ⟨2, by decide⟩, imm := getPc }, 22) := by
  have hdrop : (code sel).drop 19 = emitPush2 getPc ++ (code sel).drop 22 := by
    rw [code_drop19, code_drop22]
  have h := decodeAt_of_drop hdrop (decodeAt_push2 getPc _)
  simpa [getPc_mod] using h

theorem decode_pc22 (sel : Nat) :
    decodeAt (code sel) 22 = some ({ op := .JUMPI }, 23) := by
  have h : (code sel).drop 22 = Opcode.toByte .JUMPI :: (code sel).drop 23 := code_drop22 sel
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPI _ rfl)

theorem decode_pc67 (sel : Nat) :
    decodeAt (code sel) 67 = some ({ op := .JUMPDEST }, 68) := by
  have h : (code sel).drop 67 = Opcode.toByte .JUMPDEST :: GetBody.code := by
    rw [code_drop67]
    rfl
  exact decodeAt_of_drop h (decodeAt_op_head .JUMPDEST _ rfl)

theorem isJumpDest_get (sel : Nat) : isJumpDest (code sel) getPc = true := by
  simpa [getPc] using isJumpDest_of_decode (decode_pc67 sel)

/-- Matching selector on the compiler's `get`-only bytecode returns storage slot 0. -/
theorem getOnly_hit (sel : Nat) (n : Nat) :
    match run 32 (env sel []) (st0 n) with
    | some (Halt.ret data, _) => decodeWord data = wrap n
    | _ => False := by
  let e := env sel []
  have s0 : step e (st0 n) =
      StepResult.next { st0 n with stack := [4], pc := 2 } := by
    have h := step_push e (st0 n) 4 (decode_pc0 sel)
      (list_length_lt_1024 (k := 0) (by simp [st0]))
    simpa using h
  rw [run_of_next 31 e (st0 n) _ s0]
  have s2 : step e { st0 n with stack := [4], pc := 2 } =
      StepResult.next { st0 n with stack := [e.calldata.length, 4], pc := 3 } := by
    have h := step_calldatasize e { st0 n with stack := [4], pc := 2 } (decode_pc2 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 30 e _ _ s2]
  have s3 : step e { st0 n with stack := [e.calldata.length, 4], pc := 3 } =
      StepResult.next { st0 n with stack := [0], pc := 4 } := by
    have h := step_lt e { st0 n with stack := [e.calldata.length, 4], pc := 3 }
      e.calldata.length 4 [] (decode_pc3 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [ltW] at h
    exact h
  rw [run_of_next 29 e _ _ s3]
  have s4 : step e { st0 n with stack := [0], pc := 4 } =
      StepResult.next { st0 n with stack := [revPc, 0], pc := 7 } := by
    have h := step_push e { st0 n with stack := [0], pc := 4 } revPc (decode_pc4 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 28 e _ _ s4]
  have s7 : step e { st0 n with stack := [revPc, 0], pc := 7 } =
      StepResult.next { st0 n with stack := [], pc := 8 } := by
    have h := step_jumpi_zero e { st0 n with stack := [revPc, 0], pc := 7 } revPc []
      (decode_pc7 sel) rfl
    simpa using h
  rw [run_of_next 27 e _ _ s7]
  have s8 : step e { st0 n with stack := [], pc := 8 } =
      StepResult.next { st0 n with stack := [0], pc := 9 } := by
    have h := step_push e { st0 n with stack := [], pc := 8 } 0 (decode_pc8 sel)
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 26 e _ _ s8]
  have s9 : step e { st0 n with stack := [0], pc := 9 } =
      StepResult.next { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } := by
    have h := step_calldataload e { st0 n with stack := [0], pc := 9 } 0 []
      (decode_pc9 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simpa [env, st0] using h
  rw [run_of_next 25 e _ _ s9]
  have s10 :
      step e { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } =
        StepResult.next
          { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } := by
    have h := step_push e
      { st0 n with stack := [calldataLoad (packCall sel []) 0], pc := 10 } 0xE0 (decode_pc10 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 24 e _ _ s10]
  have s12 :
      step e { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 } =
        StepResult.next
          { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } := by
    have h := step_shr e
      { st0 n with stack := [0xE0, calldataLoad (packCall sel []) 0], pc := 12 }
      0xE0 (calldataLoad (packCall sel []) 0) [] (decode_pc12 sel) rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 23 e _ _ s12]
  have s13 :
      step e { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 } =
        StepResult.next
          { st0 n with
            stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)],
            pc := 18 } := by
    have h := step_push e
      { st0 n with stack := [shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 13 }
      (sel % 2 ^ 32) (decode_pc13 sel) (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 22 e _ _ s13]
  have s18 :
      step e
        { st0 n with
          stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 } =
        StepResult.next { st0 n with stack := [1], pc := 19 } := by
    have h := step_eq e
      { st0 n with
        stack := [sel % 2 ^ 32, shrW 0xE0 (calldataLoad (packCall sel []) 0)], pc := 18 }
      (sel % 2 ^ 32) (shrW 0xE0 (calldataLoad (packCall sel []) 0)) []
      (decode_pc18 sel) rfl (list_length_lt_1024 (k := 0) rfl)
    simp [shrW_calldataLoad_packCall, eqW_self] at h ⊢
    exact h
  rw [run_of_next 21 e _ _ s18]
  have s19 : step e { st0 n with stack := [1], pc := 19 } =
      StepResult.next { st0 n with stack := [getPc, 1], pc := 22 } := by
    have h := step_push e { st0 n with stack := [1], pc := 19 } getPc (decode_pc19 sel)
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 20 e _ _ s19]
  have s22 : step e { st0 n with stack := [getPc, 1], pc := 22 } =
      StepResult.next { st0 n with stack := [], pc := getPc } := by
    have h := step_jumpi_nz e { st0 n with stack := [getPc, 1], pc := 22 } getPc 1 []
      (decode_pc22 sel) rfl (by decide) (isJumpDest_get sel)
    simpa [env] using h
  rw [run_of_next 19 e _ _ s22]
  have s67 : step e { st0 n with stack := [], pc := getPc } =
      StepResult.next { st0 n with stack := [], pc := 68 } := by
    have hdec : decodeAt e.code getPc = some ({ op := .JUMPDEST }, 68) := by
      simpa [env, getPc] using decode_pc67 sel
    exact step_jumpdest e { st0 n with stack := [], pc := getPc } hdec
  rw [run_of_next 18 e _ _ s67]
  have hcode : e.code = bodyPre sel ++ GetBody.code := by
    simpa [env] using code_bodyPre sel
  have d68 : decodeAt e.code 68 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 69) := by
    rw [hcode, show (68 : Nat) = (bodyPre sel).length + 0 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc0
  have s68 : step e { st0 n with stack := [], pc := 68 } =
      StepResult.next { st0 n with stack := [0], pc := 69 } := by
    have h := step_push e { st0 n with stack := [], pc := 68 } 0 d68
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 17 e _ _ s68]
  have d69 : decodeAt e.code 69 = some ({ op := .SLOAD }, 70) := by
    rw [hcode, show (69 : Nat) = (bodyPre sel).length + 1 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc1
  have s69 : step e { st0 n with stack := [0], pc := 69 } =
      StepResult.next { st0 n with stack := [n], pc := 70 } := by
    have h := step_sload e { st0 n with stack := [0], pc := 69 } 0 [] d69 rfl
      (list_length_lt_1024 (k := 0) rfl)
    simpa [st0] using h
  rw [run_of_next 16 e _ _ s69]
  have d70 : decodeAt e.code 70 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 71) := by
    rw [hcode, show (70 : Nat) = (bodyPre sel).length + 2 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc2
  have s70 : step e { st0 n with stack := [n], pc := 70 } =
      StepResult.next { st0 n with stack := [0, n], pc := 71 } := by
    have h := step_push e { st0 n with stack := [n], pc := 70 } 0 d70
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 15 e _ _ s70]
  have d71 : decodeAt e.code 71 = some ({ op := .MSTORE }, 72) := by
    rw [hcode, show (71 : Nat) = (bodyPre sel).length + 3 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc3
  have s71 : step e { st0 n with stack := [0, n], pc := 71 } =
      StepResult.next
        { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 72 } :=
    step_mstore e { st0 n with stack := [0, n], pc := 71 } 0 n [] d71 rfl
  rw [run_of_next 14 e _ _ s71]
  have d72 : decodeAt e.code 72 =
      some ({ op := .PUSH ⟨1, by decide⟩, imm := 32 }, 74) := by
    rw [hcode, show (72 : Nat) = (bodyPre sel).length + 4 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc4
  have s72 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 72 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 74 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [], pc := 72 } 32 d72
      (list_length_lt_1024 (k := 0) rfl)
    simpa using h
  rw [run_of_next 13 e _ _ s72]
  have d74 : decodeAt e.code 74 =
      some ({ op := .PUSH ⟨0, by decide⟩, imm := 0 }, 75) := by
    rw [hcode, show (74 : Nat) = (bodyPre sel).length + 6 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc6
  have s74 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 74 } =
        StepResult.next
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 75 } := by
    have h := step_push e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [32], pc := 74 } 0 d74
      (list_length_lt_1024 (k := 1) rfl)
    simpa using h
  rw [run_of_next 12 e _ _ s74]
  have d75 : decodeAt e.code 75 = some ({ op := .RETURN }, 76) := by
    rw [hcode, show (75 : Nat) = (bodyPre sel).length + 7 from by simp]
    simpa using GetBody.decode_suffix (bodyPre sel) GetBody.decode_pc7
  have s75 :
      step e { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 75 } =
        StepResult.halt
          (.ret ((List.range 32).map fun i =>
            memGet (memStore (st0 n).mem 0 n) (0 + i)))
          { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 75 } := by
    have h := step_return e
      { st0 n with mem := memStore (st0 n).mem 0 n, stack := [0, 32], pc := 75 }
      0 32 [] d75 rfl
    simpa using h
  rw [run_of_halt 11 e _ _ _ s75]
  rw [GetBody.memStore_packWord]
  simp only
  exact decodeWord_packWord_of_lt (wrap_lt n)

end Lsc3.Compile.GetContract
