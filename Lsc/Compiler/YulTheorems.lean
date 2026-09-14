import Lsc.Compiler.YulDefs
import Lsc.Compiler.Proof.YulProof

/-!
Well-formedness of Core→Yul emission and unfolding of `noExt*`.
Call-free Yul (`noExtExprs` / `noExtStmts`) and the ABI / selector
guards (`fitsGuardWords`, `selectorsNodup`) used by the emitter.
-/

namespace Lsc.Compiler

open Lsc

/-- The empty expression list has no external operations. -/
@[simp]
theorem noExtExprs_nil : noExtExprs [] = true :=
  Proof.noExtExprs_nil

/-- `noExtExprs` on a cons is the head expression and the tail. -/
@[simp]
theorem noExtExprs_cons (e es) :
    noExtExprs (e :: es) = (noExtExpr e && noExtExprs es) :=
  Proof.noExtExprs_cons e es

/-- The empty statement list has no external operations. -/
@[simp]
theorem noExtStmts_nil : noExtStmts [] = true :=
  Proof.noExtStmts_nil

/-- `noExtStmts` on a cons is the head statement and the tail. -/
@[simp]
theorem noExtStmts_cons (s ss) :
    noExtStmts (s :: ss) = (noExtStmt s && noExtStmts ss) :=
  Proof.noExtStmts_cons s ss

/-- The empty switch-case list has no external operations. -/
@[simp]
theorem noExtCases_nil : noExtCases [] = true :=
  Proof.noExtCases_nil

/-- `noExtCases` on a cons is the case body and the tail. -/
@[simp]
theorem noExtCases_cons (p rest) :
    noExtCases (p :: rest) = (noExtStmts p.2 && noExtCases rest) :=
  Proof.noExtCases_cons p rest

/-- The empty block has no external operations. -/
@[simp]
theorem noExtBlock_nil : noExtBlock [] = true :=
  Proof.noExtBlock_nil

/-- `noExtBlock` on a cons is the head statement and the tail. -/
@[simp]
theorem noExtBlock_cons (s ss) :
    noExtBlock (s :: ss) = (noExtStmt s && noExtBlock ss) :=
  Proof.noExtBlock_cons s ss

/-- `atomWF` holds of a variable, or of a literal that fits in a word. -/
theorem atomWF_iff (a : Atom) :
    atomWF a = true ↔ match a with | .var _ => True | .lit n => n < wordBound :=
  Proof.atomWF_iff a

/-- `fieldKindOK` means field `idx` exists and has kind `k`. -/
theorem fieldKindOK_iff (c : ContractDef) (idx : Nat) (k : FieldKind) :
    fieldKindOK c idx k = true ↔ ∃ fd, c.fields[idx]? = some fd ∧ fd.kind = k :=
  Proof.fieldKindOK_iff c idx k

/-- `fitsGuardWords n` is `n ≤ 4` (ABI words under the memory guard). -/
theorem fitsGuardWords_iff (n : Nat) :
    fitsGuardWords n = true ↔ n ≤ 4 :=
  Proof.fitsGuardWords_iff n

/-- `fitsGuardCall n` is `n ≤ 3` (CALL args under the memory guard). -/
theorem fitsGuardCall_iff (n : Nat) :
    fitsGuardCall n = true ↔ n ≤ 3 :=
  Proof.fitsGuardCall_iff n

/-- A well-formed CALL target and args have well-formed atoms and at most three arguments. -/
theorem callWF_elim {t args} (h : callWF t args = true) :
    atomWF t = true ∧ (∀ x ∈ args, atomWF x = true) ∧ args.length ≤ 3 :=
  Proof.callWF_elim h

/-- A well-formed `Op.call` has a well-formed CALL and a 4-byte selector. -/
theorem opWF_call {c t sel args ret}
    (h : opWF c (.call t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 :=
  Proof.opWF_call h

/-- A well-formed `Op.view` has a well-formed CALL and a 4-byte selector. -/
theorem opWF_view {c t sel args ret}
    (h : opWF c (.view t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 :=
  Proof.opWF_view h

/-- A well-formed `Stmt.call` has a well-formed CALL and a 4-byte selector. -/
theorem stmtWF_call {c t sel args ret}
    (h : stmtWF c (.call t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 :=
  Proof.stmtWF_call h

/-- A well-formed `Stmt.view` has a well-formed CALL and a 4-byte selector. -/
theorem stmtWF_view {c t sel args ret}
    (h : stmtWF c (.view t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 :=
  Proof.stmtWF_view h

/-- Up to four ABI words after `abiPtr` fit under `memoryGuardK`. -/
theorem abiWords_le {n : Nat} (h : n ≤ 4) : abiPtr + 32 * n ≤ memoryGuardK :=
  Proof.abiWords_le h

/-- A selector plus up to three ABI words after `abiPtr` fit under `memoryGuardK`. -/
theorem abiCall_le {n : Nat} (h : n ≤ 3) : abiPtr + (4 + 32 * n) ≤ memoryGuardK :=
  Proof.abiCall_le h

/-- Up to three ABI words after `abiAfterSel` fit under `memoryGuardK`. -/
theorem abiAfterSel_le {n : Nat} (h : n ≤ 3) : abiAfterSel + 32 * n ≤ memoryGuardK :=
  Proof.abiAfterSel_le h

/-- `eventOK` means the event exists, has `n` params, and `n ≤ 4`. -/
theorem eventOK_iff (c : ContractDef) (ev n : Nat) :
    eventOK c ev n = true ↔
      ∃ ed, c.events[ev]? = some ed ∧ ed.params.length = n ∧ n ≤ 4 :=
  Proof.eventOK_iff c ev n

/-- `errorOK` means the error exists, has `n` params, and `n ≤ 3`. -/
theorem errorOK_iff (c : ContractDef) (err n : Nat) :
    errorOK c err n = true ↔
      ∃ ed, c.errors[err]? = some ed ∧ ed.params.length = n ∧ n ≤ 3 :=
  Proof.errorOK_iff c err n

/-- `identsNodup tag n` is pairwise uniqueness of `{tag}_i`. -/
theorem identsNodup_iff (tag : String) (n : Nat) :
    identsNodup tag n = true ↔ ((List.range n).map (identV tag)).Pairwise (fun a b => a ≠ b) :=
  Proof.identsNodup_iff tag n

/-- `selectorsNodup` is pairwise uniqueness of function selectors. -/
theorem selectorsNodup_iff (c : ContractDef) :
    selectorsNodup c = true ↔
      (c.functions.map (fun f => f.selector)).Pairwise (fun a b => a ≠ b) :=
  Proof.selectorsNodup_iff c

end Lsc.Compiler
