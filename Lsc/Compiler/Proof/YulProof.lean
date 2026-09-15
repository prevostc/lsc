import Lsc.Compiler.YulDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of Yul well-formedness (`atomWF`, `callWF`, `selectorsNodup`)
and `noExt*` unfolding. Statements live in `YulTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

namespace Proof

theorem noExtExprs_nil : noExtExprs [] = true := rfl

theorem noExtExprs_cons (e es) :
    noExtExprs (e :: es) = (noExtExpr e && noExtExprs es) := rfl

theorem noExtStmts_nil : noExtStmts [] = true := rfl

theorem noExtStmts_cons (s ss) :
    noExtStmts (s :: ss) = (noExtStmt s && noExtStmts ss) := rfl

theorem noExtCases_nil : noExtCases [] = true := rfl

theorem noExtCases_cons (p rest) :
    noExtCases (p :: rest) = (noExtStmts p.2 && noExtCases rest) := rfl

theorem noExtBlock_nil : noExtBlock [] = true := rfl

theorem noExtBlock_cons (s ss) :
    noExtBlock (s :: ss) = (noExtStmt s && noExtBlock ss) := rfl

theorem atomWF_iff (a : Atom) :
    atomWF a = true ↔ match a with | .var _ => True | .lit n => n < wordBound := by
  cases a <;> simp [atomWF, decide_eq_true_eq]

theorem fieldKindOK_iff (c : ContractDef) (idx : Nat) (k : FieldKind) :
    fieldKindOK c idx k = true ↔ ∃ fd, c.fields[idx]? = some fd ∧ fd.kind = k := by
  simp only [fieldKindOK]
  cases c.fields[idx]? <;> simp [decide_eq_true_eq]

theorem fitsGuardWords_iff (n : Nat) :
    fitsGuardWords n = true ↔ n ≤ 4 := by
  unfold fitsGuardWords abiPtr memoryGuardK
  rw [decide_eq_true_eq]
  constructor <;> intro <;> omega

theorem fitsGuardCall_iff (n : Nat) :
    fitsGuardCall n = true ↔ n ≤ 3 := by
  unfold fitsGuardCall abiPtr memoryGuardK
  rw [decide_eq_true_eq]
  constructor <;> intro <;> omega

theorem callWF_elim {t args} (h : callWF t args = true) :
    atomWF t = true ∧ (∀ x ∈ args, atomWF x = true) ∧ args.length ≤ 3 := by
  simp [callWF, Bool.and_eq_true, fitsGuardCall_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem opWF_call {c t sel args ret}
    (h : opWF c (.call t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 := by
  simpa [opWF, Bool.and_eq_true, decide_eq_true_eq] using h

theorem opWF_view {c t sel args ret}
    (h : opWF c (.view t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 := by
  simpa [opWF, Bool.and_eq_true, decide_eq_true_eq] using h

theorem stmtWF_call {c t sel args ret}
    (h : stmtWF c (.call t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 := by
  simpa [stmtWF, Bool.and_eq_true, decide_eq_true_eq] using h

theorem stmtWF_view {c t sel args ret}
    (h : stmtWF c (.view t sel args ret) = true) :
    callWF t args = true ∧ sel < 2 ^ 32 := by
  simpa [stmtWF, Bool.and_eq_true, decide_eq_true_eq] using h

theorem opWF_send {c t amt} (h : opWF c (.send t amt) = true) :
    atomWF t = true ∧ atomWF amt = true := by
  simpa [opWF, Bool.and_eq_true] using h

theorem abiWords_le {n : Nat} (h : n ≤ 4) : abiPtr + 32 * n ≤ memoryGuardK := by
  unfold abiPtr memoryGuardK; omega

theorem abiCall_le {n : Nat} (h : n ≤ 3) : abiPtr + (4 + 32 * n) ≤ memoryGuardK := by
  unfold abiPtr memoryGuardK; omega

theorem abiAfterSel_le {n : Nat} (h : n ≤ 3) : abiAfterSel + 32 * n ≤ memoryGuardK := by
  unfold abiAfterSel memoryGuardK; omega

theorem eventOK_iff (c : ContractDef) (ev n : Nat) :
    eventOK c ev n = true ↔
      ∃ ed, c.events[ev]? = some ed ∧ ed.params.length = n ∧ n ≤ 4 := by
  simp only [eventOK]
  cases c.events[ev]? <;> simp [fitsGuardWords_iff, decide_eq_true_eq]

theorem errorOK_iff (c : ContractDef) (err n : Nat) :
    errorOK c err n = true ↔
      ∃ ed, c.errors[err]? = some ed ∧ ed.params.length = n ∧ n ≤ 3 := by
  simp only [errorOK]
  cases c.errors[err]? <;> simp [fitsGuardCall_iff, decide_eq_true_eq]

theorem identsNodup_iff (tag : String) (n : Nat) :
    identsNodup tag n = true ↔ ((List.range n).map (identV tag)).Pairwise (fun a b => a ≠ b) := by
  simp [identsNodup, decide_eq_true_eq]

theorem selectorsNodup_iff (c : ContractDef) :
    selectorsNodup c = true ↔
      (c.functions.map (fun f => f.selector)).Pairwise (fun a b => a ≠ b) := by
  simp [selectorsNodup, decide_eq_true_eq]

end Proof

end Lsc.Compiler
