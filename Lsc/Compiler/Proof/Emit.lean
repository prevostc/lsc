import Lsc.Compiler.Proof.Env

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Accumulator homomorphism: `emit* e = { acc := (emit* {}).acc ++ e.acc }`.
These lemmas are **not** `simp` — rewriting `emitDo {}` with `emitDo_acc` loops.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM

theorem Emit.cat_stmts (e e0 : Emit) :
    ({ acc := e0.acc ++ e.acc } : Emit).stmts = e.stmts ++ e0.stmts := by
  simp [Emit.stmts, List.reverse_append]

theorem emitDo_acc (e : Emit) (op : YOp) (args : List YExpr) :
    emitDo e op args = { acc := (emitDo ({} : Emit) op args).acc ++ e.acc } := rfl

theorem emitLet_acc (e : Emit) (n : YIdent) (x : YExpr) :
    emitLet e n x = { acc := (emitLet ({} : Emit) n x).acc ++ e.acc } := rfl

theorem emitAssign_acc (e : Emit) (n : YIdent) (x : YExpr) :
    emitAssign e n x = { acc := (emitAssign ({} : Emit) n x).acc ++ e.acc } := rfl

theorem emitBlock_acc (e : Emit) (body : YBlock) :
    emitBlock e body = { acc := (emitBlock ({} : Emit) body).acc ++ e.acc } := rfl

theorem emitSeqIfWord_acc (e : Emit) (d : Nat) (cond : Cond) (eA eB : Emit) :
    emitSeqIfWord tag e d cond eA eB =
      { acc := (emitSeqIfWord tag {} d cond eA eB).acc ++ e.acc } := by
  unfold emitSeqIfWord
  rw [emitBlock_acc, emitLet_acc]
  conv => rhs; rw [emitBlock_acc]
  simp [List.append_assoc]

theorem emitBlock_stmts (e : Emit) (body : YBlock) :
    (emitBlock e body).stmts = e.stmts ++ [.block body] :=
  Emit.stmts_push _ _

theorem seqIfWordInner_eq (d : Nat) (cond : Cond) (eA eB : Emit) :
    seqIfWordInner tag d cond eA eB =
      [.letDecl [identPhi tag d] (some (lit 0)),
        .switch (emitCond tag d cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts),
        .assign [identV tag d] (var (identPhi tag d))] := by
  simp [seqIfWordInner, emitAssign, emitLet, Emit.push, Emit.stmts,
    List.reverse_cons, List.reverse_nil, List.nil_append]

theorem emitSeqIfWord_nil_stmts (d : Nat) (cond : Cond) (eA eB : Emit) :
    (emitSeqIfWord tag {} d cond eA eB).stmts =
      [.letDecl [identV tag d] (some (lit 0)),
        .block (seqIfWordInner tag d cond eA eB)] := by
  unfold emitSeqIfWord
  rw [emitBlock_stmts]
  have hlet : (emitLet ({} : Emit) (identV tag d) (lit 0)).stmts =
      [.letDecl [identV tag d] (some (lit 0))] := by
    simp [emitLet, Emit.push, Emit.stmts]
  rw [hlet]
  rfl

theorem hoist_seqIfWordInner (d : Nat) (cond : Cond) (eA eB : Emit) :
    hoist evm (seqIfWordInner tag d cond eA eB) = [] := by
  simp [seqIfWordInner_eq, hoist]

theorem emitIf_acc (e : Emit) (cnd : YExpr) (body : YBlock) :
    emitIf e cnd body = { acc := (emitIf ({} : Emit) cnd body).acc ++ e.acc } := rfl

theorem emitExtCall_stmts (e : Emit) (depth : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (bind : Option YIdent) :
    (emitExtCall tag e depth target sel args ret isView bind).stmts =
      e.stmts ++
        match bind with
        | none => [.block (emitExtCallBody tag depth target sel args ret isView none)]
        | some name =>
          [.letDecl [name] (some (lit 0)),
           .block (emitExtCallBody tag depth target sel args ret isView (some name))] := by
  cases bind <;> simp [emitExtCall, emitBlock, emitLet, Emit.stmts_push]

theorem emitExtSend_stmts (e : Emit) (depth : Nat) (target amount : Atom)
    (bind : Option YIdent) :
    (emitExtSend tag e depth target amount bind).stmts =
      e.stmts ++
        match bind with
        | none => [.block (emitExtSendBody tag depth target amount none)]
        | some name =>
          [.letDecl [name] (some (lit 0)),
           .block (emitExtSendBody tag depth target amount (some name))] := by
  cases bind <;> simp [emitExtSend, emitBlock, emitLet, Emit.stmts_push]

theorem emitReturnUnit_acc (e : Emit) (halt : Bool) :
    emitReturnUnit e halt = { acc := (emitReturnUnit {} halt).acc ++ e.acc } := by
  cases halt <;> rfl

theorem emitReturnUnit_true (e : Emit) :
    (emitReturnUnit e true).stmts = e.stmts ++ [stopStmt] := by
  simp [emitReturnUnit, Emit.stmts_push]

/-- `foldl` of aligned `mstore`s, starting from `extra` vs `extra` appended onto `e`. -/
theorem foldl_mstore_cat (e extra : Emit) (base : Nat) (xs : List YExpr) (i0 : Nat) :
    (xs.foldl (fun p a =>
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1))
      ({ acc := extra.acc ++ e.acc }, i0)).1 =
      { acc :=
          (xs.foldl (fun p a =>
              (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1))
            (extra, i0)).1.acc ++ e.acc } := by
  induction xs generalizing extra i0 with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons]
    have hdo :
        emitDo { acc := extra.acc ++ e.acc } Op.mstore [lit (base + 32 * i0), a] =
          { acc := (emitDo extra Op.mstore [lit (base + 32 * i0), a]).acc ++ e.acc } := by
      simp [emitDo, Emit.push, List.append_assoc]
    rw [hdo]
    exact ih (emitDo extra Op.mstore [lit (base + 32 * i0), a]) (i0 + 1)

theorem foldl_mstore_acc (e : Emit) (base : Nat) (xs : List YExpr) (i0 : Nat) :
    (xs.foldl (fun p a =>
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1)) (e, i0)).1 =
      { acc :=
          (xs.foldl (fun p a =>
              (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1))
            (({} : Emit), i0)).1.acc ++ e.acc } := by
  simpa using foldl_mstore_cat e {} base xs i0

theorem foldl_mstore_args_cat (e extra : Emit) (base depth : Nat) (args : List Atom) (i0 : Nat) :
    (args.foldl (fun p a =>
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE tag depth a], p.2 + 1))
      ({ acc := extra.acc ++ e.acc }, i0)).1 =
      { acc :=
          (args.foldl (fun p a =>
              (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE tag depth a], p.2 + 1))
            (extra, i0)).1.acc ++ e.acc } := by
  induction args generalizing extra i0 with
  | nil => simp
  | cons a args ih =>
    simp only [List.foldl_cons]
    have hdo :
        emitDo { acc := extra.acc ++ e.acc } Op.mstore [lit (base + 32 * i0), atomE tag depth a] =
          { acc := (emitDo extra Op.mstore [lit (base + 32 * i0), atomE tag depth a]).acc ++ e.acc } := by
      simp [emitDo, Emit.push, List.append_assoc]
    rw [hdo]
    exact ih (emitDo extra Op.mstore [lit (base + 32 * i0), atomE tag depth a]) (i0 + 1)

theorem emitDo_cat (e extra : Emit) (op : YOp) (args : List YExpr) :
    emitDo { acc := extra.acc ++ e.acc } op args =
      { acc := (emitDo extra op args).acc ++ e.acc } := by
  simp [emitDo, Emit.push, List.append_assoc]

theorem emitLet_cat (e extra : Emit) (n : YIdent) (x : YExpr) :
    emitLet { acc := extra.acc ++ e.acc } n x =
      { acc := (emitLet extra n x).acc ++ e.acc } := by
  simp [emitLet, Emit.push, List.append_assoc]

theorem emitIf_cat (e extra : Emit) (cnd : YExpr) (body : YBlock) :
    emitIf { acc := extra.acc ++ e.acc } cnd body =
      { acc := (emitIf extra cnd body).acc ++ e.acc } := by
  simp [emitIf, Emit.push, List.append_assoc]

theorem emitPanic_acc (e : Emit) (code : Nat) :
    emitPanic e code = { acc := (emitPanic {} code).acc ++ e.acc } := by
  simp [emitPanic, emitDo, Emit.push]

theorem emitCustomError_acc (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr) :
    emitCustomError c e err args =
      { acc := (emitCustomError c {} err args).acc ++ e.acc } := by
  simp only [emitCustomError]
  rw [emitDo_acc e]
  rw [foldl_mstore_cat]
  rw [emitDo_cat]

theorem emitReturnWords_acc (e : Emit) (xs : List YExpr) :
    emitReturnWords e xs = { acc := (emitReturnWords {} xs).acc ++ e.acc } := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [emitReturnWords]
    rw [foldl_mstore_acc]
    rw [emitDo_cat]

theorem emitLog1_acc (e : Emit) (topic : Nat) (args : List YExpr) :
    emitLog1 e topic args = { acc := (emitLog1 {} topic args).acc ++ e.acc } := by
  simp only [emitLog1]
  rw [foldl_mstore_acc]
  rw [emitDo_cat]

theorem emitMapSlotPrep_acc (e : Emit) (slot : Nat) (k : YExpr) :
    emitMapSlotPrep e slot k = { acc := (emitMapSlotPrep {} slot k).acc ++ e.acc } := by
  simp [emitMapSlotPrep, emitDo, Emit.push]

theorem emitMap2SlotPrep_acc (e : Emit) (slot : Nat) (k₁ k₂ : YExpr) :
    emitMap2SlotPrep e slot k₁ k₂ =
      { acc := (emitMap2SlotPrep {} slot k₁ k₂).acc ++ e.acc } := by
  simp [emitMap2SlotPrep, emitMapSlotPrep, emitDo, Emit.push]

theorem emitMulOverflowGuard_acc (e : Emit) (a b p : YExpr) :
    emitMulOverflowGuard e a b p =
      { acc := (emitMulOverflowGuard {} a b p).acc ++ e.acc } :=
  emitIf_acc _ _ _

theorem emitAddChecked_acc (e : Emit) (name : YIdent) (a b : YExpr) :
    emitAddChecked e name a b =
      { acc := (emitAddChecked {} name a b).acc ++ e.acc } := by
  simp [emitAddChecked, emitLet, emitIf, Emit.push]

theorem emitSubChecked_acc (e : Emit) (name : YIdent) (a b : YExpr) :
    emitSubChecked e name a b =
      { acc := (emitSubChecked {} name a b).acc ++ e.acc } := by
  simp [emitSubChecked, emitLet, emitIf, Emit.push]

theorem emitMulChecked_acc (e : Emit) (name : YIdent) (a b : YExpr) :
    emitMulChecked e name a b =
      { acc := (emitMulChecked {} name a b).acc ++ e.acc } := by
  simp [emitMulChecked, emitLet, emitMulOverflowGuard, emitIf, Emit.push]

theorem emitDivChecked_acc (e : Emit) (name : YIdent) (a b : YExpr) :
    emitDivChecked e name a b =
      { acc := (emitDivChecked {} name a b).acc ++ e.acc } := by
  simp [emitDivChecked, emitLet, emitIf, Emit.push]

theorem emitPow10_acc (e : Emit) (name : YIdent) (d : YExpr) :
    emitPow10 e name d =
      { acc := (emitPow10 {} name d).acc ++ e.acc } := by
  simp [emitPow10, emitLet, emitIf, Emit.push]

theorem emitMulDivDown_acc (e : Emit) (name : YIdent) (a b c : YExpr) :
    emitMulDivDown e name a b c =
      { acc := (emitMulDivDown {} name a b c).acc ++ e.acc } := by
  simp [emitMulDivDown, emitLet, emitIf, emitMulOverflowGuard, Emit.push]

theorem emitMulDivUp_acc (e : Emit) (name : YIdent) (a b c : YExpr) :
    emitMulDivUp e name a b c =
      { acc := (emitMulDivUp {} name a b c).acc ++ e.acc } := by
  simp [emitMulDivUp, emitLet, emitIf, emitMulOverflowGuard, Emit.push]

theorem emitCallRetCheck_acc (e : Emit) (ret : AbiRet) :
    emitCallRetCheck e ret = { acc := (emitCallRetCheck {} ret).acc ++ e.acc } := by
  cases ret <;> simp [emitCallRetCheck, emitIf, Emit.push]

private theorem emitCallRetCheck_cat (e extra : Emit) (ret : AbiRet) :
    emitCallRetCheck { acc := extra.acc ++ e.acc } ret =
      { acc := (emitCallRetCheck extra ret).acc ++ e.acc } := by
  cases ret <;> simp [emitCallRetCheck, emitIf, Emit.push, List.append_assoc]

theorem emitExtCall_acc tag (e : Emit) (depth : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (bindResult : Option YIdent) :
    emitExtCall tag e depth target sel args ret isView bindResult =
      { acc := (emitExtCall tag {} depth target sel args ret isView bindResult).acc ++ e.acc } := by
  cases bindResult with
  | none =>
    simp [emitExtCall, emitBlock, Emit.push]
  | some name =>
    simp [emitExtCall, emitLet, emitBlock, Emit.push]

theorem emitExtSend_acc tag (e : Emit) (depth : Nat) (target amount : Atom)
    (bindResult : Option YIdent) :
    emitExtSend tag e depth target amount bindResult =
      { acc := (emitExtSend tag {} depth target amount bindResult).acc ++ e.acc } := by
  cases bindResult with
  | none =>
    simp [emitExtSend, emitBlock, Emit.push]
  | some name =>
    simp [emitExtSend, emitLet, emitBlock, Emit.push]

theorem emitLetOp_acc (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) :
    emitLetOp tag c e d op =
      (emitLetOp tag c {} d op).map fun e0 => { acc := e0.acc ++ e.acc } := by
  cases op with
  | load _ =>
    simp only [emitLetOp, Option.map_some]
    exact congrArg some (emitLet_acc e _ _)
  | loadMap f k =>
    simp only [emitLetOp, Option.map_some]
    rw [emitMapSlotPrep_acc, emitLet_cat]
  | loadMap2 f k₁ k₂ =>
    simp only [emitLetOp, Option.map_some]
    rw [emitMap2SlotPrep_acc, emitLet_cat]
  | sender | value | timestamp | blockNumber | selfAddress | selfBalance | pure _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitLet_acc _ _ _)
  | addChecked _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitAddChecked_acc _ _ _ _)
  | subChecked _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitSubChecked_acc _ _ _ _)
  | mulChecked _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitMulChecked_acc _ _ _ _)
  | divChecked _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitDivChecked_acc _ _ _ _)
  | mulDivDown _ _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitMulDivDown_acc _ _ _ _ _)
  | mulDivUp _ _ _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitMulDivUp_acc _ _ _ _ _)
  | pow10 _ =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitPow10_acc _ _ _)
  | call t sel args ret =>
    simp only [emitLetOp, Option.map_some]
    exact congrArg some (emitExtCall_acc tag e _ t sel args ret false _)
  | view t sel args ret =>
    simp only [emitLetOp, Option.map_some]
    exact congrArg some (emitExtCall_acc tag e _ t sel args ret true _)
  | send t amt =>
    simp only [emitLetOp, Option.map_some]
    exact congrArg some (emitExtSend_acc tag e _ t amt _)

theorem emitLetOp_some tag (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) :
    ∃ e', emitLetOp tag c e d op = some e' := by
  cases op <;> simp [emitLetOp]

theorem emitStmt_acc (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt) :
    emitStmt tag c e d s = { acc := (emitStmt tag c {} d s).acc ++ e.acc } := by
  cases s with
  | store _ _ => simp [emitStmt, emitDo, Emit.push]
  | storeMap f k v =>
    simp only [emitStmt]; rw [emitMapSlotPrep_acc, emitDo_cat]
  | storeMap2 f k₁ k₂ v =>
    simp only [emitStmt]; rw [emitMap2SlotPrep_acc, emitDo_cat]
  | require _ _ _ => simp [emitStmt, emitIf, Emit.push]
  | emit _ _ => simp only [emitStmt]; exact emitLog1_acc _ _ _
  | revert _ _ => simp only [emitStmt]; exact emitCustomError_acc _ _ _ _
  | call t sel args ret =>
    simp only [emitStmt]; exact emitExtCall_acc tag e _ t sel args ret false none
  | view t sel args ret =>
    simp only [emitStmt]; exact emitExtCall_acc tag e _ t sel args ret true none

theorem emitLockClear_acc (e : Emit) :
    emitLockClear e = { acc := lockClearStmt :: e.acc } := rfl

theorem emitLockClear_stmts (e : Emit) :
    (emitLockClear e).stmts = e.stmts ++ [lockClearStmt] :=
  Emit.stmts_push e lockClearStmt

/-- Unit halt with optional lock-clear, grouped so `append_inv` peels the body. -/
theorem emitReturnUnit_lock_if (e : Emit) (clearLock : Bool) :
    (emitReturnUnit (if clearLock then emitLockClear e else e) true).stmts =
      e.stmts ++ ((if clearLock then [lockClearStmt] else []) ++ [stopStmt]) := by
  cases clearLock with
  | false => simp [emitReturnUnit_true]
  | true => simp [emitLockClear_stmts, emitReturnUnit_true]

theorem emitRet_acc_unlocked tag (e : Emit) (d : Nat) (halt : Bool)
    {t} (r : RetExpr t) :
    emitRet tag e d halt r false =
      { acc := (emitRet tag {} d halt r false).acc ++ e.acc } := by
  cases r with
  | unit => simp only [emitRet]; exact emitReturnUnit_acc _ _
  | word _ | addr _ | flag _ | pair _ _ => simp only [emitRet]; exact emitReturnWords_acc _ _

theorem emitRet_lock_eq tag (e : Emit) (d : Nat) (halt : Bool)
    {t} (r : RetExpr t) :
    emitRet tag e d halt r true = emitRet tag (emitLockClear e) d halt r false := rfl

theorem emitRet_acc tag (e : Emit) (d : Nat) (halt : Bool)
    {t} (r : RetExpr t) (clearLock : Bool := false) :
    emitRet tag e d halt r clearLock =
      { acc := (emitRet tag {} d halt r clearLock).acc ++ e.acc } := by
  cases clearLock with
  | false => exact emitRet_acc_unlocked tag e d halt r
  | true =>
    rw [emitRet_lock_eq, emitRet_lock_eq tag {} d halt r]
    rw [emitRet_acc_unlocked tag (emitLockClear e) d halt r]
    rw [emitRet_acc_unlocked tag (emitLockClear {}) d halt r]
    simp [emitLockClear_acc, List.append_assoc]

theorem emitRet_word_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.word a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.word a), Emit.cat_stmts]
  simp [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitRet_addr_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.addr a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.addr a), Emit.cat_stmts]
  simp [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitRet_flag_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.flag a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.flag a), Emit.cat_stmts]
  simp [emitRet, retAtoms, List.map_cons, List.map_nil]

private theorem emitReturnWords_lockClear_stmts (xs : List YExpr) :
    (emitReturnWords (emitLockClear {}) xs).stmts =
      [lockClearStmt] ++ (emitReturnWords {} xs).stmts := by
  have h := congrArg Emit.stmts (emitReturnWords_acc (emitLockClear {}) xs)
  simpa [Emit.cat_stmts, emitLockClear_stmts, Emit.stmts_nil] using h

theorem emitRet_word_stmts_lock (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.word a) true).stmts =
      e.stmts ++ [lockClearStmt] ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.word a) true, Emit.cat_stmts]
  simp [emitRet, emitReturnWords_lockClear_stmts, retAtoms, List.map_cons, List.map_nil,
    List.append_assoc]

theorem emitRet_addr_stmts_lock (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.addr a) true).stmts =
      e.stmts ++ [lockClearStmt] ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.addr a) true, Emit.cat_stmts]
  simp [emitRet, emitReturnWords_lockClear_stmts, retAtoms, List.map_cons, List.map_nil,
    List.append_assoc]

theorem emitRet_flag_stmts_lock (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet tag e d halt (.flag a) true).stmts =
      e.stmts ++ [lockClearStmt] ++ (emitReturnWords {} [atomE tag d a]).stmts := by
  rw [emitRet_acc tag e d halt (.flag a) true, Emit.cat_stmts]
  simp [emitRet, emitReturnWords_lockClear_stmts, retAtoms, List.map_cons, List.map_nil,
    List.append_assoc]

theorem emitRet_word_stmts_if (e : Emit) (d : Nat) (halt : Bool) (a : Atom)
    (clearLock : Bool) :
    (emitRet tag e d halt (.word a) clearLock).stmts =
      e.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag d a]).stmts) := by
  cases clearLock with
  | false =>
    simpa using emitRet_word_stmts tag e d halt a
  | true =>
    have h := emitRet_word_stmts_lock tag e d halt a
    simpa [List.append_assoc] using h

theorem emitRet_addr_stmts_if (e : Emit) (d : Nat) (halt : Bool) (a : Atom)
    (clearLock : Bool) :
    (emitRet tag e d halt (.addr a) clearLock).stmts =
      e.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag d a]).stmts) := by
  cases clearLock with
  | false =>
    simpa using emitRet_addr_stmts tag e d halt a
  | true =>
    have h := emitRet_addr_stmts_lock tag e d halt a
    simpa [List.append_assoc] using h

theorem emitRet_flag_stmts_if (e : Emit) (d : Nat) (halt : Bool) (a : Atom)
    (clearLock : Bool) :
    (emitRet tag e d halt (.flag a) clearLock).stmts =
      e.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag d a]).stmts) := by
  cases clearLock with
  | false =>
    simpa using emitRet_flag_stmts tag e d halt a
  | true =>
    have h := emitRet_flag_stmts_lock tag e d halt a
    simpa [List.append_assoc] using h

theorem emitRet_pair_ww_stmts (e : Emit) (d : Nat) (halt : Bool) (a b : Atom) :
    (emitRet tag e d halt (.pair (.word a) (.word b))).stmts =
      e.stmts ++ (emitReturnWords {} [atomE tag d a, atomE tag d b]).stmts := by
  rw [emitRet_acc tag e d halt (.pair (.word a) (.word b)), Emit.cat_stmts]
  simp [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitRet_pair_ww_stmts_lock (e : Emit) (d : Nat) (halt : Bool) (a b : Atom) :
    (emitRet tag e d halt (.pair (.word a) (.word b)) true).stmts =
      e.stmts ++ [lockClearStmt] ++
        (emitReturnWords {} [atomE tag d a, atomE tag d b]).stmts := by
  rw [emitRet_acc tag e d halt (.pair (.word a) (.word b)) true, Emit.cat_stmts]
  simp [emitRet, emitReturnWords_lockClear_stmts, retAtoms, List.map_cons, List.map_nil,
    List.append_assoc]

theorem emitRet_pair_ww_stmts_if (e : Emit) (d : Nat) (halt : Bool) (a b : Atom)
    (clearLock : Bool) :
    (emitRet tag e d halt (.pair (.word a) (.word b)) clearLock).stmts =
      e.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag d a, atomE tag d b]).stmts) := by
  cases clearLock with
  | false =>
    simpa using emitRet_pair_ww_stmts tag e d halt a b
  | true =>
    have h := emitRet_pair_ww_stmts_lock tag e d halt a b
    simpa [List.append_assoc] using h

theorem emitCore_acc tag {c : ContractDef} {halt : Bool} {clearLock : Bool} {t : RetTy} :
    ∀ (core : Core t) (e : Emit) (d : Nat),
      emitCore tag c e d halt core clearLock =
        (emitCore tag c {} d halt core clearLock).map fun e0 =>
          { acc := e0.acc ++ e.acc } := by
  intro core
  induction core with
  | ret r => intro e d; simp only [emitCore]; rw [emitRet_acc tag e d halt r clearLock]; rfl
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d
    simp only [emitCore]
    rw [emitLetOp_acc]
    cases emitLetOp tag c {} d op with
    | none => simp
    | some e0 =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      rw [emitRet_acc tag { acc := e0.acc ++ e.acc } (d + 1) halt _ clearLock]
      rw [emitRet_acc tag e0 (d + 1) halt _ clearLock]
      simp [List.append_assoc]
  | stmtTail s =>
    intro e d
    simp only [emitCore, Option.map_some]
    split_ifs with hcl
    · rw [emitStmt_acc]
      rw [emitLockClear_acc, emitLockClear_acc (emitStmt tag c {} d s)]
      rw [emitReturnUnit_acc, emitReturnUnit_acc
        { acc := lockClearStmt :: (emitStmt tag c {} d s).acc }]
      simp [List.append_assoc]
    · rw [emitStmt_acc, emitReturnUnit_acc, emitReturnUnit_acc (emitStmt tag c {} d s)]
      simp [List.append_assoc]
  | revertTail err args =>
    intro e d; simp only [emitCore, Option.map_some]; exact congrArg some (emitCustomError_acc _ _ _ _)
  | letOp op k ih =>
    intro e d
    simp only [emitCore]
    rw [emitLetOp_acc]
    cases emitLetOp tag c {} d op with
    | none => simp
    | some e0 =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      rw [ih { acc := e0.acc ++ e.acc } (d + 1), ih e0 (d + 1)]
      cases emitCore tag c {} (d + 1) halt k clearLock with
      | none => simp
      | some _ => simp [List.append_assoc]
  | seq s k ih =>
    intro e d
    simp only [emitCore]
    rw [emitStmt_acc]
    rw [ih { acc := (emitStmt tag c {} d s).acc ++ e.acc } d, ih (emitStmt tag c {} d s) d]
    cases emitCore tag c {} d halt k clearLock with
    | none => simp
    | some _ => simp [List.append_assoc]
  | letPure p args k ih =>
    intro e d
    simp only [emitCore]
    rw [emitLet_acc]
    rw [ih { acc := (emitLet {} (identV tag d) (emitPrim tag d p args)).acc ++ e.acc } (d + 1),
      ih (emitLet {} (identV tag d) (emitPrim tag d p args)) (d + 1)]
    cases emitCore tag c {} (d + 1) halt k clearLock with
    | none => simp
    | some _ => simp [List.append_assoc]
  | ite cond a b =>
    intro e d
    simp only [emitCore]
    cases emitCore tag c {} d halt a clearLock with
    | none => simp
    | some _ =>
      cases emitCore tag c {} d halt b clearLock with
      | none => simp
      | some _ => simp [Emit.push]
  | @seqIf tBr _ cond th el k _ _ ihk =>
    intro e d
    cases tBr with
    | unit =>
      simp only [emitCore]
      cases hA : emitCore tag c {} d false th false with
      | none => simp
      | some eA =>
        cases hB : emitCore tag c {} d false el false with
        | none => simp
        | some eB =>
          simp only [hA, hB, Bind.bind, Option.bind, Pure.pure]
          rw [ihk (e.push (.switch (emitCond tag d cond)
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))) d]
          rw [ihk (({} : Emit).push (.switch (emitCond tag d cond)
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))) d]
          cases emitCore tag c {} d halt k clearLock with
          | none => simp
          | some _ => simp [Emit.push, List.append_assoc]
    | word | addr | flag =>
      simp only [emitCore]
      cases hA : emitCoreToVar tag c {} d (identPhi tag d) th with
      | none => simp
      | some eA =>
        cases hB : emitCoreToVar tag c {} d (identPhi tag d) el with
        | none => simp
        | some eB =>
          simp only [hA, hB, Bind.bind, Option.bind, Pure.pure]
          rw [emitSeqIfWord_acc]
          rw [ihk ({ acc := (emitSeqIfWord tag {} d cond eA eB).acc ++ e.acc } : Emit)
            (d + 1)]
          rw [ihk (emitSeqIfWord tag {} d cond eA eB) (d + 1)]
          cases emitCore tag c {} (d + 1) halt k clearLock with
          | none => simp
          | some _ => simp [List.append_assoc]
    | pair _ _ => simp [emitCore]

theorem emitCore_prefix {c halt clearLock t} {core : Core t}
    {e e' : Emit} {d : Nat} (hem : emitCore tag c e d halt core clearLock = some e') :
    ∃ e0, emitCore tag c {} d halt core clearLock = some e0 ∧
      e'.stmts = e.stmts ++ e0.stmts := by
  have h := emitCore_acc tag (c := c) (halt := halt) (clearLock := clearLock) core e d
  rw [h] at hem
  cases h0 : emitCore tag c {} d halt core clearLock with
  | none => simp [h0] at hem
  | some e0 =>
    simp [h0] at hem
    exact ⟨e0, rfl, by cases hem; exact Emit.cat_stmts e e0⟩

theorem emitCoreToVar_acc tag {c : ContractDef} {t : RetTy} (core : Core t)
    (e : Emit) (d : Nat) (dest : YIdent) :
    emitCoreToVar tag c e d dest core =
      (emitCoreToVar tag c {} d dest core).map fun e0 =>
        { acc := e0.acc ++ e.acc } := by
  induction core generalizing e d dest with
  | ret r =>
    cases r with
    | word a | addr a | flag a =>
      simp only [emitCoreToVar, emitAssignRet]
      rw [emitAssign_acc]
      rfl
    | unit | pair _ _ =>
      simp only [emitCoreToVar, emitAssignRet, Option.map_some]
      simp [List.nil_append]
  | opTail op | opTailAddr op | opTailFlag op =>
    simp only [emitCoreToVar]
    rw [emitLetOp_acc]
    cases emitLetOp tag c {} d op with
    | none => simp
    | some e0 =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      rw [emitAssign_acc, emitAssign_acc (e := e0)]
      simp [List.append_assoc]
  | stmtTail s =>
    simp only [emitCoreToVar]
    rw [emitStmt_acc]
    rfl
  | revertTail err args =>
    simp only [emitCoreToVar]
    rw [emitCustomError_acc]
    rfl
  | letOp op k ih =>
    simp only [emitCoreToVar]
    rw [emitLetOp_acc]
    cases emitLetOp tag c {} d op with
    | none => simp
    | some e0 =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      rw [ih { acc := e0.acc ++ e.acc } (d + 1), ih e0 (d + 1)]
      cases emitCoreToVar tag c {} (d + 1) dest k with
      | none => simp
      | some _ => simp [List.append_assoc]
  | seq s k ih =>
    simp only [emitCoreToVar]
    rw [emitStmt_acc]
    rw [ih { acc := (emitStmt tag c {} d s).acc ++ e.acc } d, ih (emitStmt tag c {} d s) d]
    cases emitCoreToVar tag c {} d dest k with
    | none => simp
    | some _ => simp [List.append_assoc]
  | letPure p args k ih =>
    simp only [emitCoreToVar]
    rw [emitLet_acc]
    rw [ih { acc := (emitLet {} (identV tag d) (emitPrim tag d p args)).acc ++ e.acc }
        (d + 1),
      ih (emitLet {} (identV tag d) (emitPrim tag d p args)) (d + 1)]
    cases emitCoreToVar tag c {} (d + 1) dest k with
    | none => simp
    | some _ => simp [List.append_assoc]
  | ite cond a b =>
    simp only [emitCoreToVar]
    cases emitCoreToVar tag c {} d dest a with
    | none => simp
    | some _ =>
      cases emitCoreToVar tag c {} d dest b with
      | none => simp
      | some _ => simp [Emit.push]
  | @seqIf tBr _ cond th el k _ _ ihk =>
    cases tBr with
    | unit =>
      simp only [emitCoreToVar]
      cases hA : emitCoreToVar tag c {} d dest th with
      | none => simp
      | some eA =>
        cases hB : emitCoreToVar tag c {} d dest el with
        | none => simp
        | some eB =>
          simp only [hA, hB, Bind.bind, Option.bind, Pure.pure]
          rw [ihk (e.push (.switch (emitCond tag d cond)
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))) d]
          rw [ihk (({} : Emit).push (.switch (emitCond tag d cond)
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))) d]
          cases emitCoreToVar tag c {} d dest k with
          | none => simp
          | some _ => simp [Emit.push, List.append_assoc]
    | word | addr | flag =>
      simp only [emitCoreToVar]
      cases hA : emitCoreToVar tag c {} d (identPhi tag d) th with
      | none => simp
      | some eA =>
        cases hB : emitCoreToVar tag c {} d (identPhi tag d) el with
        | none => simp
        | some eB =>
          simp only [hA, hB, Bind.bind, Option.bind, Pure.pure]
          rw [emitSeqIfWord_acc]
          rw [ihk ({ acc := (emitSeqIfWord tag {} d cond eA eB).acc ++ e.acc } : Emit)
            (d + 1)]
          rw [ihk (emitSeqIfWord tag {} d cond eA eB) (d + 1)]
          cases emitCoreToVar tag c {} (d + 1) dest k with
          | none => simp
          | some _ => simp [List.append_assoc]
    | pair _ _ => simp [emitCoreToVar]

theorem emitCoreToVar_prefix {c t} {core : Core t}
    {e e' : Emit} {d : Nat} {dest : YIdent}
    (hem : emitCoreToVar tag c e d dest core = some e') :
    ∃ e0, emitCoreToVar tag c {} d dest core = some e0 ∧
      e'.stmts = e.stmts ++ e0.stmts := by
  have h := emitCoreToVar_acc tag (c := c) core e d dest
  rw [h] at hem
  cases h0 : emitCoreToVar tag c {} d dest core with
  | none => simp [h0] at hem
  | some e0 =>
    simp [h0] at hem
    exact ⟨e0, rfl, by cases hem; exact Emit.cat_stmts e e0⟩

/-- On unit cores, `emitCoreToVar` ignores `dest` and matches `emitCore` with
`haltUnit = false`. -/
theorem emitCoreToVar_eq_emitCore_unit_gen tag {c : ContractDef} {t : RetTy}
    (core : Core t) (e : Emit) (d : Nat) (dest : YIdent) (ht : t = .unit) :
    emitCoreToVar tag c e d dest core = emitCore tag c e d false core false := by
  induction core generalizing e d dest with
  | ret r =>
    cases r with
    | unit => simp [emitCoreToVar, emitAssignRet, emitCore, emitRet, emitReturnUnit]
    | word _ | addr _ | flag _ | pair _ _ => cases ht
  | opTail _ | opTailAddr _ | opTailFlag _ => cases ht
  | stmtTail s =>
    simp [emitCoreToVar, emitCore, emitReturnUnit]
  | revertTail err args =>
    simp [emitCoreToVar, emitCore]
  | letOp op k ih =>
    simp only [emitCoreToVar, emitCore]
    cases emitLetOp tag c e d op with
    | none => simp
    | some e1 => exact ih e1 (d + 1) dest ht
  | seq s k ih =>
    simp [emitCoreToVar, emitCore]
    exact ih _ d dest ht
  | letPure p args k ih =>
    simp [emitCoreToVar, emitCore]
    exact ih _ (d + 1) dest ht
  | ite cond a b iha ihb =>
    simp only [emitCoreToVar, emitCore]
    rw [iha {} d dest ht, ihb {} d dest ht]
  | @seqIf tBr _ cond th el k ihth ihel ihk =>
    cases tBr with
    | unit =>
      simp only [emitCoreToVar, emitCore]
      rw [ihth {} d dest rfl, ihel {} d dest rfl]
      cases emitCore tag c {} d false th false with
      | none => simp
      | some eA =>
        cases emitCore tag c {} d false el false with
        | none => simp
        | some eB =>
          simp only [Bind.bind, Option.bind, Pure.pure]
          exact ihk _ d dest ht
    | word | addr | flag =>
      simp only [emitCoreToVar, emitCore]
      cases emitCoreToVar tag c {} d (identPhi tag d) th with
      | none => simp
      | some eA =>
        cases emitCoreToVar tag c {} d (identPhi tag d) el with
        | none => simp
        | some eB =>
          simp only [Bind.bind, Option.bind, Pure.pure]
          exact ihk (emitSeqIfWord tag e d cond eA eB) (d + 1) dest ht
    | pair _ _ =>
      simp [emitCoreToVar, emitCore]

theorem emitCoreToVar_eq_emitCore_unit tag {c : ContractDef} (core : Core .unit)
    (e : Emit) (d : Nat) (dest : YIdent) :
    emitCoreToVar tag c e d dest core = emitCore tag c e d false core false :=
  emitCoreToVar_eq_emitCore_unit_gen tag core e d dest rfl

mutual
theorem emitCore_some tag {c t} (core : Core t) (e : Emit) (d : Nat)
    (halt : Bool) (clearLock : Bool := false) :
    ∃ e', emitCore tag c e d halt core clearLock = some e' := by
  induction core generalizing e d halt clearLock with
  | ret _ => simp [emitCore]
  | opTail op | opTailAddr op | opTailFlag op =>
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [emitCore, h1]
  | stmtTail _ | revertTail _ _ => simp [emitCore]
  | letOp op k ih =>
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [emitCore, h1]; exact ih e1 (d + 1) halt clearLock
  | seq s k ih => simp [emitCore]; exact ih (emitStmt tag c e d s) d halt clearLock
  | letPure p args k ih =>
    simp [emitCore]; exact ih (emitLet e (identV tag d) (emitPrim tag d p args)) (d + 1)
      halt clearLock
  | ite _ a b iha ihb =>
    obtain ⟨eA, hA⟩ := iha ({} : Emit) d halt clearLock
    obtain ⟨eB, hB⟩ := ihb ({} : Emit) d halt clearLock
    simp [emitCore, hA, hB]
  | @seqIf tBr _ cond th el k ihth ihel ihk =>
    cases tBr with
    | unit =>
      obtain ⟨eA, hA⟩ := ihth ({} : Emit) d false false
      obtain ⟨eB, hB⟩ := ihel ({} : Emit) d false false
      simp [emitCore, hA, hB]
      exact ihk _ d halt clearLock
    | word | addr | flag =>
      obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d
        (identPhi tag d)
      obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d
        (identPhi tag d)
      simp [emitCore, hA, hB]
      exact ihk _ (d + 1) halt clearLock
    | pair _ _ => simp [emitCore]

theorem emitCoreToVar_some tag {c t} (core : Core t) (e : Emit) (d : Nat)
    (dest : YIdent) :
    ∃ e', emitCoreToVar tag c e d dest core = some e' := by
  induction core generalizing e d dest with
  | ret r =>
    cases r <;> simp [emitCoreToVar, emitAssignRet]
  | opTail op | opTailAddr op | opTailFlag op =>
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [emitCoreToVar, h1]
  | stmtTail _ | revertTail _ _ => simp [emitCoreToVar]
  | letOp op k ih =>
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [emitCoreToVar, h1]; exact ih e1 (d + 1) dest
  | seq s k ih => simp [emitCoreToVar]; exact ih (emitStmt tag c e d s) d dest
  | letPure p args k ih =>
    simp [emitCoreToVar]
    exact ih (emitLet e (identV tag d) (emitPrim tag d p args)) (d + 1) dest
  | ite _ a b iha ihb =>
    obtain ⟨eA, hA⟩ := iha ({} : Emit) d dest
    obtain ⟨eB, hB⟩ := ihb ({} : Emit) d dest
    simp [emitCoreToVar, hA, hB]
  | @seqIf tBr _ cond th el k ihth ihel ihk =>
    cases tBr with
    | unit =>
      obtain ⟨eA, hA⟩ := ihth ({} : Emit) d dest
      obtain ⟨eB, hB⟩ := ihel ({} : Emit) d dest
      simp [emitCoreToVar, hA, hB]
      exact ihk _ d dest
    | word | addr | flag =>
      obtain ⟨eA, hA⟩ := ihth ({} : Emit) d (identPhi tag d)
      obtain ⟨eB, hB⟩ := ihel ({} : Emit) d (identPhi tag d)
      simp [emitCoreToVar, hA, hB]
      exact ihk _ (d + 1) dest
    | pair _ _ => simp [emitCoreToVar]
end

/-! ## `funDef`-freedom so `hoist` of emitted blocks is `[]` -/

@[simp] theorem notFunDef_letDecl {xs e} : notFunDef (.letDecl xs e) = true := rfl
@[simp] theorem notFunDef_expr {e} : notFunDef (.exprStmt e) = true := rfl
@[simp] theorem notFunDef_cond {c b} : notFunDef (.cond c b) = true := rfl
@[simp] theorem notFunDef_switch {c cases d} : notFunDef (.switch c cases d) = true := rfl
@[simp] theorem notFunDef_assign {xs e} : notFunDef (.assign xs e) = true := rfl
@[simp] theorem notFunDef_block {b} : notFunDef (.block b) = true := rfl
@[simp] theorem notFunDef_lockClear : notFunDef lockClearStmt = true := rfl
@[simp] theorem notFunDef_lockSet : notFunDef lockSetStmt = true := rfl
@[simp] theorem notFunDef_lockCheck : notFunDef lockCheckStmt = true := rfl

def Emit.noFun (e : Emit) : Prop := ∀ s ∈ e.acc, notFunDef s = true

theorem Emit.noFun_stmts {e : Emit} (h : e.noFun) :
    ∀ s ∈ e.stmts, notFunDef s = true := by
  intro s hs
  exact h s (List.mem_reverse.mp hs)

theorem noFun_nil : ({} : Emit).noFun := by intro _ h; cases h

theorem noFun_push {e : Emit} {s : YStmt} (he : e.noFun) (hs : notFunDef s = true) :
    (e.push s).noFun := by
  intro t ht
  simp [Emit.push] at ht
  rcases ht with rfl | ht
  · exact hs
  · exact he t ht

theorem noFun_lockClear {e : Emit} (he : e.noFun) : (emitLockClear e).noFun :=
  noFun_push he rfl

theorem noFun_do {e op args} (he : e.noFun) : (emitDo e op args).noFun := noFun_push he rfl
theorem noFun_let {e n x} (he : e.noFun) : (emitLet e n x).noFun := noFun_push he rfl
theorem noFun_assign {e n x} (he : e.noFun) : (emitAssign e n x).noFun := noFun_push he rfl
theorem noFun_block {e b} (he : e.noFun) : (emitBlock e b).noFun := noFun_push he rfl
theorem noFun_if {e c b} (he : e.noFun) : (emitIf e c b).noFun := noFun_push he rfl

theorem noFun_foldl_mstore {e : Emit} {base i0} {xs : List YExpr} (he : e.noFun) :
    ((xs.foldl (fun p a =>
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1)) (e, i0)).1).noFun := by
  induction xs generalizing e i0 with
  | nil => simpa using he
  | cons a xs ih =>
    simp only [List.foldl_cons]
    exact ih (noFun_do he)

theorem noFun_foldl_mstore_args {e : Emit} {base i0 depth} {args : List Atom} (he : e.noFun) :
    ((args.foldl (fun p a =>
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE tag depth a], p.2 + 1)) (e, i0)).1).noFun := by
  induction args generalizing e i0 with
  | nil => simpa using he
  | cons a args ih =>
    simp only [List.foldl_cons]
    exact ih (noFun_do he)

theorem noFun_panic (e : Emit) (code : Nat) (he : e.noFun) : (emitPanic e code).noFun := by
  simp only [emitPanic]
  exact noFun_do (noFun_do (noFun_do he))

theorem noFun_customError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr)
    (he : e.noFun) : (emitCustomError c e err args).noFun := by
  simp only [emitCustomError]
  exact noFun_do (noFun_foldl_mstore (noFun_do he))

theorem noFun_returnWords (e : Emit) (xs : List YExpr) (he : e.noFun) :
    (emitReturnWords e xs).noFun := by
  cases xs with
  | nil => exact noFun_push he rfl
  | cons _ _ => simp only [emitReturnWords]; exact noFun_do (noFun_foldl_mstore he)

theorem noFun_log1 (e : Emit) (topic : Nat) (args : List YExpr) (he : e.noFun) :
    (emitLog1 e topic args).noFun := by
  simp only [emitLog1]; exact noFun_do (noFun_foldl_mstore he)

theorem noFun_mapSlotPrep (e : Emit) (slot : Nat) (k : YExpr) (he : e.noFun) :
    (emitMapSlotPrep e slot k).noFun := by
  simp only [emitMapSlotPrep]; exact noFun_do (noFun_do he)

theorem noFun_map2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr) (he : e.noFun) :
    (emitMap2SlotPrep e slot k₁ k₂).noFun := by
  simp only [emitMap2SlotPrep]; exact noFun_do (noFun_do (noFun_mapSlotPrep e slot k₁ he))

theorem noFun_addChecked (e : Emit) (name : YIdent) (a b : YExpr) (he : e.noFun) :
    (emitAddChecked e name a b).noFun := by
  simp only [emitAddChecked]; exact noFun_if (noFun_let he)

theorem noFun_subChecked (e : Emit) (name : YIdent) (a b : YExpr) (he : e.noFun) :
    (emitSubChecked e name a b).noFun := by
  simp only [emitSubChecked]; exact noFun_let (noFun_if he)

theorem noFun_mulChecked (e : Emit) (name : YIdent) (a b : YExpr) (he : e.noFun) :
    (emitMulChecked e name a b).noFun := by
  simp only [emitMulChecked, emitMulOverflowGuard]; exact noFun_if (noFun_let he)

theorem noFun_divChecked (e : Emit) (name : YIdent) (a b : YExpr) (he : e.noFun) :
    (emitDivChecked e name a b).noFun := by
  simp only [emitDivChecked]; exact noFun_let (noFun_if he)

theorem noFun_pow10 (e : Emit) (name : YIdent) (d : YExpr) (he : e.noFun) :
    (emitPow10 e name d).noFun := by
  simp only [emitPow10]; exact noFun_let (noFun_if he)

theorem noFun_mulDivDown (e : Emit) (name : YIdent) (a b c : YExpr) (he : e.noFun) :
    (emitMulDivDown e name a b c).noFun := by
  simp only [emitMulDivDown, emitMulOverflowGuard]
  exact noFun_push (noFun_if (noFun_let (noFun_if he))) rfl

theorem noFun_mulDivUp (e : Emit) (name : YIdent) (a b c : YExpr) (he : e.noFun) :
    (emitMulDivUp e name a b c).noFun := by
  simp only [emitMulDivUp, emitMulOverflowGuard]
  exact noFun_push (noFun_if (noFun_let (noFun_if he))) rfl

theorem noFun_callRetCheck (e : Emit) (ret : AbiRet) (he : e.noFun) :
    (emitCallRetCheck e ret).noFun := by
  cases ret <;> simp [emitCallRetCheck] <;> first | exact he | exact noFun_if he

theorem noFun_extCall tag (e : Emit) (depth : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (bindResult : Option YIdent)
    (he : e.noFun) :
    (emitExtCall tag e depth target sel args ret isView bindResult).noFun := by
  cases bindResult with
  | none =>
    simp only [emitExtCall]
    exact noFun_block he
  | some name =>
    simp only [emitExtCall]
    exact noFun_block (noFun_let he)

theorem noFun_extSend tag (e : Emit) (depth : Nat) (target amount : Atom)
    (bindResult : Option YIdent) (he : e.noFun) :
    (emitExtSend tag e depth target amount bindResult).noFun := by
  cases bindResult with
  | none =>
    simp only [emitExtSend]
    exact noFun_block he
  | some name =>
    simp only [emitExtSend]
    exact noFun_block (noFun_let he)

theorem noFun_letOp (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) (he : e.noFun)
    {e1} (h1 : emitLetOp tag c e d op = some e1) : e1.noFun := by
  cases op with
  | load _ | sender | value | timestamp | blockNumber | selfAddress | selfBalance | pure _ =>
    simp [emitLetOp] at h1; cases h1; exact noFun_let he
  | loadMap _ _ =>
    simp [emitLetOp] at h1; cases h1; exact noFun_let (noFun_mapSlotPrep _ _ _ he)
  | loadMap2 _ _ _ =>
    simp [emitLetOp] at h1; cases h1; exact noFun_let (noFun_map2SlotPrep _ _ _ _ he)
  | addChecked _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_addChecked _ _ _ _ he
  | subChecked _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_subChecked _ _ _ _ he
  | mulChecked _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_mulChecked _ _ _ _ he
  | divChecked _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_divChecked _ _ _ _ he
  | mulDivDown _ _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_mulDivDown _ _ _ _ _ he
  | mulDivUp _ _ _ => simp [emitLetOp] at h1; cases h1; exact noFun_mulDivUp _ _ _ _ _ he
  | pow10 _ => simp [emitLetOp] at h1; cases h1; exact noFun_pow10 _ _ _ he
  | call t sel args ret =>
    simp [emitLetOp] at h1; cases h1
    exact noFun_extCall tag e _ t sel args ret false _ he
  | view t sel args ret =>
    simp [emitLetOp] at h1; cases h1
    exact noFun_extCall tag e _ t sel args ret true _ he
  | send t amt =>
    simp [emitLetOp] at h1; cases h1
    exact noFun_extSend tag e _ t amt _ he

theorem noFun_stmt tag (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt) (he : e.noFun) :
    (emitStmt tag c e d s).noFun := by
  cases s with
  | store _ _ => simp only [emitStmt]; exact noFun_do he
  | storeMap _ _ _ => simp only [emitStmt]; exact noFun_do (noFun_mapSlotPrep _ _ _ he)
  | storeMap2 _ _ _ _ => simp only [emitStmt]; exact noFun_do (noFun_map2SlotPrep _ _ _ _ he)
  | require _ _ _ => simp only [emitStmt]; exact noFun_if he
  | emit _ _ => simp only [emitStmt]; exact noFun_log1 _ _ _ he
  | revert _ _ => simp only [emitStmt]; exact noFun_customError _ _ _ _ he
  | call t sel args ret =>
    simp only [emitStmt]; exact noFun_extCall tag e _ t sel args ret false none he
  | view t sel args ret =>
    simp only [emitStmt]; exact noFun_extCall tag e _ t sel args ret true none he

theorem noFun_ret tag (e : Emit) (d : Nat) (halt : Bool)
    {t} (r : RetExpr t) (clearLock : Bool := false) (he : e.noFun) :
    (emitRet tag e d halt r clearLock).noFun := by
  cases clearLock with
  | false =>
    cases r with
    | unit =>
      cases halt with
      | false => simpa [emitRet, emitReturnUnit] using he
      | true => simp only [emitRet, emitReturnUnit]; exact noFun_push he rfl
    | word _ | addr _ | flag _ | pair _ _ => simp only [emitRet]; exact noFun_returnWords _ _ he
  | true =>
    cases r with
    | unit =>
      cases halt with
      | false => simpa [emitRet, emitReturnUnit] using noFun_lockClear he
      | true => simp only [emitRet, emitReturnUnit]; exact noFun_push (noFun_lockClear he) rfl
    | word _ | addr _ | flag _ | pair _ _ =>
      simp only [emitRet]; exact noFun_returnWords _ _ (noFun_lockClear he)

theorem noFun_core tag {c halt clearLock t} :
    ∀ (core : Core t) (e : Emit) (d : Nat) {e' : Emit},
      emitCore tag c e d halt core clearLock = some e' → e.noFun → e'.noFun := by
  intro core
  induction core with
  | ret r =>
    intro e d e' hem he; simp [emitCore] at hem; cases hem; exact noFun_ret tag e d halt r clearLock he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [h1] at hem; cases hem
    exact noFun_ret tag e1 (d + 1) halt _ clearLock (noFun_letOp tag c e d op he h1)
  | stmtTail s =>
    intro e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noFun_ret tag (emitStmt tag c e d s) d halt .unit clearLock
      (noFun_stmt tag c e d s he)
  | revertTail err args =>
    intro e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noFun_customError c e err _ he
  | letOp op k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [h1] at hem
    exact ih e1 (d + 1) hem (noFun_letOp tag c e d op he h1)
  | seq s k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    exact ih (emitStmt tag c e d s) d hem (noFun_stmt tag c e d s he)
  | letPure p args k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    exact ih _ (d + 1) hem (noFun_let he)
  | ite cond a b =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := halt) (clearLock := clearLock)
      a ({} : Emit) d
    obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := halt) (clearLock := clearLock)
      b ({} : Emit) d
    simp [hA, hB] at hem; cases hem
    exact noFun_push he rfl
  | @seqIf tBr _ cond th el k _ _ ihk =>
    intro e d e' hem he
    cases tBr with
    | unit =>
      simp [emitCore] at hem
      obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        th ({} : Emit) d
      obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        el ({} : Emit) d
      simp [hA, hB] at hem
      exact ihk _ d hem (noFun_push he notFunDef_switch)
    | word | addr | flag =>
      simp [emitCore] at hem
      obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d (identPhi tag d)
      obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d (identPhi tag d)
      simp [hA, hB] at hem
      exact ihk _ (d + 1) hem (noFun_block (noFun_let he))
    | pair _ _ =>
      simp [emitCore] at hem; cases hem; exact he

theorem noFun_coreToVar tag {c t} :
    ∀ (core : Core t) (e : Emit) (d : Nat) (dest : YIdent) {e' : Emit},
      emitCoreToVar tag c e d dest core = some e' → e.noFun → e'.noFun := by
  intro core
  induction core with
  | ret r =>
    intro e d dest e' hem he
    cases r with
    | word _ | addr _ | flag _ =>
      simp [emitCoreToVar, emitAssignRet] at hem; cases hem; exact noFun_assign he
    | unit | pair _ _ =>
      simp [emitCoreToVar, emitAssignRet] at hem; cases hem; exact he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [h1] at hem; cases hem
    exact noFun_assign (noFun_letOp tag c e d op he h1)
  | stmtTail s =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem; cases hem
    exact noFun_stmt tag c e d s he
  | revertTail err args =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem; cases hem
    exact noFun_customError c e err _ he
  | letOp op k ih =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some tag c e d op
    simp [h1] at hem
    exact ih e1 (d + 1) dest hem (noFun_letOp tag c e d op he h1)
  | seq s k ih =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem
    exact ih (emitStmt tag c e d s) d dest hem (noFun_stmt tag c e d s he)
  | letPure p args k ih =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem
    exact ih _ (d + 1) dest hem (noFun_let he)
  | ite cond a b =>
    intro e d dest e' hem he
    simp [emitCoreToVar] at hem
    obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) a ({} : Emit) d dest
    obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) b ({} : Emit) d dest
    simp [hA, hB] at hem; cases hem
    exact noFun_push he notFunDef_switch
  | @seqIf tBr _ cond th el k _ _ ihk =>
    intro e d dest e' hem he
    cases tBr with
    | unit =>
      simp [emitCoreToVar] at hem
      obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d dest
      obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d dest
      simp [hA, hB] at hem
      exact ihk _ d dest hem (noFun_push he notFunDef_switch)
    | word | addr | flag =>
      simp [emitCoreToVar] at hem
      obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d (identPhi tag d)
      obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d (identPhi tag d)
      simp [hA, hB] at hem
      exact ihk _ (d + 1) dest hem (noFun_block (noFun_let he))
    | pair _ _ =>
      simp [emitCoreToVar] at hem; cases hem; exact he

theorem hoist_emitCoreToVar tag {c t} {core : Core t} {e' d dest}
    (hem : emitCoreToVar tag c {} d dest core = some e') :
    hoist evm e'.stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_coreToVar tag core {} d dest hem noFun_nil))

theorem hoist_emitCore tag {c halt clearLock t} {core : Core t} {e' d}
    (hem : emitCore tag c {} d halt core clearLock = some e') :
    hoist evm e'.stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_core tag core {} d hem noFun_nil))

theorem hoist_emitStmt (c : ContractDef) (d : Nat) (s : Lsc.Stmt) :
    hoist evm (emitStmt tag c {} d s).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_stmt tag c {} d s noFun_nil))

theorem hoist_panic (code : Nat) : hoist evm (emitPanic {} code).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_panic {} code noFun_nil))

theorem hoist_customError (c : ContractDef) (err : Nat) (args : List YExpr) :
    hoist evm (emitCustomError c {} err args).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_customError c {} err args noFun_nil))

theorem emitParams_acc (e : Emit) (off n : Nat) :
    emitParams tag e off n = { acc := (emitParams tag {} off n).acc ++ e.acc } := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    dsimp only [emitParams]
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show (List.range n).foldl (fun e i =>
          e.push (.letDecl [identV tag i] (some (bop Op.calldataload [lit (off + 32 * i)])))) e =
        emitParams tag e off n from rfl]
    rw [ih]
    simp [Emit.push, emitParams]

/-! ## `NoExternalOps` of emitted CallFree Yul -/

theorem noExtBlock_append {a b : YBlock}
    (ha : noExtBlock a = true) (hb : noExtBlock b = true) :
    noExtBlock (a ++ b) = true := by
  induction a with
  | nil => simpa [noExtBlock] using hb
  | cons s rest ih =>
    simp [noExtBlock, noExtStmts, Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ih ha.2⟩

theorem noExt_atomE tag (d : Nat) (a : Atom) : noExtExpr (atomE tag d a) = true := by
  cases a with
  | var i =>
    simp only [atomE]
    split_ifs <;> rfl
  | lit n => rfl

theorem noExt_lit (n : Nat) : noExtExpr (lit n) = true := rfl
theorem noExt_var (x : YIdent) : noExtExpr (var x) = true := rfl

theorem noExt_bop {op : YOp} {args : List YExpr}
    (hop : noExtOp op = true) (ha : noExtExprs args = true) :
    noExtExpr (bop op args) = true := by
  change (noExtOp op && noExtExprs args) = true
  simp [hop, ha]

theorem noExtExprs_cons_true {e es}
    (he : noExtExpr e = true) (hs : noExtExprs es = true) :
    noExtExprs (e :: es) = true := by
  simp [he, hs]

theorem noExt_push {e : Emit} {s : YStmt}
    (he : noExtBlock e.stmts = true) (hs : noExtStmt s = true) :
    noExtBlock (e.push s).stmts = true := by
  simpa [Emit.stmts_push] using noExtBlock_append he (by simp [noExtBlock, noExtStmts, hs])

theorem noExt_nil : noExtBlock ({} : Emit).stmts = true := by
  simp [Emit.stmts_nil, noExtBlock]

theorem noExt_do {e op args} (he : noExtBlock e.stmts = true)
    (hop : noExtOp op = true) (ha : noExtExprs args = true) :
    noExtBlock (emitDo e op args).stmts = true :=
  noExt_push he (by
    change noExtExpr (bop op args) = true
    exact noExt_bop hop ha)

theorem noExt_let {e n x} (he : noExtBlock e.stmts = true) (hx : noExtExpr x = true) :
    noExtBlock (emitLet e n x).stmts = true :=
  noExt_push he (by simp [noExtStmt, hx])

theorem noExt_if {e cnd b} (he : noExtBlock e.stmts = true)
    (hc : noExtExpr cnd = true) (hb : noExtBlock b = true) :
    noExtBlock (emitIf e cnd b).stmts = true :=
  noExt_push he (by simp [noExtStmt, hc]; exact hb)

theorem noExt_assign {e n x} (he : noExtBlock e.stmts = true) (hx : noExtExpr x = true) :
    noExtBlock (emitAssign e n x).stmts = true :=
  noExt_push he (by simp [noExtStmt, hx])

theorem noExt_block {e b} (he : noExtBlock e.stmts = true) (hb : noExtBlock b = true) :
    noExtBlock (emitBlock e b).stmts = true :=
  noExt_push he (by simp [noExtStmt]; exact hb)

theorem noExt_params (off n : Nat) :
    noExtBlock (emitParams tag {} off n).stmts = true := by
  induction n with
  | zero => simp [emitParams, Emit.stmts_nil, noExtBlock]
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    simp only [emitParams]
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact noExt_push (e := emitParams tag {} off n) ih
      (by
        simp [noExtStmt]
        exact noExt_bop (op := YulSemantics.EVM.Op.calldataload) rfl
          (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_keccak064 : noExtExpr keccak064 = true :=
  noExt_bop rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_stop : noExtStmt stopStmt = true :=
  noExt_bop (op := YulSemantics.EVM.Op.stop) rfl noExtExprs_nil

theorem noExt_lockClearStmt : noExtStmt lockClearStmt = true :=
  noExt_bop (op := YulSemantics.EVM.Op.tstore) rfl
    (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_maybeLock (clearLock : Bool) :
    noExtBlock (if clearLock then [lockClearStmt] else []) = true := by
  cases clearLock <;> simp [noExtBlock, noExtStmts, noExt_lockClearStmt]

theorem noExt_lockSetStmt : noExtStmt lockSetStmt = true :=
  noExt_bop (op := YulSemantics.EVM.Op.tstore) rfl
    (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_revert00 : noExtStmt revert00 = true :=
  noExt_bop (op := YulSemantics.EVM.Op.revert) rfl
    (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_lockCheckStmt : noExtStmt lockCheckStmt = true := by
  unfold lockCheckStmt noExtStmt
  rw [noExt_bop (op := YulSemantics.EVM.Op.tload) rfl
    (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil)]
  simp [noExtStmts, noExt_revert00]

theorem noExt_valueCheckStmt : noExtStmt valueCheckStmt = true := by
  unfold valueCheckStmt noExtStmt
  rw [noExt_bop (op := YulSemantics.EVM.Op.callvalue) rfl noExtExprs_nil]
  simp [noExtStmts, noExt_revert00]

theorem noExt_valueCheckPrefix (f : FnDef) : noExtStmts (valueCheckPrefix f) = true := by
  cases hpay : f.payable
  · simp [valueCheckPrefix, hpay, noExtStmts, noExt_valueCheckStmt]
  · simp [valueCheckPrefix, hpay, noExtStmts]

theorem noExt_lockClear (e : Emit) (he : noExtBlock e.stmts = true) :
    noExtBlock (emitLockClear e).stmts = true :=
  noExt_push he noExt_lockClearStmt

theorem noExt_switch {e : Emit} {cnd : YExpr} {cases : List (YulSemantics.Literal × YBlock)}
    {dflt : Option YBlock}
    (he : noExtBlock e.stmts = true) (hc : noExtExpr cnd = true)
    (hcs : noExtCases cases = true)
    (hd : match dflt with | none => True | some b => noExtBlock b = true) :
    noExtBlock (e.push (.switch cnd cases dflt)).stmts = true :=
  noExt_push he (by
    cases dflt with
    | none =>
      simp [noExtStmt, hc, hcs]
    | some b =>
      have hb : noExtStmts b = true := by simpa [noExtBlock] using hd
      simp [noExtStmt, hc, hcs, hb])

theorem noExt_emitCond (d : Nat) : ∀ c, noExtExpr (emitCond tag d c) = true := by
  intro c
  induction c with
  | lt a b =>
    exact noExt_bop (op := YulSemantics.EVM.Op.lt) rfl
      (noExtExprs_cons_true (noExt_atomE tag d a) (noExtExprs_cons_true (noExt_atomE tag d b) noExtExprs_nil))
  | le a b =>
    exact noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl
      (noExtExprs_cons_true
        (noExt_bop (op := YulSemantics.EVM.Op.lt) rfl
          (noExtExprs_cons_true (noExt_atomE tag d b) (noExtExprs_cons_true (noExt_atomE tag d a) noExtExprs_nil)))
        noExtExprs_nil)
  | eq a b =>
    exact noExt_bop (op := YulSemantics.EVM.Op.eq) rfl
      (noExtExprs_cons_true (noExt_atomE tag d a) (noExtExprs_cons_true (noExt_atomE tag d b) noExtExprs_nil))
  | ne a b =>
    exact noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl
      (noExtExprs_cons_true
        (noExt_bop (op := YulSemantics.EVM.Op.eq) rfl
          (noExtExprs_cons_true (noExt_atomE tag d a) (noExtExprs_cons_true (noExt_atomE tag d b) noExtExprs_nil)))
        noExtExprs_nil)
  | and c1 c2 ih1 ih2 =>
    exact noExt_bop (op := YulSemantics.EVM.Op.and) rfl
      (noExtExprs_cons_true ih1 (noExtExprs_cons_true ih2 noExtExprs_nil))
  | or c1 c2 ih1 ih2 =>
    exact noExt_bop (op := YulSemantics.EVM.Op.or) rfl
      (noExtExprs_cons_true ih1 (noExtExprs_cons_true ih2 noExtExprs_nil))
  | not c ih =>
    exact noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl
      (noExtExprs_cons_true ih noExtExprs_nil)
  | tt | ff => exact noExt_lit _

theorem noExt_seqIfWordInner (d : Nat) (cond : Cond) (eA eB : Emit)
    (hA : noExtBlock eA.stmts = true) (hB : noExtBlock eB.stmts = true) :
    noExtBlock (seqIfWordInner tag d cond eA eB) = true := by
  rw [seqIfWordInner_eq]
  simp [noExtBlock, noExtStmts, noExtStmt, noExtCases, noExt_emitCond, noExt_lit,
    noExtExpr]
  simpa [noExtBlock, noExt_var] using And.intro hB hA

theorem noExt_emitSeqIfWord (e : Emit) (d : Nat) (cond : Cond) (eA eB : Emit)
    (he : noExtBlock e.stmts = true)
    (hA : noExtBlock eA.stmts = true) (hB : noExtBlock eB.stmts = true) :
    noExtBlock (emitSeqIfWord tag e d cond eA eB).stmts = true :=
  noExt_block (noExt_let he (noExt_lit 0)) (noExt_seqIfWordInner tag d cond eA eB hA hB)

theorem noExt_emitPrim (d : Nat) (p : Prim) (args : List Atom) :
    noExtExpr (emitPrim tag d p args) = true := by
  simp only [emitPrim]
  split
  · exact noExt_atomE tag d _
  · exact noExt_bop (op := YulSemantics.EVM.Op.add) rfl
      (noExtExprs_cons_true (noExt_atomE tag d _) (noExtExprs_cons_true (noExt_atomE tag d _) noExtExprs_nil))
  · exact noExt_bop (op := YulSemantics.EVM.Op.sub) rfl
      (noExtExprs_cons_true (noExt_atomE tag d _) (noExtExprs_cons_true (noExt_atomE tag d _) noExtExprs_nil))
  · exact noExt_bop (op := YulSemantics.EVM.Op.mul) rfl
      (noExtExprs_cons_true (noExt_atomE tag d _) (noExtExprs_cons_true (noExt_atomE tag d _) noExtExprs_nil))
  · exact noExt_lit 0

theorem noExt_foldl_mstore {e : Emit} {base i0 : Nat} {xs : List YExpr}
    (he : noExtBlock e.stmts = true) (hx : ∀ x ∈ xs, noExtExpr x = true) :
    noExtBlock ((xs.foldl (fun p a =>
        (emitDo p.1 YulSemantics.EVM.Op.mstore [lit (base + 32 * p.2), a], p.2 + 1))
      (e, i0)).1).stmts = true := by
  induction xs generalizing e i0 with
  | nil => simpa using he
  | cons a xs ih =>
    simp only [List.foldl_cons]
    exact ih (noExt_do he rfl (noExtExprs_cons_true (noExt_lit _)
      (noExtExprs_cons_true (hx a (by simp)) noExtExprs_nil)))
      (fun x hx' => hx x (by simp [hx']))

theorem noExt_panic (e : Emit) (code : Nat) (he : noExtBlock e.stmts = true) :
    noExtBlock (emitPanic e code).stmts = true := by
  simp only [emitPanic]
  exact noExt_do (noExt_do (noExt_do he
    (op := YulSemantics.EVM.Op.mstore) rfl
      (noExtExprs_cons_true (noExt_lit _)
        (noExtExprs_cons_true
          (noExt_bop rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil)))
          noExtExprs_nil)))
    (op := YulSemantics.EVM.Op.mstore) rfl
      (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil)))
    (op := YulSemantics.EVM.Op.revert) rfl
      (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_customError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr)
    (he : noExtBlock e.stmts = true) (ha : ∀ x ∈ args, noExtExpr x = true) :
    noExtBlock (emitCustomError c e err args).stmts = true := by
  simp only [emitCustomError]
  exact noExt_do (noExt_foldl_mstore (noExt_do he rfl
      (noExtExprs_cons_true (noExt_lit _)
        (noExtExprs_cons_true
          (noExt_bop rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil)))
          noExtExprs_nil)))
    ha)
    (op := YulSemantics.EVM.Op.revert) rfl
      (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_returnWords (e : Emit) (xs : List YExpr) (he : noExtBlock e.stmts = true)
    (hx : ∀ x ∈ xs, noExtExpr x = true) :
    noExtBlock (emitReturnWords e xs).stmts = true := by
  cases xs with
  | nil => exact noExt_push he noExt_stop
  | cons _ _ =>
    simp only [emitReturnWords]
    exact noExt_do (noExt_foldl_mstore he hx)
      (op := YulSemantics.EVM.Op.ret) rfl
        (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_returnUnit (e : Emit) (halt : Bool) (he : noExtBlock e.stmts = true) :
    noExtBlock (emitReturnUnit e halt).stmts = true := by
  cases halt with
  | false => simpa [emitReturnUnit] using he
  | true => simp only [emitReturnUnit]; exact noExt_push he noExt_stop

theorem noExt_log1 (e : Emit) (topic : Nat) (args : List YExpr)
    (he : noExtBlock e.stmts = true) (ha : ∀ x ∈ args, noExtExpr x = true) :
    noExtBlock (emitLog1 e topic args).stmts = true := by
  simp only [emitLog1]
  exact noExt_do (noExt_foldl_mstore he ha)
    (op := YulSemantics.EVM.Op.log1) rfl
      (noExtExprs_cons_true (noExt_lit _)
        (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil)))

theorem noExt_mapSlotPrep (e : Emit) (slot : Nat) (k : YExpr)
    (he : noExtBlock e.stmts = true) (hk : noExtExpr k = true) :
    noExtBlock (emitMapSlotPrep e slot k).stmts = true := by
  simp only [emitMapSlotPrep]
  exact noExt_do (noExt_do he rfl (noExtExprs_cons_true (noExt_lit _)
      (noExtExprs_cons_true hk noExtExprs_nil)))
    rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))

theorem noExt_map2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr)
    (he : noExtBlock e.stmts = true) (h1 : noExtExpr k₁ = true) (h2 : noExtExpr k₂ = true) :
    noExtBlock (emitMap2SlotPrep e slot k₁ k₂).stmts = true := by
  simp only [emitMap2SlotPrep]
  exact noExt_do (noExt_do (noExt_mapSlotPrep e slot k₁ he h1)
      rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true noExt_keccak064 noExtExprs_nil)))
    rfl (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true h2 noExtExprs_nil))

theorem noExt_mulOverflowGuard (e : Emit) (a b p : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true)
    (hb : noExtExpr b = true) (hp : noExtExpr p = true) :
    noExtBlock (emitMulOverflowGuard e a b p).stmts = true := by
  simp only [emitMulOverflowGuard]
  exact noExt_if he
    (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl (noExtExprs_cons_true
      (noExt_bop (op := YulSemantics.EVM.Op.or) rfl (noExtExprs_cons_true
        (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl (noExtExprs_cons_true ha noExtExprs_nil))
        (noExtExprs_cons_true
          (noExt_bop (op := YulSemantics.EVM.Op.eq) rfl (noExtExprs_cons_true
            (noExt_bop (op := YulSemantics.EVM.Op.div) rfl
              (noExtExprs_cons_true hp (noExtExprs_cons_true ha noExtExprs_nil)))
            (noExtExprs_cons_true hb noExtExprs_nil)))
          noExtExprs_nil)))
      noExtExprs_nil))
    (noExt_panic {} 0x11 noExt_nil)

theorem noExt_addChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true) (hb : noExtExpr b = true) :
    noExtBlock (emitAddChecked e name a b).stmts = true := by
  simp only [emitAddChecked]
  exact noExt_if (noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.add) rfl
      (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil))))
    (noExt_bop (op := YulSemantics.EVM.Op.lt) rfl
      (noExtExprs_cons_true (noExt_var name) (noExtExprs_cons_true ha noExtExprs_nil)))
    (noExt_panic {} 0x11 noExt_nil)

theorem noExt_subChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true) (hb : noExtExpr b = true) :
    noExtBlock (emitSubChecked e name a b).stmts = true := by
  simp only [emitSubChecked]
  exact noExt_let (noExt_if he
      (noExt_bop (op := YulSemantics.EVM.Op.lt) rfl
        (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil)))
      (noExt_panic {} 0x11 noExt_nil))
    (noExt_bop (op := YulSemantics.EVM.Op.sub) rfl
      (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil)))

theorem noExt_mulChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true) (hb : noExtExpr b = true) :
    noExtBlock (emitMulChecked e name a b).stmts = true := by
  simp only [emitMulChecked]
  exact noExt_mulOverflowGuard (emitLet e name (bop YulSemantics.EVM.Op.mul [a, b]))
    a b (var name)
    (noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.mul) rfl
      (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil))))
    ha hb (noExt_var name)

theorem noExt_divChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true) (hb : noExtExpr b = true) :
    noExtBlock (emitDivChecked e name a b).stmts = true := by
  simp only [emitDivChecked]
  exact noExt_let (noExt_if he
      (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl (noExtExprs_cons_true hb noExtExprs_nil))
      (noExt_panic {} 0x12 noExt_nil))
    (noExt_bop (op := YulSemantics.EVM.Op.div) rfl
      (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil)))

theorem noExt_pow10 (e : Emit) (name : YIdent) (d : YExpr)
    (he : noExtBlock e.stmts = true) (hd : noExtExpr d = true) :
    noExtBlock (emitPow10 e name d).stmts = true := by
  simp only [emitPow10]
  exact noExt_let (noExt_if he
      (noExt_bop (op := YulSemantics.EVM.Op.gt) rfl
        (noExtExprs_cons_true hd (noExtExprs_cons_true (noExt_lit 77) noExtExprs_nil)))
      (noExt_panic {} 0x11 noExt_nil))
    (noExt_bop (op := YulSemantics.EVM.Op.exp) rfl
      (noExtExprs_cons_true (noExt_lit 10) (noExtExprs_cons_true hd noExtExprs_nil)))

theorem noExt_mulDivDown (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true)
    (hb : noExtExpr b = true) (hc : noExtExpr c = true) :
    noExtBlock (emitMulDivDown e name a b c).stmts = true := by
  simp only [emitMulDivDown]
  exact noExt_assign
    (noExt_mulOverflowGuard
      (emitLet (emitIf e (bop YulSemantics.EVM.Op.iszero [c]) (emitPanic {} 0x12).stmts)
        name (bop YulSemantics.EVM.Op.mul [a, b]))
      a b (var name)
      (noExt_let (noExt_if he
          (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl (noExtExprs_cons_true hc noExtExprs_nil))
          (noExt_panic {} 0x12 noExt_nil))
        (noExt_bop (op := YulSemantics.EVM.Op.mul) rfl
          (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil))))
      ha hb (noExt_var name))
    (noExt_bop (op := YulSemantics.EVM.Op.div) rfl
      (noExtExprs_cons_true (noExt_var name) (noExtExprs_cons_true hc noExtExprs_nil)))

theorem noExt_assign_div_mod (name : YIdent) (c : YExpr) (hc : noExtExpr c = true) :
    noExtStmt (.assign [name] (bop YulSemantics.EVM.Op.div [var name, c])) = true :=
  noExt_bop (op := YulSemantics.EVM.Op.div) rfl
    (noExtExprs_cons_true (noExt_var name) (noExtExprs_cons_true hc noExtExprs_nil))

theorem noExt_mulDivUp (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noExtBlock e.stmts = true) (ha : noExtExpr a = true)
    (hb : noExtExpr b = true) (hc : noExtExpr c = true) :
    noExtBlock (emitMulDivUp e name a b c).stmts = true := by
  simp only [emitMulDivUp]
  refine noExt_switch
    (e := emitMulOverflowGuard
      (emitLet (emitIf e (bop YulSemantics.EVM.Op.iszero [c]) (emitPanic {} 0x12).stmts)
        name (bop YulSemantics.EVM.Op.mul [a, b]))
      a b (var name))
    (noExt_mulOverflowGuard
      (emitLet (emitIf e (bop YulSemantics.EVM.Op.iszero [c]) (emitPanic {} 0x12).stmts)
        name (bop YulSemantics.EVM.Op.mul [a, b]))
      a b (var name)
      (noExt_let (noExt_if he
          (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl (noExtExprs_cons_true hc noExtExprs_nil))
          (noExt_panic {} 0x12 noExt_nil))
        (noExt_bop (op := YulSemantics.EVM.Op.mul) rfl
          (noExtExprs_cons_true ha (noExtExprs_cons_true hb noExtExprs_nil))))
      ha hb (noExt_var name))
    (noExt_bop (op := YulSemantics.EVM.Op.mod) rfl
      (noExtExprs_cons_true (noExt_var name) (noExtExprs_cons_true hc noExtExprs_nil)))
    (by
      change (noExtStmts [.assign [name] (bop YulSemantics.EVM.Op.div [var name, c])] &&
          noExtCases []) = true
      simp [noExt_assign_div_mod name c hc])
    (by
      change noExtBlock
        [.assign [name] (bop YulSemantics.EVM.Op.add
          [bop YulSemantics.EVM.Op.div [var name, c], lit 1])] = true
      simp [noExtBlock, noExtStmts, noExtStmt]
      exact noExt_bop (op := YulSemantics.EVM.Op.add) rfl (noExtExprs_cons_true
        (noExt_bop (op := YulSemantics.EVM.Op.div) rfl
          (noExtExprs_cons_true (noExt_var name) (noExtExprs_cons_true hc noExtExprs_nil)))
        (noExtExprs_cons_true (noExt_lit 1) noExtExprs_nil)))

theorem noExt_atomEs tag (d : Nat) (as : List Atom) :
    ∀ x ∈ as.map (atomE tag d), noExtExpr x = true := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact noExt_atomE tag d a

theorem noExt_ret (e : Emit) (d : Nat) (halt : Bool)
    {t} (r : RetExpr t)
    (he : noExtBlock e.stmts = true)
    (clearLock : Bool := false) :
    noExtBlock (emitRet tag e d halt r clearLock).stmts = true := by
  cases clearLock with
  | false =>
    cases r with
    | unit => simp only [emitRet]; exact noExt_returnUnit e halt he
    | word a | addr a | flag a =>
      simp only [emitRet]
      exact noExt_returnWords e _ he (noExt_atomEs tag d _)
    | pair a b =>
      simp only [emitRet]
      exact noExt_returnWords e _ he (noExt_atomEs tag d _)
  | true =>
    cases r with
    | unit => simp only [emitRet]; exact noExt_returnUnit _ halt (noExt_lockClear e he)
    | word a | addr a | flag a =>
      simp only [emitRet]
      exact noExt_returnWords _ _ (noExt_lockClear e he) (noExt_atomEs tag d _)
    | pair a b =>
      simp only [emitRet]
      exact noExt_returnWords _ _ (noExt_lockClear e he) (noExt_atomEs tag d _)

end Lsc.Compiler
