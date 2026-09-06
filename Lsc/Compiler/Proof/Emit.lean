import Lsc.Compiler.Proof.Env

set_option linter.unusedSimpArgs false

/-!
Accumulator homomorphism: `emit* e = { acc := (emit* {}).acc ++ e.acc }`.
These lemmas are **not** `simp` — rewriting `emitDo {}` with `emitDo_acc` loops.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

theorem Emit.cat_stmts (e e0 : Emit) :
    ({ acc := e0.acc ++ e.acc } : Emit).stmts = e.stmts ++ e0.stmts := by
  simp [Emit.stmts, List.reverse_append]

theorem emitDo_acc (e : Emit) (op : YOp) (args : List YExpr) :
    emitDo e op args = { acc := (emitDo ({} : Emit) op args).acc ++ e.acc } := rfl

theorem emitLet_acc (e : Emit) (n : YIdent) (x : YExpr) :
    emitLet e n x = { acc := (emitLet ({} : Emit) n x).acc ++ e.acc } := rfl

theorem emitIf_acc (e : Emit) (cnd : YExpr) (body : YBlock) :
    emitIf e cnd body = { acc := (emitIf ({} : Emit) cnd body).acc ++ e.acc } := rfl

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
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE depth a], p.2 + 1))
      ({ acc := extra.acc ++ e.acc }, i0)).1 =
      { acc :=
          (args.foldl (fun p a =>
              (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE depth a], p.2 + 1))
            (extra, i0)).1.acc ++ e.acc } := by
  induction args generalizing extra i0 with
  | nil => simp
  | cons a args ih =>
    simp only [List.foldl_cons]
    have hdo :
        emitDo { acc := extra.acc ++ e.acc } Op.mstore [lit (base + 32 * i0), atomE depth a] =
          { acc := (emitDo extra Op.mstore [lit (base + 32 * i0), atomE depth a]).acc ++ e.acc } := by
      simp [emitDo, Emit.push, List.append_assoc]
    rw [hdo]
    exact ih (emitDo extra Op.mstore [lit (base + 32 * i0), atomE depth a]) (i0 + 1)

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

theorem emitExtCall_acc (c : ContractDef) (e : Emit) (depth b m : Nat) (args : List Atom)
    (bindResult : Option YIdent) :
    emitExtCall c e depth b m args bindResult =
      { acc := (emitExtCall c {} depth b m args bindResult).acc ++ e.acc } := by
  simp only [emitExtCall]
  rw [emitLet_acc e]
  rw [emitDo_cat]
  rw [foldl_mstore_args_cat]
  rw [emitLet_cat]
  rw [emitIf_cat]
  rw [emitCallRetCheck_cat]
  cases bindResult with
  | none => rfl
  | some name =>
    cases (bindingMethod c b m).2 <;> exact emitLet_cat _ _ _ _

theorem emitLetOp_acc (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) :
    emitLetOp c e d op =
      (emitLetOp c {} d op).map fun e0 => { acc := e0.acc ++ e.acc } := by
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
  | sender | value | timestamp | blockNumber | selfAddress | pure _ =>
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
  | call b m args =>
    simp only [emitLetOp, Option.map_some]; exact congrArg some (emitExtCall_acc _ _ _ _ _ _ _)

theorem emitLetOp_some (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) :
    ∃ e', emitLetOp c e d op = some e' := by
  cases op <;> simp [emitLetOp]

theorem emitStmt_acc (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt) :
    emitStmt c e d s = { acc := (emitStmt c {} d s).acc ++ e.acc } := by
  cases s with
  | store _ _ => simp [emitStmt, emitDo, Emit.push]
  | storeMap f k v =>
    simp only [emitStmt]; rw [emitMapSlotPrep_acc, emitDo_cat]
  | storeMap2 f k₁ k₂ v =>
    simp only [emitStmt]; rw [emitMap2SlotPrep_acc, emitDo_cat]
  | require _ _ _ => simp [emitStmt, emitIf, Emit.push]
  | emit _ _ => simp only [emitStmt]; exact emitLog1_acc _ _ _
  | revert _ _ => simp only [emitStmt]; exact emitCustomError_acc _ _ _ _
  | call b m args => simp only [emitStmt]; exact emitExtCall_acc _ _ _ _ _ _ _

theorem emitRet_acc (e : Emit) (d : Nat) (halt : Bool) {t} (r : RetExpr t) :
    emitRet e d halt r = { acc := (emitRet {} d halt r).acc ++ e.acc } := by
  cases r with
  | unit => simp only [emitRet]; exact emitReturnUnit_acc _ _
  | word _ | addr _ | flag _ | pair _ _ => simp only [emitRet]; exact emitReturnWords_acc _ _

theorem emitRet_word_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet e d halt (.word a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE d a]).stmts := by
  rw [emitRet_acc e d halt (.word a), Emit.cat_stmts]
  simp only [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitRet_addr_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet e d halt (.addr a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE d a]).stmts := by
  rw [emitRet_acc e d halt (.addr a), Emit.cat_stmts]
  simp only [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitRet_flag_stmts (e : Emit) (d : Nat) (halt : Bool) (a : Atom) :
    (emitRet e d halt (.flag a)).stmts =
      e.stmts ++ (emitReturnWords {} [atomE d a]).stmts := by
  rw [emitRet_acc e d halt (.flag a), Emit.cat_stmts]
  simp only [emitRet, retAtoms, List.map_cons, List.map_nil]

theorem emitCore_acc {c : ContractDef} {halt : Bool} {t : RetTy} :
    ∀ (core : Core t) (e : Emit) (d : Nat),
      emitCore c e d halt core = (emitCore c {} d halt core).map fun e0 =>
        { acc := e0.acc ++ e.acc } := by
  intro core
  induction core with
  | ret r => intro e d; simp only [emitCore]; rw [emitRet_acc]; rfl
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d
    simp only [emitCore]
    rw [emitLetOp_acc]
    cases emitLetOp c {} d op with
    | none => simp
    | some e0 => simp only [Option.map_some, Bind.bind, Option.bind]; rw [emitRet_acc]; rfl
  | stmtTail s =>
    intro e d
    simp only [emitCore, Option.map_some]
    rw [emitStmt_acc, emitReturnUnit_acc, emitReturnUnit_acc (emitStmt c {} d s)]
    simp [List.append_assoc]
  | revertTail err args =>
    intro e d; simp only [emitCore, Option.map_some]; exact congrArg some (emitCustomError_acc _ _ _ _)
  | letOp op k ih =>
    intro e d
    simp only [emitCore]
    rw [emitLetOp_acc]
    cases emitLetOp c {} d op with
    | none => simp
    | some e0 =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      rw [ih { acc := e0.acc ++ e.acc } (d + 1), ih e0 (d + 1)]
      cases emitCore c {} (d + 1) halt k with
      | none => simp
      | some _ => simp [List.append_assoc]
  | seq s k ih =>
    intro e d
    simp only [emitCore]
    rw [emitStmt_acc]
    rw [ih { acc := (emitStmt c {} d s).acc ++ e.acc } d, ih (emitStmt c {} d s) d]
    cases emitCore c {} d halt k with
    | none => simp
    | some _ => simp [List.append_assoc]
  | letPure p args k ih =>
    intro e d
    simp only [emitCore]
    rw [emitLet_acc]
    rw [ih { acc := (emitLet {} (identV d) (emitPrim d p args)).acc ++ e.acc } (d + 1),
      ih (emitLet {} (identV d) (emitPrim d p args)) (d + 1)]
    cases emitCore c {} (d + 1) halt k with
    | none => simp
    | some _ => simp [List.append_assoc]
  | ite cond a b =>
    intro e d
    simp only [emitCore]
    cases emitCore c {} d halt a with
    | none => simp
    | some _ =>
      cases emitCore c {} d halt b with
      | none => simp
      | some _ => simp [Emit.push]

theorem emitCore_prefix {c halt t} {core : Core t}
    {e e' : Emit} {d : Nat} (hem : emitCore c e d halt core = some e') :
    ∃ e0, emitCore c {} d halt core = some e0 ∧ e'.stmts = e.stmts ++ e0.stmts := by
  have h := emitCore_acc (c := c) (halt := halt) core e d
  rw [h] at hem
  cases h0 : emitCore c {} d halt core with
  | none => simp [h0] at hem
  | some e0 =>
    simp [h0] at hem
    exact ⟨e0, rfl, by cases hem; exact Emit.cat_stmts e e0⟩

theorem emitCore_some {c halt t} (core : Core t) (e : Emit) (d : Nat) :
    ∃ e', emitCore c e d halt core = some e' := by
  induction core generalizing e d with
  | ret _ => simp [emitCore]
  | opTail op | opTailAddr op | opTailFlag op =>
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [emitCore, h1]
  | stmtTail _ | revertTail _ _ => simp [emitCore]
  | letOp op k ih =>
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [emitCore, h1]; exact ih e1 (d + 1)
  | seq s k ih => simp [emitCore]; exact ih (emitStmt c e d s) d
  | letPure p args k ih =>
    simp [emitCore]; exact ih (emitLet e (identV d) (emitPrim d p args)) (d + 1)
  | ite _ a b iha ihb =>
    obtain ⟨eA, hA⟩ := iha ({} : Emit) d
    obtain ⟨eB, hB⟩ := ihb ({} : Emit) d
    simp [emitCore, hA, hB]

/-! ## `funDef`-freedom so `hoist` of emitted blocks is `[]` -/

@[simp] theorem notFunDef_letDecl {xs e} : notFunDef (.letDecl xs e) = true := rfl
@[simp] theorem notFunDef_expr {e} : notFunDef (.exprStmt e) = true := rfl
@[simp] theorem notFunDef_cond {c b} : notFunDef (.cond c b) = true := rfl
@[simp] theorem notFunDef_switch {c cases d} : notFunDef (.switch c cases d) = true := rfl
@[simp] theorem notFunDef_assign {xs e} : notFunDef (.assign xs e) = true := rfl
@[simp] theorem notFunDef_block {b} : notFunDef (.block b) = true := rfl
@[simp] theorem notFunDef_stop : notFunDef stopStmt = true := rfl

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

theorem noFun_do {e op args} (he : e.noFun) : (emitDo e op args).noFun := noFun_push he rfl
theorem noFun_let {e n x} (he : e.noFun) : (emitLet e n x).noFun := noFun_push he rfl
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
        (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE depth a], p.2 + 1)) (e, i0)).1).noFun := by
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

theorem noFun_extCall (c : ContractDef) (e : Emit) (depth b m : Nat) (args : List Atom)
    (bindResult : Option YIdent) (he : e.noFun) :
    (emitExtCall c e depth b m args bindResult).noFun := by
  simp only [emitExtCall]
  have hpack :
      (args.foldl (fun p a =>
          (emitDo p.1 Op.mstore [lit (abiAfterSel + 32 * p.2), atomE depth a], p.2 + 1))
        (emitDo (emitLet e s!"_tok_{depth}"
            (bop Op.sload [lit (bindingSlot c b)]))
          Op.mstore
          [lit abiPtr, bop Op.shl [lit 224, lit (bindingMethod c b m).1]], 0)).1.noFun :=
    noFun_foldl_mstore_args (noFun_do (noFun_let he))
  have hok :=
    noFun_let (n := s!"_ok_{depth}") (x := bop YulSemantics.EVM.Op.call
      [lit extCallGas, var s!"_tok_{depth}", lit 0, lit abiPtr,
        lit (4 + 32 * args.length), lit abiPtr, lit 32]) hpack
  have hcall := noFun_callRetCheck _
      (bindingMethod c b m).2
      (noFun_if (c := bop Op.iszero [var s!"_ok_{depth}"]) (b := [revert00]) hok)
  cases bindResult with
  | none => exact hcall
  | some name =>
    revert hcall
    cases (bindingMethod c b m).2 <;> intro hcall <;> exact noFun_let hcall

theorem noFun_letOp (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op) (he : e.noFun)
    {e1} (h1 : emitLetOp c e d op = some e1) : e1.noFun := by
  cases op with
  | load _ | sender | value | timestamp | blockNumber | selfAddress | pure _ =>
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
  | call b m args => simp [emitLetOp] at h1; cases h1; exact noFun_extCall _ _ _ _ _ _ _ he

theorem noFun_stmt (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt) (he : e.noFun) :
    (emitStmt c e d s).noFun := by
  cases s with
  | store _ _ => simp only [emitStmt]; exact noFun_do he
  | storeMap _ _ _ => simp only [emitStmt]; exact noFun_do (noFun_mapSlotPrep _ _ _ he)
  | storeMap2 _ _ _ _ => simp only [emitStmt]; exact noFun_do (noFun_map2SlotPrep _ _ _ _ he)
  | require _ _ _ => simp only [emitStmt]; exact noFun_if he
  | emit _ _ => simp only [emitStmt]; exact noFun_log1 _ _ _ he
  | revert _ _ => simp only [emitStmt]; exact noFun_customError _ _ _ _ he
  | call b m args => simp only [emitStmt]; exact noFun_extCall _ _ _ _ _ _ none he

theorem noFun_ret (e : Emit) (d : Nat) (halt : Bool) {t} (r : RetExpr t) (he : e.noFun) :
    (emitRet e d halt r).noFun := by
  cases r with
  | unit =>
    cases halt with
    | false => simpa [emitRet, emitReturnUnit] using he
    | true => simp only [emitRet, emitReturnUnit]; exact noFun_push he rfl
  | word _ | addr _ | flag _ | pair _ _ => simp only [emitRet]; exact noFun_returnWords _ _ he

theorem noFun_core {c halt t} :
    ∀ (core : Core t) (e : Emit) (d : Nat) {e' : Emit},
      emitCore c e d halt core = some e' → e.noFun → e'.noFun := by
  intro core
  induction core with
  | ret r =>
    intro e d e' hem he; simp [emitCore] at hem; cases hem; exact noFun_ret e d halt r he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [h1] at hem; cases hem
    exact noFun_ret e1 (d + 1) halt _ (noFun_letOp c e d op he h1)
  | stmtTail s =>
    intro e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noFun_ret _ d halt .unit (noFun_stmt c e d s he)
  | revertTail err args =>
    intro e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noFun_customError c e err _ he
  | letOp op k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [h1] at hem
    exact ih e1 (d + 1) hem (noFun_letOp c e d op he h1)
  | seq s k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    exact ih (emitStmt c e d s) d hem (noFun_stmt c e d s he)
  | letPure p args k ih =>
    intro e d e' hem he
    simp [emitCore] at hem
    exact ih _ (d + 1) hem (noFun_let he)
  | ite cond a b =>
    intro e d e' hem he
    simp [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some (c := c) (halt := halt) a ({} : Emit) d
    obtain ⟨eB, hB⟩ := emitCore_some (c := c) (halt := halt) b ({} : Emit) d
    simp [hA, hB] at hem; cases hem
    exact noFun_push he rfl

theorem hoist_emitCore {c halt t} {core : Core t} {e' d}
    (hem : emitCore c {} d halt core = some e') :
    hoist evm e'.stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_core core {} d hem noFun_nil))

theorem hoist_emitStmt (c : ContractDef) (d : Nat) (s : Lsc.Stmt) :
    hoist evm (emitStmt c {} d s).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_stmt c {} d s noFun_nil))

theorem hoist_panic (code : Nat) : hoist evm (emitPanic {} code).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_panic {} code noFun_nil))

theorem hoist_customError (c : ContractDef) (err : Nat) (args : List YExpr) :
    hoist evm (emitCustomError c {} err args).stmts = [] :=
  hoist_nil_of (Emit.noFun_stmts (noFun_customError c {} err args noFun_nil))

theorem emitParams_acc (e : Emit) (off n : Nat) :
    emitParams e off n = { acc := (emitParams {} off n).acc ++ e.acc } := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    dsimp only [emitParams]
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show (List.range n).foldl (fun e i =>
          e.push (.letDecl [identV i] (some (bop Op.calldataload [lit (off + 32 * i)])))) e =
        emitParams e off n from rfl]
    rw [ih]
    simp [Emit.push, emitParams]

end Lsc.Compiler
