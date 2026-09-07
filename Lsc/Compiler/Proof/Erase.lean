import Lsc.Compiler.Yul
import Lsc.Compiler.Proof.Emit
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
`toYulFn` never emits a Yul `.call` (externals are `.builtin Op.call`). Erasing
`memoryguard` is therefore identity on dispatcher tails and function bodies.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.MemorySpill

mutual
def noYulCallExpr : YExpr → Bool
  | .lit _ | .var _ => true
  | .builtin _ args => noYulCallExprs args
  | .call _ _ => false

def noYulCallExprs : List YExpr → Bool
  | [] => true
  | e :: es => noYulCallExpr e && noYulCallExprs es

def noYulCallStmt : YStmt → Bool
  | .block b | .funDef _ _ _ b => noYulCallStmts b
  | .letDecl _ none => true
  | .letDecl _ (some e) => noYulCallExpr e
  | .assign _ e | .exprStmt e => noYulCallExpr e
  | .cond c b => noYulCallExpr c && noYulCallStmts b
  | .switch c cases dflt =>
      noYulCallExpr c && noYulCallCases cases &&
        match dflt with
        | none => true
        | some b => noYulCallStmts b
  | .forLoop init c post body =>
      noYulCallStmts init && noYulCallExpr c && noYulCallStmts post && noYulCallStmts body
  | .break | .continue | .leave => true

def noYulCallStmts : YBlock → Bool
  | [] => true
  | s :: rest => noYulCallStmt s && noYulCallStmts rest

def noYulCallCases : List (Literal × YBlock) → Bool
  | [] => true
  | (_, b) :: rest => noYulCallStmts b && noYulCallCases rest
end

theorem noYulCallExpr_lit (n : Nat) : noYulCallExpr (lit n) = true := rfl
theorem noYulCallExpr_var (x : YIdent) : noYulCallExpr (var x) = true := rfl

theorem noYulCallExprs_cons (e : YExpr) (es : List YExpr) :
    noYulCallExprs (e :: es) = (noYulCallExpr e && noYulCallExprs es) := rfl

theorem noYulCall_bop (op : YOp) (args : List YExpr) :
    noYulCallExpr (bop op args) = noYulCallExprs args := rfl

theorem noYulCall_atom (d : Nat) (a : Atom) : noYulCallExpr (atomE d a) = true := by
  cases a with
  | var i =>
    simp only [atomE]
    split <;> simp [noYulCallExpr, var, lit]
  | lit n => simp [atomE, noYulCallExpr, lit]

theorem noYulCallExprs_nil : noYulCallExprs [] = true := rfl

theorem noYulCallExprs_of_all (args : List YExpr)
    (h : ∀ e ∈ args, noYulCallExpr e = true) : noYulCallExprs args = true := by
  induction args with
  | nil => rfl
  | cons e es ih =>
    rw [noYulCallExprs_cons, Bool.and_eq_true]
    exact ⟨h e (by simp), ih (fun e' he' => h e' (by simp [he']))⟩

theorem noYulCallExprs_map_atom (d : Nat) (as : List Atom) :
    noYulCallExprs (as.map (atomE d)) = true :=
  noYulCallExprs_of_all _ (fun e he => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact noYulCall_atom d a)

theorem noYulCall_revert00 : noYulCallStmt revert00 = true := by
  simp [revert00, noYulCallStmt, noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]

theorem noYulCall_stopStmt : noYulCallStmt stopStmt = true := by
  simp [stopStmt, noYulCallStmt, noYulCall_bop, noYulCallExprs]

theorem noYulCall_guardLt (n : Nat) :
    noYulCallStmts (emitGuardLt {} n).stmts = true := by
  simp [emitGuardLt, Emit.stmts, Emit.push, noYulCallStmts, noYulCallStmt,
    noYulCall_bop, noYulCallExprs, noYulCallExpr, lit, revert00]

mutual
theorem eraseMemoryGuardExpr_id (e : YExpr) (h : noYulCallExpr e = true) :
    eraseMemoryGuardExpr e = e := by
  cases e with
  | lit l => simp [eraseMemoryGuardExpr]
  | var x => simp [eraseMemoryGuardExpr]
  | builtin op args =>
    simp only [noYulCallExpr] at h
    simp [eraseMemoryGuardExpr, eraseMemoryGuardArgs_id args h]
  | call n args =>
    simp [noYulCallExpr] at h
termination_by sizeOf e

theorem eraseMemoryGuardArgs_id (args : List YExpr) (h : noYulCallExprs args = true) :
    eraseMemoryGuardArgs args = args := by
  cases args with
  | nil => simp [eraseMemoryGuardArgs]
  | cons e es =>
    simp only [noYulCallExprs, Bool.and_eq_true] at h
    simp [eraseMemoryGuardArgs, eraseMemoryGuardExpr_id e h.1, eraseMemoryGuardArgs_id es h.2]
termination_by sizeOf args
end

mutual
theorem eraseMemoryGuardStmt_id (s : YStmt) (h : noYulCallStmt s = true) :
    eraseMemoryGuardStmt s = s := by
  cases s with
  | block b =>
    simp only [noYulCallStmt] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardStmts_id b h]
  | funDef n ps rs b =>
    simp only [noYulCallStmt] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardStmts_id b h]
  | letDecl xs val =>
    cases val with
    | none => simp [eraseMemoryGuardStmt]
    | some e =>
      simp only [noYulCallStmt] at h
      simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id e h]
  | assign xs e =>
    simp only [noYulCallStmt] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id e h]
  | cond c b =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id c h.1, eraseMemoryGuardStmts_id b h.2]
  | «switch» c cases dflt =>
    cases dflt with
    | none =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id c h.1.1,
        eraseMemoryGuardCases_id cases h.1.2]
    | some b =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id c h.1.1,
        eraseMemoryGuardCases_id cases h.1.2, eraseMemoryGuardStmts_id b h.2]
  | «forLoop» init c post body =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardStmts_id init h.1.1.1,
      eraseMemoryGuardExpr_id c h.1.1.2, eraseMemoryGuardStmts_id post h.1.2,
      eraseMemoryGuardStmts_id body h.2]
  | «break» => simp [eraseMemoryGuardStmt]
  | «continue» => simp [eraseMemoryGuardStmt]
  | «leave» => simp [eraseMemoryGuardStmt]
  | exprStmt e =>
    simp only [noYulCallStmt] at h
    simp [eraseMemoryGuardStmt, eraseMemoryGuardExpr_id e h]
termination_by sizeOf s

theorem eraseMemoryGuardStmts_id (b : YBlock) (h : noYulCallStmts b = true) :
    eraseMemoryGuardStmts b = b := by
  cases b with
  | nil => simp [eraseMemoryGuardStmts]
  | cons s rest =>
    simp only [noYulCallStmts, Bool.and_eq_true] at h
    simp [eraseMemoryGuardStmts, eraseMemoryGuardStmt_id s h.1,
      eraseMemoryGuardStmts_id rest h.2]
termination_by sizeOf b

theorem eraseMemoryGuardCases_id (cases : List (Literal × YBlock))
    (h : noYulCallCases cases = true) :
    eraseMemoryGuardCases cases = cases := by
  cases cases with
  | nil => simp [eraseMemoryGuardCases]
  | cons p rest =>
    cases p with
    | mk l b =>
      simp only [noYulCallCases, Bool.and_eq_true] at h
      simp [eraseMemoryGuardCases, eraseMemoryGuardStmts_id b h.1,
        eraseMemoryGuardCases_id rest h.2]
termination_by sizeOf cases
end

theorem eraseMemoryGuardStmt_memoryGuard :
    eraseMemoryGuardStmt memoryGuardStmt = memoryGuardErased := by
  simp [memoryGuardStmt, memoryGuardErased, eraseMemoryGuardStmt, eraseMemoryGuardExpr,
    eraseMemoryGuardArgs, bop, lit]

theorem eraseMemoryGuardStmts_cons (s : YStmt) (rest : YBlock) :
    eraseMemoryGuardStmts (s :: rest) =
      eraseMemoryGuardStmt s :: eraseMemoryGuardStmts rest := by
  simp [eraseMemoryGuardStmts]

theorem noYulCall_emitCond (d : Nat) : ∀ c, noYulCallExpr (emitCond d c) = true
  | .lt a b | .le a b | .eq a b | .ne a b => by
    simp [emitCond, noYulCall_bop, noYulCallExprs, noYulCall_atom]
  | .and c d' => by
    simp [emitCond, noYulCall_bop, noYulCallExprs, noYulCall_emitCond d c,
      noYulCall_emitCond d d']
  | .or c d' => by
    simp [emitCond, noYulCall_bop, noYulCallExprs, noYulCall_emitCond d c,
      noYulCall_emitCond d d']
  | .not c => by
    simp [emitCond, noYulCall_bop, noYulCallExprs, noYulCall_emitCond d c]
  | .tt | .ff => by simp [emitCond, noYulCallExpr, lit]

theorem noYulCall_emitPrim (d : Nat) (p : Prim) (args : List Atom) :
    noYulCallExpr (emitPrim d p args) = true := by
  cases p <;> cases args with
  | nil => simp [emitPrim, noYulCallExpr, lit]
  | cons a rest =>
    cases rest with
    | nil =>
      simp [emitPrim, noYulCall_atom, noYulCallExpr, lit]
    | cons b rest2 =>
      cases rest2 with
      | nil => simp [emitPrim, noYulCall_bop, noYulCallExprs, noYulCall_atom, noYulCallExpr, lit]
      | cons _ _ => simp [emitPrim, noYulCallExpr, lit]

theorem noYulCallStmts_append (a b : YBlock) :
    noYulCallStmts (a ++ b) = (noYulCallStmts a && noYulCallStmts b) := by
  induction a with
  | nil => simp [noYulCallStmts]
  | cons s rest ih => simp [noYulCallStmts, ih, Bool.and_assoc]

theorem noYulCallStmts_reverse (b : YBlock) :
    noYulCallStmts b.reverse = noYulCallStmts b := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
    simp [List.reverse_cons, noYulCallStmts_append, noYulCallStmts, ih, Bool.and_comm]

theorem noYulCall_emit_push (e : Emit) (s : YStmt)
    (he : noYulCallStmts e.stmts = true) (hs : noYulCallStmt s = true) :
    noYulCallStmts (e.push s).stmts = true := by
  simp [Emit.stmts_push, noYulCallStmts_append, noYulCallStmts, he, hs]

theorem noYulCall_emitDo (e : Emit) (op : YOp) (args : List YExpr)
    (he : noYulCallStmts e.stmts = true) (ha : noYulCallExprs args = true) :
    noYulCallStmts (emitDo e op args).stmts = true := by
  exact noYulCall_emit_push e _ he (by simp [noYulCallStmt, noYulCallExpr, ha])

theorem noYulCall_emitLet (e : Emit) (n : YIdent) (x : YExpr)
    (he : noYulCallStmts e.stmts = true) (hx : noYulCallExpr x = true) :
    noYulCallStmts (emitLet e n x).stmts = true := by
  exact noYulCall_emit_push e _ he (by simp [noYulCallStmt, hx])

theorem noYulCall_emitAssign (e : Emit) (n : YIdent) (x : YExpr)
    (he : noYulCallStmts e.stmts = true) (hx : noYulCallExpr x = true) :
    noYulCallStmts (emitAssign e n x).stmts = true := by
  exact noYulCall_emit_push e _ he (by simp [noYulCallStmt, hx])

theorem noYulCall_emitIf (e : Emit) (cnd : YExpr) (body : YBlock)
    (he : noYulCallStmts e.stmts = true) (hc : noYulCallExpr cnd = true)
    (hb : noYulCallStmts body = true) :
    noYulCallStmts (emitIf e cnd body).stmts = true := by
  exact noYulCall_emit_push e _ he (by simp [noYulCallStmt, hc, hb])

theorem noYulCall_emitBlock (e : Emit) (body : YBlock)
    (he : noYulCallStmts e.stmts = true) (hb : noYulCallStmts body = true) :
    noYulCallStmts (e.push (.block body)).stmts = true := by
  exact noYulCall_emit_push e _ he (by simp [noYulCallStmt, hb])

theorem noYulCallExprs_two (a b : YExpr)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true) :
    noYulCallExprs [a, b] = true := by
  simp [noYulCallExprs, ha, hb]

theorem noYulCallExprs_one (a : YExpr) (ha : noYulCallExpr a = true) :
    noYulCallExprs [a] = true := by
  simp [noYulCallExprs, ha]

theorem noYulCall_nilEmit : noYulCallStmts ({} : Emit).stmts = true := rfl

theorem noYulCall_keccak064 : noYulCallExpr keccak064 = true := by
  simp [keccak064, noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]

theorem noYulCall_panicStmts (code : Nat) :
    noYulCallStmts (emitPanic {} code).stmts = true := by
  simp [emitPanic, emitDo, Emit.push, Emit.stmts, noYulCallStmts, noYulCallStmt,
    noYulCall_bop, noYulCallExprs, noYulCallExpr, lit, bop]

theorem noYulCall_foldl_mstore (base : Nat) (xs : List YExpr) (i0 : Nat) :
    ∀ (e : Emit), noYulCallStmts e.stmts = true → noYulCallExprs xs = true →
      noYulCallStmts (xs.foldl (fun p a =>
          (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1)) (e, i0)).1.stmts = true := by
  induction xs generalizing i0 with
  | nil =>
    intro e he _hx
    simpa [List.foldl] using he
  | cons x rest ih =>
    intro e he hx
    simp only [noYulCallExprs, Bool.and_eq_true] at hx
    simp only [List.foldl_cons]
    exact ih (i0 + 1) (emitDo e Op.mstore [lit (base + 32 * i0), x])
      (noYulCall_emitDo e _ _ he (by simp [noYulCallExprs, noYulCallExpr, lit, hx.1])) hx.2

theorem noYulCall_emitCustomError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr)
    (he : noYulCallStmts e.stmts = true) (ha : noYulCallExprs args = true) :
    noYulCallStmts (emitCustomError c e err args).stmts = true := by
  unfold emitCustomError
  set sel := match c.errors[err]? with | some ed => ed.selector | none => 0
  have h1 := noYulCall_emitDo e Op.mstore
    [lit abiPtr, bop Op.shl [lit 224, lit sel]] he
    (by simp [noYulCallExprs, noYulCallExpr, lit, noYulCall_bop])
  have h2 := noYulCall_foldl_mstore abiAfterSel args 0 _ h1 ha
  exact noYulCall_emitDo _ Op.revert [lit abiPtr, lit (4 + 32 * args.length)] h2
    (by simp [noYulCallExprs, noYulCallExpr, lit])

theorem noYulCall_emitReturnWords (e : Emit) (xs : List YExpr)
    (he : noYulCallStmts e.stmts = true) (hx : noYulCallExprs xs = true) :
    noYulCallStmts (emitReturnWords e xs).stmts = true := by
  cases xs with
  | nil =>
    simp [emitReturnWords]
    exact noYulCall_emit_push e stopStmt he noYulCall_stopStmt
  | cons x rest =>
    simp only [emitReturnWords]
    have h1 := noYulCall_foldl_mstore abiPtr (x :: rest) 0 e he hx
    exact noYulCall_emitDo _ Op.ret [lit abiPtr, lit (32 * (x :: rest).length)] h1
      (by simp [noYulCallExprs, noYulCallExpr, lit])

theorem noYulCall_emitReturnUnit (e : Emit) (halt : Bool)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitReturnUnit e halt).stmts = true := by
  cases halt with
  | true =>
    simp [emitReturnUnit]
    exact noYulCall_emit_push e stopStmt he noYulCall_stopStmt
  | false => simpa [emitReturnUnit] using he

theorem noYulCall_emitLog1 (e : Emit) (topic : Nat) (args : List YExpr)
    (he : noYulCallStmts e.stmts = true) (ha : noYulCallExprs args = true) :
    noYulCallStmts (emitLog1 e topic args).stmts = true := by
  unfold emitLog1
  have h1 := noYulCall_foldl_mstore abiPtr args 0 e he ha
  exact noYulCall_emitDo _ Op.log1 [lit abiPtr, lit (32 * args.length), lit topic] h1
    (by simp [noYulCallExprs, noYulCallExpr, lit])

theorem noYulCall_emitMapSlotPrep (e : Emit) (slot : Nat) (k : YExpr)
    (he : noYulCallStmts e.stmts = true) (hk : noYulCallExpr k = true) :
    noYulCallStmts (emitMapSlotPrep e slot k).stmts = true := by
  unfold emitMapSlotPrep
  have h1 := noYulCall_emitDo e Op.mstore [lit 0, k] he
    (by simp [noYulCallExprs, noYulCallExpr, lit, hk])
  exact noYulCall_emitDo _ Op.mstore [lit 32, lit slot] h1
    (by simp [noYulCallExprs, noYulCallExpr, lit])

theorem noYulCall_emitMap2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (h1 : noYulCallExpr k₁ = true) (h2 : noYulCallExpr k₂ = true) :
    noYulCallStmts (emitMap2SlotPrep e slot k₁ k₂).stmts = true := by
  unfold emitMap2SlotPrep
  have hp := noYulCall_emitMapSlotPrep e slot k₁ he h1
  have hm := noYulCall_emitDo (emitMapSlotPrep e slot k₁) Op.mstore [lit 32, keccak064] hp
    (by simp [noYulCallExprs, noYulCallExpr, lit, noYulCall_keccak064])
  exact noYulCall_emitDo _ Op.mstore [lit 0, k₂] hm
    (by simp [noYulCallExprs, noYulCallExpr, lit, h2])

theorem noYulCall_emitMulOverflowGuard (e : Emit) (a b p : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true)
    (hp : noYulCallExpr p = true) :
    noYulCallStmts (emitMulOverflowGuard e a b p).stmts = true := by
  unfold emitMulOverflowGuard
  exact noYulCall_emitIf e _ (emitPanic {} 0x11).stmts he
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, ha, hb, hp])
    (noYulCall_panicStmts _)

theorem noYulCall_emitAddChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true) :
    noYulCallStmts (emitAddChecked e name a b).stmts = true := by
  unfold emitAddChecked
  have hl := noYulCall_emitLet e name (bop Op.add [a, b]) he
    (by simp [noYulCall_bop, noYulCallExprs, ha, hb])
  exact noYulCall_emitIf _ _ (emitPanic {} 0x11).stmts hl
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, var, ha])
    (noYulCall_panicStmts _)

theorem noYulCall_emitSubChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true) :
    noYulCallStmts (emitSubChecked e name a b).stmts = true := by
  simpa [emitSubChecked] using
    noYulCall_emitLet (emitIf e (bop Op.lt [a, b]) (emitPanic {} 0x11).stmts) name
      (bop Op.sub [a, b])
      (noYulCall_emitIf e _ (emitPanic {} 0x11).stmts he
        (by simp [noYulCall_bop, noYulCallExprs, ha, hb]) (noYulCall_panicStmts _))
      (by simp [noYulCall_bop, noYulCallExprs, ha, hb])

theorem noYulCall_emitMulChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true) :
    noYulCallStmts (emitMulChecked e name a b).stmts = true := by
  unfold emitMulChecked
  have hl := noYulCall_emitLet e name (bop Op.mul [a, b]) he
    (by simp [noYulCall_bop, noYulCallExprs, ha, hb])
  exact noYulCall_emitMulOverflowGuard _ a b (var name) hl ha hb (by simp [noYulCallExpr, var])

theorem noYulCall_emitDivChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true) :
    noYulCallStmts (emitDivChecked e name a b).stmts = true := by
  simpa [emitDivChecked] using
    noYulCall_emitLet (emitIf e (bop Op.iszero [b]) (emitPanic {} 0x12).stmts) name
      (bop Op.div [a, b])
      (noYulCall_emitIf e _ (emitPanic {} 0x12).stmts he
        (by simp [noYulCall_bop, noYulCallExprs, hb]) (noYulCall_panicStmts _))
      (by simp [noYulCall_bop, noYulCallExprs, ha, hb])

theorem noYulCall_emitMulDivDown (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true)
    (hc : noYulCallExpr c = true) :
    noYulCallStmts (emitMulDivDown e name a b c).stmts = true := by
  simpa [emitMulDivDown] using
    (noYulCall_emit_push
      (emitMulOverflowGuard
        (emitLet (emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts) name
          (bop Op.mul [a, b]))
        a b (var name))
      (.assign [name] (bop Op.div [var name, c]))
      (noYulCall_emitMulOverflowGuard _
        a b (var name)
        (noYulCall_emitLet _ name (bop Op.mul [a, b])
          (noYulCall_emitIf e _ (emitPanic {} 0x12).stmts he
            (by simp [noYulCall_bop, noYulCallExprs, hc]) (noYulCall_panicStmts _))
          (by simp [noYulCall_bop, noYulCallExprs, ha, hb]))
        ha hb (by simp [noYulCallExpr, var]))
      (by simp [noYulCallStmt, noYulCall_bop, noYulCallExprs, noYulCallExpr, var, hc]))

theorem noYulCall_emitMulDivUp (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noYulCallStmts e.stmts = true)
    (ha : noYulCallExpr a = true) (hb : noYulCallExpr b = true)
    (hc : noYulCallExpr c = true) :
    noYulCallStmts (emitMulDivUp e name a b c).stmts = true := by
  simpa [emitMulDivUp] using
    (noYulCall_emit_push
      (emitMulOverflowGuard
        (emitLet (emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts) name
          (bop Op.mul [a, b]))
        a b (var name))
      (.switch (bop Op.mod [var name, c])
        [(Literal.number 0, [.assign [name] (bop Op.div [var name, c])])]
        (some [.assign [name]
          (bop Op.add [bop Op.div [var name, c], lit 1])]))
      (noYulCall_emitMulOverflowGuard _
        a b (var name)
        (noYulCall_emitLet _ name (bop Op.mul [a, b])
          (noYulCall_emitIf e _ (emitPanic {} 0x12).stmts he
            (by simp [noYulCall_bop, noYulCallExprs, hc]) (noYulCall_panicStmts _))
          (by simp [noYulCall_bop, noYulCallExprs, ha, hb]))
        ha hb (by simp [noYulCallExpr, var]))
      (by simp [noYulCallStmt, noYulCall_bop, noYulCallExprs, noYulCallExpr, var, lit, hc,
            noYulCallStmts, noYulCallCases]))

theorem noYulCall_emitCallRetCheck (e : Emit) (ret : AbiRet)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitCallRetCheck e ret).stmts = true := by
  cases ret with
  | boolOpt =>
    unfold emitCallRetCheck
    exact noYulCall_emitIf e _ [revert00] he
      (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]) noYulCall_revert00
  | word =>
    unfold emitCallRetCheck
    exact noYulCall_emitIf e _ [revert00] he
      (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]) noYulCall_revert00
  | none => simpa [emitCallRetCheck] using he

theorem noYulCall_foldl_mstore_atoms (depth base : Nat) (args : List Atom) (i0 : Nat) :
    ∀ (e : Emit), noYulCallStmts e.stmts = true →
      noYulCallStmts (args.foldl (fun p a =>
          (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE depth a], p.2 + 1))
        (e, i0)).1.stmts = true := by
  induction args generalizing i0 with
  | nil =>
    intro e he
    simpa [List.foldl] using he
  | cons a rest ih =>
    intro e he
    simp only [List.foldl_cons]
    exact ih (i0 + 1) (emitDo e Op.mstore [lit (base + 32 * i0), atomE depth a])
      (noYulCall_emitDo e _ _ he
        (by simp [noYulCallExprs, noYulCallExpr, lit, noYulCall_atom]))

theorem noYulCall_emitExtCallBody (c : ContractDef) (depth b m : Nat) (args : List Atom)
    (assign : Option YIdent) :
    noYulCallStmts (emitExtCallBody c depth b m args assign) = true := by
  have h0 : noYulCallStmts ({} : Emit).stmts = true := noYulCall_nilEmit
  have hlet := noYulCall_emitLet ({} : Emit) (extTok depth)
    (bop Op.sload [lit (bindingSlot c b)]) h0
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit])
  have hsel := noYulCall_emitDo _ Op.mstore
    [lit abiPtr, bop Op.shl [lit 224, lit (bindingMethod c b m).1]] hlet
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit])
  have hargs := noYulCall_foldl_mstore_atoms depth abiAfterSel args 0 _ hsel
  have hcall := noYulCall_emitLet _ (extOk depth)
    (bop YulSemantics.EVM.Op.call
      [lit extCallGas, var (extTok depth), lit 0, lit abiPtr,
        lit (4 + 32 * args.length), lit abiPtr, lit 32]) hargs
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit, var])
  have hif := noYulCall_emitIf _ (bop Op.iszero [var (extOk depth)]) [revert00] hcall
    (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, var]) noYulCall_revert00
  have hret := noYulCall_emitCallRetCheck _ (bindingMethod c b m).2 hif
  cases assign with
  | none =>
    convert hret using 1
    simp [emitExtCallBody]
  | some name =>
    cases hrv : (bindingMethod c b m).2 with
    | boolOpt | none =>
      convert (noYulCall_emitAssign _ name (lit 1) hret (by simp [noYulCallExpr, lit])) using 1
      simp [emitExtCallBody, hrv]
    | word =>
      convert (noYulCall_emitAssign _ name (bop Op.mload [lit abiPtr]) hret
        (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit])) using 1
      simp [emitExtCallBody, hrv]

theorem noYulCall_emitExtCall (c : ContractDef) (e : Emit) (depth b m : Nat)
    (args : List Atom) (bind : Option YIdent)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitExtCall c e depth b m args bind).stmts = true := by
  cases bind with
  | none =>
    simp [emitExtCall, emitBlock]
    exact noYulCall_emitBlock e _ he (noYulCall_emitExtCallBody c depth b m args none)
  | some name =>
    simp [emitExtCall, emitBlock]
    have hl := noYulCall_emitLet e name (lit 0) he (by simp [noYulCallExpr, lit])
    exact noYulCall_emitBlock _ _ hl (noYulCall_emitExtCallBody c depth b m args (some name))

theorem noYulCall_emitLetOp (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op)
    (he : noYulCallStmts e.stmts = true) {e'}
    (h : emitLetOp c e d op = some e') :
    noYulCallStmts e'.stmts = true := by
  cases op with
  | load f =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitLet e _ (bop Op.sload [lit f]) he
      (by simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit])
  | loadMap f k =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := noYulCall_emitMapSlotPrep e f (atomE d k) he (noYulCall_atom d k)
    exact noYulCall_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [noYulCall_bop, noYulCallExprs, noYulCall_keccak064])
  | loadMap2 f k₁ k₂ =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := noYulCall_emitMap2SlotPrep e f (atomE d k₁) (atomE d k₂) he
      (noYulCall_atom d k₁) (noYulCall_atom d k₂)
    exact noYulCall_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [noYulCall_bop, noYulCallExprs, noYulCall_keccak064])
  | sender | value | timestamp | blockNumber | selfAddress =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitLet e _ _ he (by simp [noYulCall_bop, noYulCallExprs])
  | addChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitAddChecked e _ (atomE d a) (atomE d b) he
      (noYulCall_atom d a) (noYulCall_atom d b)
  | subChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitSubChecked e _ (atomE d a) (atomE d b) he
      (noYulCall_atom d a) (noYulCall_atom d b)
  | mulChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitMulChecked e _ (atomE d a) (atomE d b) he
      (noYulCall_atom d a) (noYulCall_atom d b)
  | divChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitDivChecked e _ (atomE d a) (atomE d b) he
      (noYulCall_atom d a) (noYulCall_atom d b)
  | mulDivDown a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitMulDivDown e _ (atomE d a) (atomE d b) (atomE d c) he
      (noYulCall_atom d a) (noYulCall_atom d b) (noYulCall_atom d c)
  | mulDivUp a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitMulDivUp e _ (atomE d a) (atomE d b) (atomE d c) he
      (noYulCall_atom d a) (noYulCall_atom d b) (noYulCall_atom d c)
  | pure a =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitLet e _ (atomE d a) he (noYulCall_atom d a)
  | call b m args =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noYulCall_emitExtCall c e d b m args (some (identV d)) he

theorem noYulCall_emitStmt (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitStmt c e d s).stmts = true := by
  cases s with
  | store f v =>
    simp only [emitStmt]
    exact noYulCall_emitDo e Op.sstore [lit f, atomE d v] he
      (by simp [noYulCallExprs, noYulCallExpr, lit, noYulCall_atom])
  | storeMap f k v =>
    simp only [emitStmt]
    have hp := noYulCall_emitMapSlotPrep e f (atomE d k) he (noYulCall_atom d k)
    exact noYulCall_emitDo _ Op.sstore [keccak064, atomE d v] hp
      (by simp [noYulCallExprs, noYulCall_keccak064, noYulCall_atom])
  | storeMap2 f k₁ k₂ v =>
    simp only [emitStmt]
    have hp := noYulCall_emitMap2SlotPrep e f (atomE d k₁) (atomE d k₂) he
      (noYulCall_atom d k₁) (noYulCall_atom d k₂)
    exact noYulCall_emitDo _ Op.sstore [keccak064, atomE d v] hp
      (by simp [noYulCallExprs, noYulCall_keccak064, noYulCall_atom])
  | require cond err args =>
    simp only [emitStmt]
    exact noYulCall_emitIf e _ (emitCustomError c {} err (args.map (atomE d))).stmts he
      (by simp [noYulCall_bop, noYulCallExprs, noYulCall_emitCond d cond])
      (noYulCall_emitCustomError c {} err _ noYulCall_nilEmit (noYulCallExprs_map_atom d args))
  | emit ev args =>
    simp only [emitStmt]
    exact noYulCall_emitLog1 e _ (args.map (atomE d)) he (noYulCallExprs_map_atom d args)
  | revert err args =>
    simp only [emitStmt]
    exact noYulCall_emitCustomError c e err (args.map (atomE d)) he
      (noYulCallExprs_map_atom d args)
  | call b m args =>
    simp only [emitStmt]
    exact noYulCall_emitExtCall c e d b m args none he

theorem noYulCall_emitRet (e : Emit) (d : Nat) (halt : Bool) {t} (r : RetExpr t)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitRet e d halt r).stmts = true := by
  cases r with
  | unit =>
    simp only [emitRet]
    exact noYulCall_emitReturnUnit e halt he
  | word a | addr a | flag a =>
    simp only [emitRet, retAtoms, List.map_cons, List.map_nil]
    exact noYulCall_emitReturnWords e [atomE d a] he
      (by simp [noYulCallExprs, noYulCall_atom])
  | pair x y =>
    simp only [emitRet]
    exact noYulCall_emitReturnWords e ((retAtoms x ++ retAtoms y).map (atomE d)) he
      (noYulCallExprs_map_atom d _)

theorem noYulCall_emitParams (e : Emit) (offset n : Nat)
    (he : noYulCallStmts e.stmts = true) :
    noYulCallStmts (emitParams e offset n).stmts = true := by
  induction n generalizing e with
  | zero => simpa [emitParams_zero] using he
  | succ n ih =>
    rw [emitParams_succ, Emit.stmts_push]
    simp [noYulCallStmts_append, noYulCallStmts, ih e he, noYulCallStmt,
      noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]

theorem noYulCall_emitCore (c : ContractDef) (halt : Bool) {t} (core : Core t) :
    ∀ (e : Emit) (d : Nat), noYulCallStmts e.stmts = true →
      ∀ e', emitCore c e d halt core = some e' → noYulCallStmts e'.stmts = true := by
  induction core with
  | ret r =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noYulCall_emitRet e d halt r he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    cases hop : emitLetOp c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      have he1 := noYulCall_emitLetOp c e d op he hop
      cases h
      exact noYulCall_emitRet e1 (d + 1) halt _ he1
  | stmtTail s =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noYulCall_emitReturnUnit (emitStmt c e d s) halt (noYulCall_emitStmt c e d s he)
  | revertTail err args =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noYulCall_emitCustomError c e err (args.map (atomE d)) he
      (noYulCallExprs_map_atom d args)
  | letOp op k ih =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind] at h
    cases hop : emitLetOp c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      exact ih e1 (d + 1) (noYulCall_emitLetOp c e d op he hop) e' h
  | seq s k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    exact ih (emitStmt c e d s) d (noYulCall_emitStmt c e d s he) e' h
  | letPure p args k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    exact ih (emitLet e (identV d) (emitPrim d p args)) (d + 1)
      (noYulCall_emitLet e _ _ he (noYulCall_emitPrim d p args)) e' h
  | ite cond a b iha ihb =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    cases ha : emitCore c {} d halt a with
    | none => simp [ha] at h
    | some eA =>
      simp [ha] at h
      cases hb : emitCore c {} d halt b with
      | none => simp [hb] at h
      | some eB =>
        simp [hb] at h
        cases h
        have hA := iha {} d noYulCall_nilEmit _ ha
        have hB := ihb {} d noYulCall_nilEmit _ hb
        exact noYulCall_emit_push e _ he (by
          simp [noYulCallStmt, noYulCall_emitCond d cond, noYulCallCases, noYulCallStmts, hA, hB])

theorem toYulFn_noYulCall {c f yul} (h : toYulFn c f = some yul) :
    noYulCallStmts yul = true := by
  unfold toYulFn at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, hem, rfl⟩ := h
  have hp := noYulCall_emitParams {} (if f.kind = .constructor then 0 else 4) f.params.length
    noYulCall_nilEmit
  exact noYulCall_emitCore c (f.kind ≠ .constructor) f.core _ f.params.length hp _ hem

theorem entryCase_noYulCall {c f p} (h : entryCase c f = some p) :
    noYulCallStmts p.2 = true := by
  simp [entryCase, Bind.bind, Option.bind] at h
  cases hb : toYulFn c f <;> simp [hb] at h
  cases h
  simp [noYulCallStmts, noYulCallStmt, noYulCall_guardLt, toYulFn_noYulCall hb]

theorem mapM_entryCase_noYulCall {c : ContractDef} :
    ∀ {fs : List FnDef} {cases : List (Literal × YBlock)},
      fs.mapM (entryCase c) = some cases → noYulCallCases cases = true
  | [], cases, h => by
    simp [List.mapM_nil] at h
    cases h
    rfl
  | f :: rest, cases, h => by
    simp [List.mapM_cons] at h
    cases hf : entryCase c f with
    | none => simp [hf] at h
    | some p =>
      simp [hf] at h
      cases hr : rest.mapM (entryCase c) with
      | none => simp [hr] at h
      | some cs =>
        simp [hr] at h
        cases h
        simp [noYulCallCases, entryCase_noYulCall hf, mapM_entryCase_noYulCall hr]

theorem noYulCall_selector :
    noYulCallExpr (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) = true := by
  simp [noYulCall_bop, noYulCallExprs, noYulCallExpr, lit]

theorem noYulCall_dispatchTail (guard : YBlock) (sel : YExpr)
    (cases : List (Literal × YBlock))
    (hg : noYulCallStmts guard = true) (hs : noYulCallExpr sel = true)
    (hc : noYulCallCases cases = true) :
    noYulCallStmts
      [YulSemantics.Stmt.block guard,
        YulSemantics.Stmt.switch sel cases (some [revert00])] = true := by
  simp [noYulCallStmts, noYulCallStmt, hg, hs, hc, noYulCall_revert00]

theorem erase_runtimeBlock {c yul} (h : runtimeBlock c = some yul) :
    ∃ cases, c.functions.mapM (entryCase c) = some cases ∧
      eraseMemoryGuardStmts yul =
        memoryGuardErased ::
          [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
            YulSemantics.Stmt.switch
              (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
              cases (some [revert00])] := by
  unfold runtimeBlock at h
  cases hsel : selectorsNodup c
  · simp [hsel] at h
  · simp [hsel] at h
    cases hmap : c.functions.mapM (entryCase c) with
    | none => simp [hmap, Option.bind] at h
    | some cs =>
      simp [hmap, Option.bind] at h
      subst yul
      refine ⟨cs, rfl, ?_⟩
      rw [eraseMemoryGuardStmts_cons, eraseMemoryGuardStmt_memoryGuard]
      have htail := noYulCall_dispatchTail (emitGuardLt {} 4).stmts _ cs
        (noYulCall_guardLt 4) noYulCall_selector (mapM_entryCase_noYulCall hmap)
      rw [eraseMemoryGuardStmts_id _ htail]

end Lsc.Compiler
