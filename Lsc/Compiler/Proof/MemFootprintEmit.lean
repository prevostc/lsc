import Lsc.Compiler.Proof.MemFootprint
import Lsc.Compiler.Proof.Emit
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`staticSafeStmts memoryGuardK` of every Core→Yul emitter form. Arity bounds
come from `fitsGuardCall` / `fitsGuardWords` in `coreWF`.
-/

namespace Lsc.Compiler

variable (tag : String)

open Lsc hiding Op Stmt
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill

theorem staticSafe_emitDo (e : Emit) (op : YOp) (args : List YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hop : staticSafeOp memoryGuardK op args = true)
    (ha : staticSafeExprs memoryGuardK args = true) :
    staticSafeStmts memoryGuardK (emitDo e op args).stmts = true :=
  staticSafe_emit_push _ e _ he (by
    simp [staticSafeStmt, staticSafeExpr, hop, ha])

theorem staticSafe_emitLet (e : Emit) (n : YIdent) (x : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hx : staticSafeExpr memoryGuardK x = true) :
    staticSafeStmts memoryGuardK (emitLet e n x).stmts = true :=
  staticSafe_emit_push _ e _ he (by simp [staticSafeStmt, hx])

theorem staticSafe_emitAssign (e : Emit) (n : YIdent) (x : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hx : staticSafeExpr memoryGuardK x = true) :
    staticSafeStmts memoryGuardK (emitAssign e n x).stmts = true :=
  staticSafe_emit_push _ e _ he (by simp [staticSafeStmt, hx])

theorem staticSafe_emitIf (e : Emit) (cnd : YExpr) (body : YBlock)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hc : staticSafeExpr memoryGuardK cnd = true)
    (hb : staticSafeStmts memoryGuardK body = true) :
    staticSafeStmts memoryGuardK (emitIf e cnd body).stmts = true :=
  staticSafe_emit_push _ e _ he (by simp [staticSafeStmt, hc, hb])

theorem staticSafe_emitBlock (e : Emit) (body : YBlock)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hb : staticSafeStmts memoryGuardK body = true) :
    staticSafeStmts memoryGuardK (e.push (.block body)).stmts = true :=
  staticSafe_emit_push _ e _ he (by simp [staticSafeStmt, hb])

theorem staticSafe_mstoreOp (p : Nat) (val : YExpr)
    (hp : p + 32 ≤ memoryGuardK)
    (hv : staticSafeExpr memoryGuardK val = true) :
    staticSafeOp memoryGuardK Op.mstore [lit p, val] = true ∧
      staticSafeExprs memoryGuardK [lit p, val] = true := by
  simp [staticSafeOp, staticSafeExprs, staticSafeExpr, litNat?, rangeBelow, lit, hp,
    decide_eq_true_eq, hv]

theorem staticSafe_emitDo_mstore (e : Emit) (p : Nat) (val : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hp : p + 32 ≤ memoryGuardK)
    (hv : staticSafeExpr memoryGuardK val = true) :
    staticSafeStmts memoryGuardK (emitDo e Op.mstore [lit p, val]).stmts = true := by
  obtain ⟨hop, ha⟩ := staticSafe_mstoreOp p val hp hv
  exact staticSafe_emitDo e _ _ he hop ha

theorem staticSafe_foldl_mstore (ptr : Nat) (xs : List YExpr) (i0 : Nat)
    (hxs : staticSafeExprs memoryGuardK xs = true)
    (hend : ptr + 32 * (i0 + xs.length) ≤ memoryGuardK) :
    ∀ (e : Emit), staticSafeStmts memoryGuardK e.stmts = true →
      staticSafeStmts memoryGuardK
        (xs.foldl (fun p a =>
            (emitDo p.1 Op.mstore [lit (ptr + 32 * p.2), a], p.2 + 1))
          (e, i0)).1.stmts = true := by
  induction xs generalizing i0 with
  | nil =>
    intro e he
    simpa [List.foldl] using he
  | cons x rest ih =>
    intro e he
    simp only [staticSafeExprs_cons, Bool.and_eq_true] at hxs
    simp only [List.foldl_cons]
    have hptr : ptr + 32 * i0 + 32 ≤ memoryGuardK := by
      simp [List.length_cons] at hend
      omega
    exact ih (i0 + 1) hxs.2 (by simp [List.length_cons] at hend; omega)
      (emitDo e Op.mstore [lit (ptr + 32 * i0), x])
      (staticSafe_emitDo_mstore e (ptr + 32 * i0) x he hptr hxs.1)

theorem staticSafe_emitCond (d : Nat) : ∀ c, staticSafeExpr memoryGuardK (emitCond tag d c) = true
  | .lt a b | .le a b | .eq a b | .ne a b => by
    simp [emitCond, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, staticSafe_atomE]
  | .and c d' => by
    simp [emitCond, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
      staticSafe_emitCond d c, staticSafe_emitCond d d']
  | .or c d' => by
    simp [emitCond, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
      staticSafe_emitCond d c, staticSafe_emitCond d d']
  | .not c => by
    simp [emitCond, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
      staticSafe_emitCond d c]
  | .tt | .ff => by simp [emitCond, staticSafeExpr_lit]

theorem staticSafe_emitPrim (d : Nat) (p : Prim) (args : List Atom) :
    staticSafeExpr memoryGuardK (emitPrim tag d p args) = true := by
  cases p <;> cases args with
  | nil => simp [emitPrim, staticSafeExpr_lit]
  | cons a rest =>
    cases rest with
    | nil => simp [emitPrim, staticSafe_atomE, staticSafeExpr_lit]
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        simp [emitPrim, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
          staticSafe_atomE, staticSafeExpr_lit]
      | cons _ _ => simp [emitPrim, staticSafeExpr_lit]

theorem staticSafe_panicStmts (code : Nat) :
    staticSafeStmts memoryGuardK (emitPanic {} code).stmts = true := by
  have h0 := staticSafe_nilEmit memoryGuardK
  have h1 := staticSafe_emitDo_mstore ({} : Emit) abiPtr
    (bop Op.shl [lit 224, lit panicSelector]) h0
    (by simp [abiPtr, memoryGuardK])
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
  have h2 := staticSafe_emitDo_mstore _ abiAfterSel (lit code) h1
    (by simp [abiAfterSel, memoryGuardK]) (staticSafeExpr_lit _ _)
  exact staticSafe_emitDo _ Op.revert [lit abiPtr, lit 36] h2
    (by simp [staticSafeOp, litNat?, rangeBelow, lit, abiPtr, memoryGuardK])
    (by simp [staticSafeExprs, staticSafeExpr, lit])

theorem staticSafe_emitCustomError (c : ContractDef) (e : Emit) (err : Nat)
    (args : List YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExprs memoryGuardK args = true)
    (hn : args.length ≤ 3) :
    staticSafeStmts memoryGuardK (emitCustomError c e err args).stmts = true := by
  unfold emitCustomError
  set sel := match c.errors[err]? with | some ed => ed.selector | none => 0
  have h1 := staticSafe_emitDo_mstore e abiPtr
    (bop Op.shl [lit 224, lit sel]) he
    (by simp [abiPtr, memoryGuardK])
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
  have h2 := staticSafe_foldl_mstore abiAfterSel args 0 ha
    (by simpa using abiAfterSel_le hn) _ h1
  exact staticSafe_emitDo _ Op.revert [lit abiPtr, lit (4 + 32 * args.length)] h2
    (by
      simp [staticSafeOp, litNat?, rangeBelow, lit, rangeBelow_iff]
      exact abiCall_le hn)
    (by simp [staticSafeExprs, staticSafeExpr, lit])

theorem staticSafe_emitReturnWords (e : Emit) (xs : List YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hx : staticSafeExprs memoryGuardK xs = true)
    (hn : xs.length ≤ 4) :
    staticSafeStmts memoryGuardK (emitReturnWords e xs).stmts = true := by
  cases xs with
  | nil =>
    simp [emitReturnWords]
    exact staticSafe_emit_push _ e stopStmt he (staticSafe_stopStmt _)
  | cons x rest =>
    simp only [emitReturnWords]
    have h1 := staticSafe_foldl_mstore abiPtr (x :: rest) 0 hx
      (by simpa using abiWords_le hn) e he
    exact staticSafe_emitDo _ Op.ret [lit abiPtr, lit (32 * (x :: rest).length)] h1
      (by
        simp [staticSafeOp, litNat?, rangeBelow, lit, rangeBelow_iff]
        exact abiWords_le hn)
      (by simp [staticSafeExprs, staticSafeExpr, lit])

theorem staticSafe_emitReturnUnit (e : Emit) (halt : Bool)
    (he : staticSafeStmts memoryGuardK e.stmts = true) :
    staticSafeStmts memoryGuardK (emitReturnUnit e halt).stmts = true := by
  cases halt with
  | true =>
    simp [emitReturnUnit]
    exact staticSafe_emit_push _ e stopStmt he (staticSafe_stopStmt _)
  | false => simpa [emitReturnUnit] using he

theorem staticSafe_emitLog1 (e : Emit) (topic : Nat) (args : List YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExprs memoryGuardK args = true)
    (hn : args.length ≤ 4) :
    staticSafeStmts memoryGuardK (emitLog1 e topic args).stmts = true := by
  unfold emitLog1
  have h1 := staticSafe_foldl_mstore abiPtr args 0 ha
    (by simpa using abiWords_le hn) e he
  exact staticSafe_emitDo _ Op.log1 [lit abiPtr, lit (32 * args.length), lit topic] h1
    (by
      simp [staticSafeOp, litNat?, rangeBelow, lit, rangeBelow_iff]
      exact abiWords_le hn)
    (by simp [staticSafeExprs, staticSafeExpr, lit])

theorem staticSafe_emitMapSlotPrep (e : Emit) (slot : Nat) (k : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hk : staticSafeExpr memoryGuardK k = true) :
    staticSafeStmts memoryGuardK (emitMapSlotPrep e slot k).stmts = true := by
  unfold emitMapSlotPrep
  have h0 := staticSafe_emitDo_mstore e 0 k he (by simp [memoryGuardK]) hk
  exact staticSafe_emitDo_mstore _ 32 (lit slot) h0 (by simp [memoryGuardK])
    (staticSafeExpr_lit _ _)

theorem staticSafe_emitMap2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (h1 : staticSafeExpr memoryGuardK k₁ = true)
    (h2 : staticSafeExpr memoryGuardK k₂ = true) :
    staticSafeStmts memoryGuardK (emitMap2SlotPrep e slot k₁ k₂).stmts = true := by
  unfold emitMap2SlotPrep
  have hp := staticSafe_emitMapSlotPrep e slot k₁ he h1
  have hk := staticSafe_keccak064 memoryGuardK (by simp [memoryGuardK])
  have h32 := staticSafe_emitDo_mstore _ 32 keccak064 hp (by simp [memoryGuardK]) hk
  exact staticSafe_emitDo_mstore _ 0 k₂ h32 (by simp [memoryGuardK]) h2

theorem staticSafe_emitMulOverflowGuard (e : Emit) (a b p : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true)
    (hp : staticSafeExpr memoryGuardK p = true) :
    staticSafeStmts memoryGuardK (emitMulOverflowGuard e a b p).stmts = true := by
  unfold emitMulOverflowGuard
  exact staticSafe_emitIf e _ (emitPanic {} 0x11).stmts he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb, hp])
    (staticSafe_panicStmts _)

theorem staticSafe_emitAddChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true) :
    staticSafeStmts memoryGuardK (emitAddChecked e name a b).stmts = true := by
  unfold emitAddChecked
  have hl := staticSafe_emitLet e name (bop Op.add [a, b]) he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])
  exact staticSafe_emitIf _ (bop Op.lt [var name, a]) (emitPanic {} 0x11).stmts hl
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, staticSafeExpr_var, ha])
    (staticSafe_panicStmts _)

theorem staticSafe_emitSubChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true) :
    staticSafeStmts memoryGuardK (emitSubChecked e name a b).stmts = true := by
  unfold emitSubChecked
  have hi := staticSafe_emitIf e (bop Op.lt [a, b]) (emitPanic {} 0x11).stmts he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])
    (staticSafe_panicStmts _)
  exact staticSafe_emitLet _ name (bop Op.sub [a, b]) hi
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])

theorem staticSafe_emitMulChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true) :
    staticSafeStmts memoryGuardK (emitMulChecked e name a b).stmts = true := by
  unfold emitMulChecked
  have hl := staticSafe_emitLet e name (bop Op.mul [a, b]) he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])
  exact staticSafe_emitMulOverflowGuard _ a b (var name) hl ha hb
    (staticSafeExpr_var _ _)

theorem staticSafe_emitDivChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true) :
    staticSafeStmts memoryGuardK (emitDivChecked e name a b).stmts = true := by
  unfold emitDivChecked
  have hi := staticSafe_emitIf e (bop Op.iszero [b]) (emitPanic {} 0x12).stmts he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, hb])
    (staticSafe_panicStmts _)
  exact staticSafe_emitLet _ name (bop Op.div [a, b]) hi
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])

theorem staticSafe_emitMulDivDown (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true)
    (hc : staticSafeExpr memoryGuardK c = true) :
    staticSafeStmts memoryGuardK (emitMulDivDown e name a b c).stmts = true := by
  unfold emitMulDivDown
  have hi := staticSafe_emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, hc])
    (staticSafe_panicStmts _)
  have hl := staticSafe_emitLet _ name (bop Op.mul [a, b]) hi
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])
  have hg := staticSafe_emitMulOverflowGuard _ a b (var name) hl ha hb (staticSafeExpr_var _ _)
  exact staticSafe_emit_push _ _ _ hg (by
    simp [staticSafeStmt_assign, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
      staticSafeExpr_var, hc])

theorem staticSafe_emitMulDivUp (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (ha : staticSafeExpr memoryGuardK a = true)
    (hb : staticSafeExpr memoryGuardK b = true)
    (hc : staticSafeExpr memoryGuardK c = true) :
    staticSafeStmts memoryGuardK (emitMulDivUp e name a b c).stmts = true := by
  unfold emitMulDivUp
  have hi := staticSafe_emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts he
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, hc])
    (staticSafe_panicStmts _)
  have hl := staticSafe_emitLet _ name (bop Op.mul [a, b]) hi
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, ha, hb])
  have hg := staticSafe_emitMulOverflowGuard _ a b (var name) hl ha hb (staticSafeExpr_var _ _)
  exact staticSafe_emit_push _ _ _ hg (by
    simp [staticSafeStmt_switch, bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
      staticSafeCases, staticSafeStmts, staticSafeExpr_var, staticSafeExpr_lit, hc])

theorem staticSafe_emitCallRetCheck (e : Emit) (ret : AbiRet)
    (he : staticSafeStmts memoryGuardK e.stmts = true) :
    staticSafeStmts memoryGuardK (emitCallRetCheck e ret).stmts = true := by
  cases ret with
  | boolOpt =>
    unfold emitCallRetCheck
    exact staticSafe_emitIf e _ [revert00] he
      (by
        simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, litNat?, rangeBelow,
          rangeBelow_iff, lit, abiPtr, memoryGuardK])
      (by simp [staticSafeStmts, staticSafe_revert00])
  | word =>
    unfold emitCallRetCheck
    exact staticSafe_emitIf e _ [revert00] he
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
      (by simp [staticSafeStmts, staticSafe_revert00])
  | none => simpa [emitCallRetCheck] using he

theorem staticSafe_callOp (n : Nat) (tok : YIdent) (hn : n ≤ 3) :
    staticSafeOp memoryGuardK YulSemantics.EVM.Op.call
      [lit extCallGas, var tok, lit 0, lit abiPtr, lit (4 + 32 * n),
        lit abiPtr, lit 32] = true := by
  simp [staticSafeOp, litNat?, rangeBelow, lit, rangeBelow_iff]
  exact ⟨abiCall_le hn, by unfold abiPtr memoryGuardK; omega⟩

theorem foldl_mstore_map (depth ptr i0 : Nat) (args : List Atom) (e : Emit) :
    ((args.map (atomE tag depth)).foldl
        (fun p a => (emitDo p.1 Op.mstore [lit (ptr + 32 * p.2), a], p.2 + 1)) (e, i0)) =
      (args.foldl
        (fun p a => (emitDo p.1 Op.mstore [lit (ptr + 32 * p.2), atomE tag depth a], p.2 + 1))
        (e, i0)) := by
  induction args generalizing e i0 with
  | nil => rfl
  | cons a rest ih => simp [List.map, List.foldl, ih]

theorem staticSafe_foldl_mstore_atoms (depth ptr : Nat) (args : List Atom) (i0 : Nat)
    (hend : ptr + 32 * (i0 + args.length) ≤ memoryGuardK) :
    ∀ (e : Emit), staticSafeStmts memoryGuardK e.stmts = true →
      staticSafeStmts memoryGuardK
        (args.foldl (fun p a =>
            (emitDo p.1 Op.mstore [lit (ptr + 32 * p.2), atomE tag depth a], p.2 + 1))
          (e, i0)).1.stmts = true := by
  have hxs := staticSafeExprs_map_atom memoryGuardK tag depth args
  intro e he
  have h := staticSafe_foldl_mstore ptr (args.map (atomE tag depth)) i0 hxs
    (by simpa [List.length_map] using hend) e he
  simpa [foldl_mstore_map] using h

theorem staticSafe_emitExtCallBody (c : ContractDef) (depth b m : Nat) (args : List Atom)
    (assign : Option YIdent) (hn : args.length ≤ 3) :
    staticSafeStmts memoryGuardK (emitExtCallBody tag c depth b m args assign) = true := by
  have h0 := staticSafe_nilEmit memoryGuardK
  have hlet := staticSafe_emitLet ({} : Emit) (extTok tag depth)
    (bop Op.sload [lit (bindingSlot c b)]) h0
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
  have hsel := staticSafe_emitDo_mstore _ abiPtr
    (bop Op.shl [lit 224, lit (bindingMethod c b m).1]) hlet
    (by simp [abiPtr, memoryGuardK])
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
  have hargs := staticSafe_foldl_mstore_atoms tag depth abiAfterSel args 0
    (by simpa using abiAfterSel_le hn) _ hsel
  have hcall := staticSafe_emitLet _ (extOk tag depth)
    (bop YulSemantics.EVM.Op.call
      [lit extCallGas, var (extTok tag depth), lit 0, lit abiPtr,
        lit (4 + 32 * args.length), lit abiPtr, lit 32]) hargs
    (by
      simp [bop, staticSafeExpr_builtin, staticSafeExprs]
      exact staticSafe_callOp args.length (extTok tag depth) hn)
  have hif := staticSafe_emitIf _ (bop Op.iszero [var (extOk tag depth)]) [revert00] hcall
    (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, staticSafeExpr_var])
    (by simp [staticSafeStmts, staticSafe_revert00])
  have hret := staticSafe_emitCallRetCheck _ (bindingMethod c b m).2 hif
  cases assign with
  | none =>
    convert hret using 1
    simp [emitExtCallBody]
  | some name =>
    cases hrv : (bindingMethod c b m).2 with
    | boolOpt | none =>
      convert (staticSafe_emitAssign _ name (lit 1) hret (staticSafeExpr_lit _ _)) using 1
      simp [emitExtCallBody, hrv]
    | word =>
      convert (staticSafe_emitAssign _ name (bop Op.mload [lit abiPtr]) hret
        (by
          simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, litNat?,
            rangeBelow, rangeBelow_iff, lit, abiPtr, memoryGuardK])) using 1
      simp [emitExtCallBody, hrv]

theorem staticSafe_emitExtCall (c : ContractDef) (e : Emit) (depth b m : Nat)
    (args : List Atom) (bind : Option YIdent)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hn : args.length ≤ 3) :
    staticSafeStmts memoryGuardK (emitExtCall tag c e depth b m args bind).stmts = true := by
  cases bind with
  | none =>
    simp [emitExtCall, emitBlock]
    exact staticSafe_emitBlock e _ he
      (staticSafe_emitExtCallBody tag c depth b m args none hn)
  | some name =>
    simp [emitExtCall, emitBlock]
    have hl := staticSafe_emitLet e name (lit 0) he (staticSafeExpr_lit _ _)
    exact staticSafe_emitBlock _ _ hl
      (staticSafe_emitExtCallBody tag c depth b m args (some name) hn)

theorem callWF_fits (c : ContractDef) (b m : Nat) (args : List Atom)
    (h : callWF c b m args = true) : args.length ≤ 3 := by
  unfold callWF at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp [Bool.and_eq_true, fitsGuardCall_iff] at h
      exact h.2

theorem eventOK_fits {c ev n} (h : eventOK c ev n = true) : n ≤ 4 := by
  obtain ⟨_, hrest⟩ := (eventOK_iff c ev n).mp h
  exact hrest.2.2

theorem errorOK_fits {c err n} (h : errorOK c err n = true) : n ≤ 3 := by
  obtain ⟨_, hrest⟩ := (errorOK_iff c err n).mp h
  exact hrest.2.2

theorem staticSafe_emitLetOp (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hwf : opWF c op = true) {e'}
    (h : emitLetOp tag c e d op = some e') :
    staticSafeStmts memoryGuardK e'.stmts = true := by
  cases op with
  | load f =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitLet e _ (bop Op.sload [lit f]) he
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit])
  | loadMap f k =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := staticSafe_emitMapSlotPrep e f (atomE tag d k) he (staticSafe_atomE _ _ _ _)
    exact staticSafe_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
        staticSafe_keccak064 memoryGuardK (by simp [memoryGuardK])])
  | loadMap2 f k₁ k₂ =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := staticSafe_emitMap2SlotPrep e f (atomE tag d k₁) (atomE tag d k₂) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
    exact staticSafe_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs,
        staticSafe_keccak064 memoryGuardK (by simp [memoryGuardK])])
  | sender | value | timestamp | blockNumber | selfAddress =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitLet e _ _ he
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs])
  | addChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitAddChecked e _ (atomE tag d a) (atomE tag d b) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | subChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitSubChecked e _ (atomE tag d a) (atomE tag d b) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | mulChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitMulChecked e _ (atomE tag d a) (atomE tag d b) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | divChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitDivChecked e _ (atomE tag d a) (atomE tag d b) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | mulDivDown a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitMulDivDown e _ (atomE tag d a) (atomE tag d b) (atomE tag d c) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | mulDivUp a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitMulDivUp e _ (atomE tag d a) (atomE tag d b) (atomE tag d c) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
  | pure a =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact staticSafe_emitLet e _ (atomE tag d a) he (staticSafe_atomE _ _ _ _)
  | call b m args =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    simp only [opWF] at hwf
    exact staticSafe_emitExtCall tag c e d b m args (some (identV tag d)) he
      (callWF_fits c b m args hwf)

theorem staticSafe_emitStmt (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hwf : stmtWF c s = true) :
    staticSafeStmts memoryGuardK (emitStmt tag c e d s).stmts = true := by
  cases s with
  | store f v =>
    simp only [emitStmt]
    exact staticSafe_emitDo e Op.sstore [lit f, atomE tag d v] he
      (by simp [staticSafeOp])
      (by simp [staticSafeExprs, staticSafeExpr, lit, staticSafe_atomE])
  | storeMap f k v =>
    simp only [emitStmt]
    have hp := staticSafe_emitMapSlotPrep e f (atomE tag d k) he (staticSafe_atomE _ _ _ _)
    exact staticSafe_emitDo _ Op.sstore [keccak064, atomE tag d v] hp
      (by simp [staticSafeOp])
      (by simp [staticSafeExprs, staticSafe_keccak064 memoryGuardK (by simp [memoryGuardK]),
        staticSafe_atomE])
  | storeMap2 f k₁ k₂ v =>
    simp only [emitStmt]
    have hp := staticSafe_emitMap2SlotPrep e f (atomE tag d k₁) (atomE tag d k₂) he
      (staticSafe_atomE _ _ _ _) (staticSafe_atomE _ _ _ _)
    exact staticSafe_emitDo _ Op.sstore [keccak064, atomE tag d v] hp
      (by simp [staticSafeOp])
      (by simp [staticSafeExprs, staticSafe_keccak064 memoryGuardK (by simp [memoryGuardK]),
        staticSafe_atomE])
  | require cond err args =>
    simp only [emitStmt]
    simp only [stmtWF, Bool.and_eq_true] at hwf
    exact staticSafe_emitIf e _ (emitCustomError c {} err (args.map (atomE tag d))).stmts he
      (by simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, staticSafe_emitCond])
      (staticSafe_emitCustomError c {} err _ (staticSafe_nilEmit _)
        (staticSafeExprs_map_atom _ _ _ _)
        (by simpa [List.length_map] using errorOK_fits hwf.1.2))
  | emit ev args =>
    simp only [emitStmt]
    simp only [stmtWF, Bool.and_eq_true] at hwf
    exact staticSafe_emitLog1 e _ (args.map (atomE tag d)) he
      (staticSafeExprs_map_atom _ _ _ _)
      (by simpa [List.length_map] using eventOK_fits hwf.1)
  | revert err args =>
    simp only [emitStmt]
    simp only [stmtWF, Bool.and_eq_true] at hwf
    exact staticSafe_emitCustomError c e err (args.map (atomE tag d)) he
      (staticSafeExprs_map_atom _ _ _ _)
      (by simpa [List.length_map] using errorOK_fits hwf.1)
  | call b m args =>
    simp only [emitStmt]
    simp only [stmtWF] at hwf
    exact staticSafe_emitExtCall tag c e d b m args none he (callWF_fits c b m args hwf)

theorem staticSafe_emitRet (e : Emit) (d : Nat) (halt : Bool) {t} (r : RetExpr t)
    (he : staticSafeStmts memoryGuardK e.stmts = true)
    (hn : (retAtoms r).length ≤ 4) :
    staticSafeStmts memoryGuardK (emitRet tag e d halt r).stmts = true := by
  cases r with
  | unit =>
    simp only [emitRet]
    exact staticSafe_emitReturnUnit e halt he
  | word a | addr a | flag a =>
    simp only [emitRet, retAtoms, List.map_cons, List.map_nil] at hn ⊢
    exact staticSafe_emitReturnWords e _ he
      (by simp [staticSafeExprs, staticSafe_atomE]) (by simp)
  | pair x y =>
    simp only [emitRet]
    exact staticSafe_emitReturnWords e ((retAtoms x ++ retAtoms y).map (atomE tag d)) he
      (staticSafeExprs_map_atom _ _ _ _) (by simpa [List.length_map, retAtoms] using hn)

theorem staticSafe_emitParams (e : Emit) (offset n : Nat)
    (he : staticSafeStmts memoryGuardK e.stmts = true) :
    staticSafeStmts memoryGuardK (emitParams tag e offset n).stmts = true := by
  induction n generalizing e with
  | zero => simpa [emitParams_zero] using he
  | succ n ih =>
    rw [emitParams_succ, Emit.stmts_push]
    simp [staticSafeStmts_append, staticSafeStmts, ih e he, staticSafeStmt_letSome,
      bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit]

theorem coreWF_ret_fits {c t} {r : RetExpr t}
    (h : coreWF c (.ret r) = true) : (retAtoms r).length ≤ 4 := by
  simp [coreWF, Bool.and_eq_true, fitsGuardWords_iff] at h
  exact h.2

theorem staticSafe_emitCore (c : ContractDef) (halt : Bool) {t} (core : Core t)
    (hwf : coreWF c core = true) :
    ∀ (e : Emit) (d : Nat), staticSafeStmts memoryGuardK e.stmts = true →
      ∀ e', emitCore tag c e d halt core = some e' →
        staticSafeStmts memoryGuardK e'.stmts = true := by
  induction core with
  | ret r =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact staticSafe_emitRet tag e d halt r he (coreWF_ret_fits hwf)
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    cases hop : emitLetOp tag c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have he1 := staticSafe_emitLetOp tag c e d op he hopWF hop
      cases h
      exact staticSafe_emitRet tag e1 (d + 1) halt _ he1 (by simp [retAtoms])
  | stmtTail s =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    have hsWF : stmtWF c s = true := by simpa [coreWF] using hwf
    exact staticSafe_emitReturnUnit (emitStmt tag c e d s) halt
      (staticSafe_emitStmt tag c e d s he hsWF)
  | revertTail err args =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    have herr : errorOK c err args.length = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.1
    exact staticSafe_emitCustomError c e err (args.map (atomE tag d)) he
      (staticSafeExprs_map_atom _ _ _ _)
      (by simpa [List.length_map] using errorOK_fits herr)
  | letOp op k ih =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind] at h
    cases hop : emitLetOp tag c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      have hopWF : opWF c op = true := by
        simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.1
      have hkWF : coreWF c k = true := by
        simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.2
      exact ih hkWF e1 (d + 1) (staticSafe_emitLetOp tag c e d op he hopWF hop) e' h
  | seq s k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    have hsWF : stmtWF c s = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.1
    have hkWF : coreWF c k = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.2
    exact ih hkWF (emitStmt tag c e d s) d (staticSafe_emitStmt tag c e d s he hsWF) e' h
  | letPure p args k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    have hkWF : coreWF c k = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.2
    exact ih hkWF (emitLet e (identV tag d) (emitPrim tag d p args)) (d + 1)
      (staticSafe_emitLet e _ _ he (staticSafe_emitPrim tag d p args)) e' h
  | ite cond a b iha ihb =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    have hcond : condWF cond = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.1.1
    have haWF : coreWF c a = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.1.2
    have hbWF : coreWF c b = true := by
      simp [coreWF, Bool.and_eq_true] at hwf; exact hwf.2
    cases ha : emitCore tag c {} d halt a with
    | none => simp [ha] at h
    | some eA =>
      simp [ha] at h
      cases hb : emitCore tag c {} d halt b with
      | none => simp [hb] at h
      | some eB =>
        simp [hb] at h
        cases h
        have hA := iha haWF {} d (staticSafe_nilEmit _) _ ha
        have hB := ihb hbWF {} d (staticSafe_nilEmit _) _ hb
        exact staticSafe_emit_push _ e _ he (by
          simp [staticSafeStmt_switch, staticSafe_emitCond, staticSafeCases, staticSafeStmts, hA, hB])

theorem staticSafe_toYulFn {c f yul} (h : toYulFn c f = some yul) :
    staticSafeStmts memoryGuardK yul = true := by
  unfold toYulFn at h
  cases hwf : coreWF c f.core
  · simp [hwf] at h
  cases hnd : identsNodup f.name (maxDepth f)
  · simp [hwf, hnd] at h
  simp [hwf, hnd, Option.map_eq_some_iff] at h
  obtain ⟨e, hem, rfl⟩ := h
  have hp := staticSafe_emitParams f.name {}
    (if f.kind = .constructor then 0 else 4) f.params.length (staticSafe_nilEmit _)
  have hhalt : (f.kind ≠ .constructor : Bool) = !decide (f.kind = .constructor) := by
    cases f.kind <;> simp
  exact staticSafe_emitCore f.name c (f.kind ≠ .constructor) f.core hwf _ f.params.length hp e
    (hhalt ▸ hem)

theorem staticSafe_guardLt (n : Nat) :
    staticSafeStmts memoryGuardK (emitGuardLt {} n).stmts = true := by
  simp [emitGuardLt, Emit.stmts_push, staticSafeStmts_append, staticSafeStmts,
    staticSafeStmt_cond, staticSafe_revert00, bop, staticSafeExpr_builtin, staticSafeOp,
    staticSafeExprs, lit, staticSafe_nilEmit]

theorem staticSafe_entryCase {c f p} (h : entryCase c f = some p) :
    staticSafeStmts memoryGuardK p.2 = true := by
  simp [entryCase, Bind.bind, Option.bind] at h
  cases hb : toYulFn c f <;> simp [hb] at h
  cases h
  simp [staticSafeStmts, staticSafeStmt, staticSafe_guardLt, staticSafe_toYulFn hb]

theorem staticSafe_mapM_entryCase {c : ContractDef} :
    ∀ {fs : List FnDef} {cases : List (Literal × YBlock)},
      fs.mapM (entryCase c) = some cases →
        staticSafeCases memoryGuardK cases = true
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
        simp [staticSafeCases, staticSafe_entryCase hf, staticSafe_mapM_entryCase hr]

theorem staticSafe_selector :
    staticSafeExpr memoryGuardK
      (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) = true := by
  simp [bop, staticSafeExpr_builtin, staticSafeOp, staticSafeExprs, lit]

theorem staticSafe_dispatchTail (cases : List (Literal × YBlock))
    (hc : staticSafeCases memoryGuardK cases = true) :
    staticSafeStmts memoryGuardK
      [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
        YulSemantics.Stmt.switch
          (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
          cases (some [revert00])] = true := by
  simp [staticSafeStmts, staticSafeStmt_block, staticSafeStmt_switch, staticSafe_guardLt,
    staticSafe_selector, hc, staticSafe_revert00]

theorem staticSafe_erase_runtime {c yul} (h : runtimeBlock c = some yul) :
    staticSafeStmts memoryGuardK (eraseMemoryGuardStmts yul) = true := by
  obtain ⟨cases, hmap, hE⟩ := erase_runtimeBlock h
  rw [hE]
  simp [staticSafeStmts, staticSafeStmt_cond, staticSafeStmt_block, staticSafeStmt_switch,
    memoryGuardErased]
  exact ⟨staticSafe_guardLt 4,
    ⟨⟨staticSafe_selector, staticSafe_mapM_entryCase hmap⟩, staticSafe_revert00 memoryGuardK⟩⟩

theorem staticSafe_resolve_runtime {c yul} (h : runtimeBlock c = some yul)
    (reserved : Nat) :
    staticSafeStmts memoryGuardK
      (resolveMemoryGuardStmts memoryGuardK reserved yul) = true := by
  obtain ⟨cases, hmap, hR⟩ := resolve_runtimeBlock h reserved
  rw [hR]
  simp [staticSafeStmts, staticSafeStmt_cond, staticSafeStmt_block, staticSafeStmt_switch]
  exact ⟨staticSafe_guardLt 4,
    ⟨⟨staticSafe_selector, staticSafe_mapM_entryCase hmap⟩, staticSafe_revert00 memoryGuardK⟩⟩

end Lsc.Compiler
