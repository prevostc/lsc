import Lsc.Compiler.Proof.GasLift
import Lsc.Compiler.Proof.Erase
import Lsc.Compiler.Proof.Env
import Lsc.Compiler.DispatchDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
Lsc never emits `gas()`. Spill rewriting only adds `mload`/`mstore` of
scratch slots, so a successful `spillBlock?` stays `noGasStmts`. Used to
re-lower a spilled run from `ExternalGas.any` to `.none` for S2
`compile_correct` (`GasCallsRealized.noneOracle`).
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect

theorem noGasOp_not_gas {op : YOp} (h : op ≠ .gas) : noGasOp op = true := by
  cases op <;> simp [noGasOp] at h ⊢

theorem noGas_lit (n : Nat) : noGasExpr (lit n) = true := by
  simp [noGasExpr, lit]

theorem noGas_var (x : YIdent) : noGasExpr (var x) = true := by
  simp [noGasExpr, var]

theorem noGas_bop (op : YOp) (args : List YExpr)
    (hop : noGasOp op = true) (ha : noGasExprs args = true) :
    noGasExpr (bop op args) = true := by
  simp [bop, noGasExpr, hop, ha]

theorem noGas_atom (d : Nat) (a : Atom) : noGasExpr (atomE tag d a) = true := by
  cases a with
  | var i =>
    simp only [atomE]
    split <;> simp [noGasExpr, var, lit]
  | lit n => simp [atomE, noGasExpr, lit]

theorem noGasExprs_nil : noGasExprs [] = true := rfl

theorem noGasExprs_cons (e : YExpr) (es : List YExpr) :
    noGasExprs (e :: es) = (noGasExpr e && noGasExprs es) := rfl

theorem noGasExprs_of_all (args : List YExpr)
    (h : ∀ e ∈ args, noGasExpr e = true) : noGasExprs args = true := by
  induction args with
  | nil => rfl
  | cons e es ih =>
    rw [noGasExprs_cons, Bool.and_eq_true]
    exact ⟨h e (by simp), ih (fun e' he' => h e' (by simp [he']))⟩

theorem noGasExprs_map_atom (d : Nat) (as : List Atom) :
    noGasExprs (as.map (atomE tag d)) = true :=
  noGasExprs_of_all _ (fun e he => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact noGas_atom tag d a)

theorem noGas_revert00 : noGasStmt revert00 = true := by
  simp [revert00, noGasStmt, bop, noGasExpr, noGasOp, noGasExprs, lit]

theorem noGas_stopStmt : noGasStmt stopStmt = true := by
  simp [stopStmt, noGasStmt, bop, noGasExpr, noGasOp, noGasExprs]

theorem noGas_guardLt (n : Nat) :
    noGasStmts (emitGuardLt {} n).stmts = true := by
  simp [emitGuardLt, Emit.push, Emit.stmts, noGasStmts, noGasStmt, bop,
    noGasExpr, noGasOp, noGasExprs, lit, noGas_revert00]

theorem noGasStmts_append (a b : YBlock) :
    noGasStmts (a ++ b) = (noGasStmts a && noGasStmts b) := by
  induction a with
  | nil => simp [noGasStmts]
  | cons s rest ih => simp [noGasStmts, ih, Bool.and_assoc]

theorem noGasStmts_reverse (b : YBlock) :
    noGasStmts b.reverse = noGasStmts b := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
    simp [List.reverse_cons, noGasStmts_append, noGasStmts, ih, Bool.and_comm]

theorem noGas_nilEmit : noGasStmts ({} : Emit).stmts = true := rfl

theorem noGas_emit_push (e : Emit) (s : YStmt)
    (he : noGasStmts e.stmts = true) (hs : noGasStmt s = true) :
    noGasStmts (e.push s).stmts = true := by
  simp [Emit.stmts_push, noGasStmts_append, noGasStmts, he, hs]

theorem noGas_emitDo (e : Emit) (op : YOp) (args : List YExpr)
    (he : noGasStmts e.stmts = true) (hop : noGasOp op = true)
    (ha : noGasExprs args = true) :
    noGasStmts (emitDo e op args).stmts = true :=
  noGas_emit_push e _ he (by simp [noGasStmt, noGasExpr, hop, ha])

theorem noGas_emitLet (e : Emit) (n : YIdent) (x : YExpr)
    (he : noGasStmts e.stmts = true) (hx : noGasExpr x = true) :
    noGasStmts (emitLet e n x).stmts = true :=
  noGas_emit_push e _ he (by simp [noGasStmt, hx])

theorem noGas_emitAssign (e : Emit) (n : YIdent) (x : YExpr)
    (he : noGasStmts e.stmts = true) (hx : noGasExpr x = true) :
    noGasStmts (emitAssign e n x).stmts = true :=
  noGas_emit_push e _ he (by simp [noGasStmt, hx])

theorem noGas_emitIf (e : Emit) (cnd : YExpr) (body : YBlock)
    (he : noGasStmts e.stmts = true) (hc : noGasExpr cnd = true)
    (hb : noGasStmts body = true) :
    noGasStmts (emitIf e cnd body).stmts = true :=
  noGas_emit_push e _ he (by simp [noGasStmt, hc, hb])

theorem noGas_emitBlock (e : Emit) (body : YBlock)
    (he : noGasStmts e.stmts = true) (hb : noGasStmts body = true) :
    noGasStmts (emitBlock e body).stmts = true :=
  noGas_emit_push e _ he (by simp [noGasStmt, hb])

theorem noGas_keccak064 : noGasExpr keccak064 = true := by
  simp [keccak064, bop, noGasExpr, noGasOp, noGasExprs, lit]

theorem noGas_panicStmts (code : Nat) :
    noGasStmts (emitPanic {} code).stmts = true := by
  simp [emitPanic, emitDo, Emit.push, Emit.stmts, noGasStmts, noGasStmt, bop,
    noGasExpr, noGasOp, noGasExprs, lit]

theorem noGas_foldl_mstore (base : Nat) (xs : List YExpr) (i0 : Nat) :
    ∀ (e : Emit), noGasStmts e.stmts = true → noGasExprs xs = true →
      noGasStmts (xs.foldl (fun p a =>
          (emitDo p.1 Op.mstore [lit (base + 32 * p.2), a], p.2 + 1)) (e, i0)).1.stmts = true := by
  induction xs generalizing i0 with
  | nil =>
    intro e he _hx
    simpa [List.foldl] using he
  | cons x rest ih =>
    intro e he hx
    simp only [noGasExprs, Bool.and_eq_true] at hx
    simp only [List.foldl_cons]
    exact ih (i0 + 1) (emitDo e Op.mstore [lit (base + 32 * i0), x])
      (noGas_emitDo e _ _ he (by simp [noGasOp])
        (by simp [noGasExprs, noGasExpr, lit, hx.1])) hx.2

theorem noGas_emitCustomError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExprs args = true) :
    noGasStmts (emitCustomError c e err args).stmts = true := by
  unfold emitCustomError
  set sel := match c.errors[err]? with | some ed => ed.selector | none => 0
  have h1 := noGas_emitDo e Op.mstore
    [lit abiPtr, bop Op.shl [lit 224, lit sel]] he (by simp [noGasOp])
    (by simp [noGasExprs, noGasExpr, lit, bop, noGasOp])
  have h2 := noGas_foldl_mstore abiAfterSel args 0 _ h1 ha
  exact noGas_emitDo _ Op.revert [lit abiPtr, lit (4 + 32 * args.length)] h2
    (by simp [noGasOp]) (by simp [noGasExprs, noGasExpr, lit])

theorem noGas_emitReturnWords (e : Emit) (xs : List YExpr)
    (he : noGasStmts e.stmts = true) (hx : noGasExprs xs = true) :
    noGasStmts (emitReturnWords e xs).stmts = true := by
  cases xs with
  | nil =>
    simp [emitReturnWords]
    exact noGas_emit_push e stopStmt he noGas_stopStmt
  | cons x rest =>
    simp only [emitReturnWords]
    have h1 := noGas_foldl_mstore abiPtr (x :: rest) 0 e he hx
    exact noGas_emitDo _ Op.ret [lit abiPtr, lit (32 * (x :: rest).length)] h1
      (by simp [noGasOp]) (by simp [noGasExprs, noGasExpr, lit])

theorem noGas_emitReturnUnit (e : Emit) (halt : Bool)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitReturnUnit e halt).stmts = true := by
  simp [emitReturnUnit]
  split
  · exact noGas_emit_push e stopStmt he noGas_stopStmt
  · exact he

theorem noGas_emitLog1 (e : Emit) (topic : Nat) (args : List YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExprs args = true) :
    noGasStmts (emitLog1 e topic args).stmts = true := by
  unfold emitLog1
  have h1 := noGas_foldl_mstore abiPtr args 0 e he ha
  exact noGas_emitDo _ Op.log1 [lit abiPtr, lit (32 * args.length), lit topic] h1
    (by simp [noGasOp]) (by simp [noGasExprs, noGasExpr, lit])

theorem noGas_emitMapSlotPrep (e : Emit) (slot : Nat) (k : YExpr)
    (he : noGasStmts e.stmts = true) (hk : noGasExpr k = true) :
    noGasStmts (emitMapSlotPrep e slot k).stmts = true := by
  unfold emitMapSlotPrep
  have h1 := noGas_emitDo e Op.mstore [lit 0, k] he (by simp [noGasOp])
    (by simp [noGasExprs, noGasExpr, lit, hk])
  exact noGas_emitDo _ Op.mstore [lit 32, lit slot] h1 (by simp [noGasOp])
    (by simp [noGasExprs, noGasExpr, lit])

theorem noGas_emitMap2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr)
    (he : noGasStmts e.stmts = true) (h1 : noGasExpr k₁ = true) (h2 : noGasExpr k₂ = true) :
    noGasStmts (emitMap2SlotPrep e slot k₁ k₂).stmts = true := by
  unfold emitMap2SlotPrep
  have hp := noGas_emitMapSlotPrep e slot k₁ he h1
  have hk := noGas_emitDo _ Op.mstore [lit 32, keccak064] hp (by simp [noGasOp])
    (by simp [noGasExprs, noGasExpr, lit, noGas_keccak064])
  exact noGas_emitDo _ Op.mstore [lit 0, k₂] hk (by simp [noGasOp])
    (by simp [noGasExprs, noGasExpr, lit, h2])

theorem noGas_emitMulOverflowGuard (e : Emit) (a b p : YExpr)
    (he : noGasStmts e.stmts = true)
    (ha : noGasExpr a = true) (hb : noGasExpr b = true) (hp : noGasExpr p = true) :
    noGasStmts (emitMulOverflowGuard e a b p).stmts = true := by
  unfold emitMulOverflowGuard
  refine noGas_emitIf e _ _ he ?_ (noGas_panicStmts 0x11)
  simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb, hp]

theorem noGas_emitAddChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExpr a = true) (hb : noGasExpr b = true) :
    noGasStmts (emitAddChecked e name a b).stmts = true := by
  unfold emitAddChecked
  have hl := noGas_emitLet e name (bop Op.add [a, b]) he
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb])
  exact noGas_emitIf _ _ _ hl
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, var, ha]) (noGas_panicStmts 0x11)

theorem noGas_emitSubChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExpr a = true) (hb : noGasExpr b = true) :
    noGasStmts (emitSubChecked e name a b).stmts = true := by
  simpa [emitSubChecked] using
    noGas_emitLet (emitIf e (bop Op.lt [a, b]) (emitPanic {} 0x11).stmts) name
      (bop Op.sub [a, b])
      (noGas_emitIf e _ (emitPanic {} 0x11).stmts he
        (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb]) (noGas_panicStmts _))
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb])

theorem noGas_emitMulChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExpr a = true) (hb : noGasExpr b = true) :
    noGasStmts (emitMulChecked e name a b).stmts = true := by
  unfold emitMulChecked
  have hl := noGas_emitLet e name (bop Op.mul [a, b]) he
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb])
  exact noGas_emitMulOverflowGuard _ a b (var name) hl ha hb (by simp [noGasExpr, var])

theorem noGas_emitDivChecked (e : Emit) (name : YIdent) (a b : YExpr)
    (he : noGasStmts e.stmts = true) (ha : noGasExpr a = true) (hb : noGasExpr b = true) :
    noGasStmts (emitDivChecked e name a b).stmts = true := by
  simpa [emitDivChecked] using
    noGas_emitLet (emitIf e (bop Op.iszero [b]) (emitPanic {} 0x12).stmts) name
      (bop Op.div [a, b])
      (noGas_emitIf e _ (emitPanic {} 0x12).stmts he
        (by simp [bop, noGasExpr, noGasOp, noGasExprs, hb]) (noGas_panicStmts _))
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb])

theorem noGas_emitPow10 (e : Emit) (name : YIdent) (d : YExpr)
    (he : noGasStmts e.stmts = true) (hd : noGasExpr d = true) :
    noGasStmts (emitPow10 e name d).stmts = true := by
  simpa [emitPow10] using
    noGas_emitLet (emitIf e (bop Op.gt [d, lit 77]) (emitPanic {} 0x11).stmts) name
      (bop Op.exp [lit 10, d])
      (noGas_emitIf e _ (emitPanic {} 0x11).stmts he
        (by simp [bop, noGasExpr, noGasOp, noGasExprs, hd, noGas_lit]) (noGas_panicStmts _))
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, hd, noGas_lit])

theorem noGas_emitMulDivDown (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noGasStmts e.stmts = true)
    (ha : noGasExpr a = true) (hb : noGasExpr b = true) (hc : noGasExpr c = true) :
    noGasStmts (emitMulDivDown e name a b c).stmts = true := by
  simpa [emitMulDivDown] using
    (noGas_emit_push
      (emitMulOverflowGuard
        (emitLet (emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts) name
          (bop Op.mul [a, b]))
        a b (var name))
      (.assign [name] (bop Op.div [var name, c]))
      (noGas_emitMulOverflowGuard _
        a b (var name)
        (noGas_emitLet _ name (bop Op.mul [a, b])
          (noGas_emitIf e _ (emitPanic {} 0x12).stmts he
            (by simp [bop, noGasExpr, noGasOp, noGasExprs, hc]) (noGas_panicStmts _))
          (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb]))
        ha hb (by simp [noGasExpr, var]))
      (by simp [noGasStmt, bop, noGasExpr, noGasOp, noGasExprs, var, hc]))

theorem noGas_emitMulDivUp (e : Emit) (name : YIdent) (a b c : YExpr)
    (he : noGasStmts e.stmts = true)
    (ha : noGasExpr a = true) (hb : noGasExpr b = true) (hc : noGasExpr c = true) :
    noGasStmts (emitMulDivUp e name a b c).stmts = true := by
  simpa [emitMulDivUp] using
    (noGas_emit_push
      (emitMulOverflowGuard
        (emitLet (emitIf e (bop Op.iszero [c]) (emitPanic {} 0x12).stmts) name
          (bop Op.mul [a, b]))
        a b (var name))
      (.switch (bop Op.mod [var name, c])
        [(Literal.number 0, [Stmt.assign [name] (bop Op.div [var name, c])])]
        (some [Stmt.assign [name] (bop Op.add [bop Op.div [var name, c], lit 1])]))
      (noGas_emitMulOverflowGuard _
        a b (var name)
        (noGas_emitLet _ name (bop Op.mul [a, b])
          (noGas_emitIf e _ (emitPanic {} 0x12).stmts he
            (by simp [bop, noGasExpr, noGasOp, noGasExprs, hc]) (noGas_panicStmts _))
          (by simp [bop, noGasExpr, noGasOp, noGasExprs, ha, hb]))
        ha hb (by simp [noGasExpr, var]))
      (by simp [noGasStmt, noGasCases, noGasDflt, noGasStmts, bop, noGasExpr, noGasOp,
        noGasExprs, var, lit, hc]))

theorem noGas_emitCallRetCheck (e : Emit) (ret : AbiRet)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitCallRetCheck e ret).stmts = true := by
  cases ret with
  | boolOpt =>
    simp [emitCallRetCheck]
    exact noGas_emitIf e _ _ he
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])
      (by simp [noGasStmts, noGas_revert00])
  | word =>
    simp [emitCallRetCheck]
    exact noGas_emitIf e _ _ he
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])
      (by simp [noGasStmts, noGas_revert00])
  | none => simpa [emitCallRetCheck] using he

theorem noGas_emitCond tag (d : Nat) : ∀ c, noGasExpr (emitCond tag d c) = true
  | .lt a b | .le a b | .eq a b | .ne a b => by
    simp [emitCond, bop, noGasExpr, noGasOp, noGasExprs, noGas_atom]
  | .and c d' => by
    simp [emitCond, bop, noGasExpr, noGasOp, noGasExprs, noGas_emitCond tag d c,
      noGas_emitCond tag d d']
  | .or c d' => by
    simp [emitCond, bop, noGasExpr, noGasOp, noGasExprs, noGas_emitCond tag d c,
      noGas_emitCond tag d d']
  | .not c => by
    simp [emitCond, bop, noGasExpr, noGasOp, noGasExprs, noGas_emitCond tag d c]
  | .tt | .ff => by simp [emitCond, noGasExpr, lit]

theorem noGas_emitPrim tag (d : Nat) (p : Prim) (args : List Atom) :
    noGasExpr (emitPrim tag d p args) = true := by
  cases p <;> cases args with
  | nil => simp [emitPrim, noGasExpr, lit]
  | cons a rest =>
    cases rest with
    | nil =>
      simp [emitPrim, noGas_atom, noGasExpr, lit]
    | cons b rest2 =>
      cases rest2 with
      | nil => simp [emitPrim, bop, noGasExpr, noGasOp, noGasExprs, noGas_atom, lit]
      | cons _ _ => simp [emitPrim, noGasExpr, lit]

theorem noGas_foldl_mstore_atoms tag (depth base : Nat) (args : List Atom) (i0 : Nat) :
    ∀ (e : Emit), noGasStmts e.stmts = true →
      noGasStmts (args.foldl (fun p a =>
          (emitDo p.1 Op.mstore [lit (base + 32 * p.2), atomE tag depth a], p.2 + 1))
        (e, i0)).1.stmts = true := by
  induction args generalizing i0 with
  | nil =>
    intro e he
    simpa [List.foldl] using he
  | cons a rest ih =>
    intro e he
    simp only [List.foldl_cons]
    exact ih (i0 + 1) (emitDo e Op.mstore [lit (base + 32 * i0), atomE tag depth a])
      (noGas_emitDo e _ _ he (by simp [noGasOp])
        (by simp [noGasExprs, noGasExpr, lit, noGas_atom]))

theorem noGas_emitExtCallBody tag (c : ContractDef) (depth b m : Nat) (args : List Atom)
    (assign : Option YIdent) :
    noGasStmts (emitExtCallBody tag c depth b m args assign) = true := by
  have h0 : noGasStmts ({} : Emit).stmts = true := noGas_nilEmit
  have hlet := noGas_emitLet ({} : Emit) (extTok tag depth)
    (bop Op.sload [lit (bindingSlot c b)]) h0
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])
  have hsel := noGas_emitDo _ Op.mstore
    [lit abiPtr, bop Op.shl [lit 224, lit (bindingMethod c b m).1]] hlet (by simp [noGasOp])
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])
  have hargs := noGas_foldl_mstore_atoms tag depth abiAfterSel args 0 _ hsel
  have hcall := noGas_emitLet _ (extOk tag depth)
    (bop YulSemantics.EVM.Op.call
      [lit extCallGas, var (extTok tag depth), lit 0, lit abiPtr,
        lit (4 + 32 * args.length), lit abiPtr, lit 32]) hargs
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit, var])
  have hif := noGas_emitIf _ (bop Op.iszero [var (extOk tag depth)]) [revert00] hcall
    (by simp [bop, noGasExpr, noGasOp, noGasExprs, var]) (by simp [noGasStmts, noGas_revert00])
  have hret := noGas_emitCallRetCheck _ (bindingMethod c b m).2 hif
  cases assign with
  | none =>
    convert hret using 1
    simp [emitExtCallBody]
  | some name =>
    cases hrv : (bindingMethod c b m).2 with
    | boolOpt | none =>
      convert (noGas_emitAssign _ name (lit 1) hret (by simp [noGasExpr, lit])) using 1
      simp [emitExtCallBody, hrv]
    | word =>
      convert (noGas_emitAssign _ name (bop Op.mload [lit abiPtr]) hret
        (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])) using 1
      simp [emitExtCallBody, hrv]

theorem noGas_emitExtCall tag (c : ContractDef) (e : Emit) (depth b m : Nat)
    (args : List Atom) (bind : Option YIdent)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitExtCall tag c e depth b m args bind).stmts = true := by
  cases bind with
  | none =>
    simp [emitExtCall, emitBlock]
    exact noGas_emitBlock e _ he (noGas_emitExtCallBody tag c depth b m args none)
  | some name =>
    simp [emitExtCall, emitBlock]
    have hl := noGas_emitLet e name (lit 0) he (by simp [noGasExpr, lit])
    exact noGas_emitBlock _ _ hl (noGas_emitExtCallBody tag c depth b m args (some name))

theorem noGas_emitLetOp tag (c : ContractDef) (e : Emit) (d : Nat) (op : Lsc.Op)
    (he : noGasStmts e.stmts = true) {e'}
    (h : emitLetOp tag c e d op = some e') :
    noGasStmts e'.stmts = true := by
  cases op with
  | load f =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitLet e _ (bop Op.sload [lit f]) he
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, lit])
  | loadMap f k =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := noGas_emitMapSlotPrep e f (atomE tag d k) he (noGas_atom tag d k)
    exact noGas_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, noGas_keccak064])
  | loadMap2 f k₁ k₂ =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    have hp := noGas_emitMap2SlotPrep e f (atomE tag d k₁) (atomE tag d k₂) he
      (noGas_atom tag d k₁) (noGas_atom tag d k₂)
    exact noGas_emitLet _ _ (bop Op.sload [keccak064]) hp
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, noGas_keccak064])
  | sender | value | timestamp | blockNumber | selfAddress =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitLet e _ _ he (by simp [bop, noGasExpr, noGasOp, noGasExprs])
  | addChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitAddChecked e _ (atomE tag d a) (atomE tag d b) he
      (noGas_atom tag d a) (noGas_atom tag d b)
  | subChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitSubChecked e _ (atomE tag d a) (atomE tag d b) he
      (noGas_atom tag d a) (noGas_atom tag d b)
  | mulChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitMulChecked e _ (atomE tag d a) (atomE tag d b) he
      (noGas_atom tag d a) (noGas_atom tag d b)
  | divChecked a b =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitDivChecked e _ (atomE tag d a) (atomE tag d b) he
      (noGas_atom tag d a) (noGas_atom tag d b)
  | mulDivDown a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitMulDivDown e _ (atomE tag d a) (atomE tag d b) (atomE tag d c) he
      (noGas_atom tag d a) (noGas_atom tag d b) (noGas_atom tag d c)
  | mulDivUp a b c =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitMulDivUp e _ (atomE tag d a) (atomE tag d b) (atomE tag d c) he
      (noGas_atom tag d a) (noGas_atom tag d b) (noGas_atom tag d c)
  | pow10 a =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitPow10 e _ (atomE tag d a) he (noGas_atom tag d a)
  | pure a =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitLet e _ (atomE tag d a) he (noGas_atom tag d a)
  | call b m args =>
    simp only [emitLetOp, Option.some.injEq] at h; subst e'
    exact noGas_emitExtCall tag c e d b m args (some (identV tag d)) he

theorem noGas_emitStmt tag (c : ContractDef) (e : Emit) (d : Nat) (s : Lsc.Stmt)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitStmt tag c e d s).stmts = true := by
  cases s with
  | store f v =>
    simp only [emitStmt]
    exact noGas_emitDo e Op.sstore [lit f, atomE tag d v] he (by simp [noGasOp])
      (by simp [noGasExprs, noGasExpr, lit, noGas_atom])
  | storeMap f k v =>
    simp only [emitStmt]
    have hp := noGas_emitMapSlotPrep e f (atomE tag d k) he (noGas_atom tag d k)
    exact noGas_emitDo _ Op.sstore [keccak064, atomE tag d v] hp (by simp [noGasOp])
      (by simp [noGasExprs, noGas_keccak064, noGas_atom])
  | storeMap2 f k₁ k₂ v =>
    simp only [emitStmt]
    have hp := noGas_emitMap2SlotPrep e f (atomE tag d k₁) (atomE tag d k₂) he
      (noGas_atom tag d k₁) (noGas_atom tag d k₂)
    exact noGas_emitDo _ Op.sstore [keccak064, atomE tag d v] hp (by simp [noGasOp])
      (by simp [noGasExprs, noGas_keccak064, noGas_atom])
  | require cond err args =>
    simp only [emitStmt]
    exact noGas_emitIf e _ _ he
      (by simp [bop, noGasExpr, noGasOp, noGasExprs, noGas_emitCond])
      (noGas_emitCustomError c {} err (args.map (atomE tag d)) noGas_nilEmit
        (noGasExprs_map_atom tag d args))
  | emit ev args =>
    simp only [emitStmt]
    exact noGas_emitLog1 e _ (args.map (atomE tag d)) he (noGasExprs_map_atom tag d args)
  | revert err args =>
    simp only [emitStmt]
    exact noGas_emitCustomError c e err (args.map (atomE tag d)) he
      (noGasExprs_map_atom tag d args)
  | call b m args =>
    simp only [emitStmt]
    exact noGas_emitExtCall tag c e d b m args none he

theorem noGas_emitRet tag (e : Emit) (d : Nat) (halt : Bool) {t} (r : RetExpr t)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitRet tag e d halt r).stmts = true := by
  cases r with
  | unit =>
    simp [emitRet]
    exact noGas_emitReturnUnit e halt he
  | word a | addr a | flag a =>
    simp [emitRet]
    exact noGas_emitReturnWords e _ he (noGasExprs_map_atom tag d _)
  | pair x y =>
    simp [emitRet]
    exact noGas_emitReturnWords e ((retAtoms x ++ retAtoms y).map (atomE tag d)) he
      (noGasExprs_map_atom tag d _)

theorem noGas_emitParams tag (e : Emit) (offset n : Nat)
    (he : noGasStmts e.stmts = true) :
    noGasStmts (emitParams tag e offset n).stmts = true := by
  induction n generalizing e with
  | zero => simpa [emitParams_zero] using he
  | succ n ih =>
    rw [emitParams_succ, Emit.stmts_push]
    simp [noGasStmts_append, noGasStmts, ih e he, noGasStmt, bop, noGasExpr, noGasOp,
      noGasExprs, lit]

theorem noGas_emitCore tag (c : ContractDef) (halt : Bool) {t} (core : Core t) :
    ∀ (e : Emit) (d : Nat), noGasStmts e.stmts = true →
      ∀ e', emitCore tag c e d halt core = some e' → noGasStmts e'.stmts = true := by
  induction core with
  | ret r =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noGas_emitRet tag e d halt r he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    cases hop : emitLetOp tag c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      have he1 := noGas_emitLetOp tag c e d op he hop
      cases h
      exact noGas_emitRet tag e1 (d + 1) halt _ he1
  | stmtTail s =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noGas_emitReturnUnit (emitStmt tag c e d s) halt (noGas_emitStmt tag c e d s he)
  | revertTail err args =>
    intro e d he e' h
    simp only [emitCore] at h
    cases h
    exact noGas_emitCustomError c e err (args.map (atomE tag d)) he
      (noGasExprs_map_atom tag d args)
  | letOp op k ih =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind] at h
    cases hop : emitLetOp tag c e d op with
    | none => simp [hop] at h
    | some e1 =>
      simp [hop] at h
      exact ih e1 (d + 1) (noGas_emitLetOp tag c e d op he hop) e' h
  | seq s k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    exact ih (emitStmt tag c e d s) d (noGas_emitStmt tag c e d s he) e' h
  | letPure p args k ih =>
    intro e d he e' h
    simp only [emitCore] at h
    exact ih (emitLet e (identV tag d) (emitPrim tag d p args)) (d + 1)
      (noGas_emitLet e _ _ he (noGas_emitPrim tag d p args)) e' h
  | ite cond a b iha ihb =>
    intro e d he e' h
    simp only [emitCore, Bind.bind, Option.bind, Pure.pure] at h
    cases ha : emitCore tag c {} d halt a with
    | none => simp [ha] at h
    | some eA =>
      simp [ha] at h
      cases hb : emitCore tag c {} d halt b with
      | none => simp [hb] at h
      | some eB =>
        simp [hb] at h
        cases h
        have hA := iha {} d noGas_nilEmit _ ha
        have hB := ihb {} d noGas_nilEmit _ hb
        exact noGas_emit_push e _ he (by
          simp [noGasStmt, noGas_emitCond tag d cond, noGasCases, noGasStmts, noGasDflt, hA, hB])

theorem toYulFn_noGas {c f yul} (h : toYulFn c f = some yul) :
    noGasStmts yul = true := by
  unfold toYulFn at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, hem, rfl⟩ := h
  have hp := noGas_emitParams f.name {} (if f.kind = .constructor then 0 else 4) f.params.length
    noGas_nilEmit
  exact noGas_emitCore f.name c (f.kind ≠ .constructor) f.core _ f.params.length hp _ hem

theorem entryCase_noGas {c f p} (h : entryCase c f = some p) :
    noGasStmts p.2 = true := by
  simp [entryCase, Bind.bind, Option.bind] at h
  cases hb : toYulFn c f <;> simp [hb] at h
  cases h
  simp [noGasStmts, noGasStmt, noGas_guardLt, toYulFn_noGas hb]

theorem mapM_entryCase_noGas {c : ContractDef} :
    ∀ {fs : List FnDef} {cases : List (Literal × YBlock)},
      fs.mapM (entryCase c) = some cases → noGasCases cases = true
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
        simp [noGasCases, entryCase_noGas hf, mapM_entryCase_noGas hr]

theorem noGas_selector :
    noGasExpr (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) = true := by
  simp [bop, noGasExpr, noGasOp, noGasExprs, lit]

theorem noGas_memoryGuardStmt : noGasStmt memoryGuardStmt = true := by
  simp [memoryGuardStmt, noGasStmt, noGasExpr, noGasExprs, lit, noGasStmts]

theorem noGas_runtimeBlock {c yul} (h : runtimeBlock c = some yul) :
    noGasStmts yul = true := by
  obtain ⟨_, cases, hmap, hyul⟩ := runtimeBlock_inv h
  subst yul
  simp [noGasStmts, noGas_memoryGuardStmt, noGasStmt, noGas_guardLt 4, noGas_selector,
    mapM_entryCase_noGas hmap, noGasDflt, noGas_revert00]

/-! ## Spill rewrite preserves `noGasStmts` -/

theorem noGas_load (slot : Nat) : noGasExpr (load slot) = true := by
  simp [load, word, noGasExpr, noGasOp, noGasExprs]

theorem noGas_store (slot : Nat) (e : YExpr) (he : noGasExpr e = true) :
    noGasStmt (store slot e) = true := by
  simp [store, word, noGasStmt, noGasExpr, noGasOp, noGasExprs, he]

theorem noGas_distributeTemps (targets : List Nat) (temps : List Ident) :
    noGasStmts (distributeTemps targets temps) = true := by
  induction targets generalizing temps with
  | nil => simp [distributeTemps, List.zip, noGasStmts]
  | cons t ts ih =>
    cases temps with
    | nil => simp [distributeTemps, List.zip, noGasStmts]
    | cons x xs =>
      simp [distributeTemps, List.zip_cons_cons, noGasStmts]
      exact ⟨noGas_store t (var x) (noGas_var x), ih xs⟩

mutual
theorem noGas_rewriteExpr (slots : SlotMap) (owner : Owner) :
    ∀ e, noGasExpr e = true → noGasExpr (rewriteExpr slots owner e) = true
  | .lit _, h => h
  | .var x, h => by
      simp only [rewriteExpr]
      cases slotFor? slots owner x with
      | none => simp [noGasExpr]
      | some slot => exact noGas_load slot
  | .builtin op args, h => by
      simp only [rewriteExpr, noGasExpr, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, noGas_rewriteArgs slots owner args h.2⟩
  | .call f args, h => by
      simp only [rewriteExpr, noGasExpr] at h ⊢
      exact noGas_rewriteArgs slots owner args h
termination_by e => sizeOf e

theorem noGas_rewriteArgs (slots : SlotMap) (owner : Owner) :
    ∀ args, noGasExprs args = true → noGasExprs (rewriteArgs slots owner args) = true
  | [], _ => rfl
  | e :: rest, h => by
      simp only [rewriteArgs, noGasExprs, Bool.and_eq_true] at h ⊢
      exact ⟨noGas_rewriteExpr slots owner e h.1, noGas_rewriteArgs slots owner rest h.2⟩
termination_by args => sizeOf args
end

theorem noGas_initParams (slots : SlotMap) (owner : Owner) (ps : List Ident) :
    noGasStmts (initParams slots owner ps) = true := by
  induction ps with
  | nil => simp [initParams, noGasStmts]
  | cons p rest ih =>
    simp only [initParams, List.filterMap_cons]
    cases slotFor? slots owner p with
    | none => simpa [initParams] using ih
    | some slot =>
      simp [noGasStmts]
      exact ⟨noGas_store slot (var p) (noGas_var p), by simpa [initParams] using ih⟩

theorem noGas_initReturns (slots : SlotMap) (owner : Owner) (rs : List Ident) :
    noGasStmts (initReturns slots owner rs) = true := by
  induction rs with
  | nil => simp [initReturns, noGasStmts]
  | cons r rest ih =>
    simp only [initReturns, List.filterMap_cons]
    cases slotFor? slots owner r with
    | none => simpa [initReturns] using ih
    | some slot =>
      simp [noGasStmts]
      exact ⟨noGas_store slot (word 0) (by simp [word, noGasExpr]),
        by simpa [initReturns] using ih⟩

theorem noGas_copyBackReturns (slots : SlotMap) (owner : Owner) (rs : List Ident) :
    noGasStmts (copyBackReturns slots owner rs) = true := by
  induction rs with
  | nil => simp [copyBackReturns, noGasStmts]
  | cons r rest ih =>
    simp only [copyBackReturns, List.filterMap_cons]
    cases slotFor? slots owner r with
    | none => simpa [copyBackReturns] using ih
    | some slot =>
      simp [noGasStmts]
      exact ⟨by simp [noGasStmt, noGas_load], by simpa [copyBackReturns] using ih⟩

theorem noGas_zeroStores (targets : List Nat) :
    noGasStmts (targets.map fun t => store t (word 0)) = true := by
  induction targets with
  | nil => simp [noGasStmts]
  | cons t ts ih =>
    simp [noGasStmts]
    exact ⟨noGas_store t (word 0) (by simp [word, noGasExpr]), ih⟩

mutual
theorem noGas_rewriteStmt (slots : SlotMap) (owner : Owner) (exitCopies : YBlock)
    (hcopies : noGasStmts exitCopies = true) (s : YStmt)
    (h : noGasStmt s = true) :
    noGasStmts (rewriteStmt slots owner exitCopies s) = true := by
  cases s with
  | block body =>
      simp [rewriteStmt, noGasStmts, noGasStmt] at h ⊢
      exact noGas_rewriteStmts slots owner exitCopies hcopies body h
  | funDef f ps rs body =>
      simp [noGasStmt] at h
      have hbody :=
        noGas_rewriteStmts slots (some f) (copyBackReturns slots (some f) rs)
          (noGas_copyBackReturns slots (some f) rs) body h
      simpa [rewriteStmt, noGasStmts, noGasStmt, noGasStmts_append,
        noGas_initParams slots (some f) ps,
        noGas_initReturns slots (some f) rs,
        noGas_copyBackReturns slots (some f) rs] using hbody
  | letDecl xs val =>
      cases xs with
      | nil =>
          cases val with
          | none =>
              simp [rewriteStmt, targetSlots?, noGasStmts, noGasStmt, noGas_zeroStores]
          | some e =>
              simp [noGasStmt] at h
              simp [rewriteStmt, targetSlots?, noGasStmts, noGasStmt,
                noGasStmts_append, noGas_distributeTemps]
              exact noGas_rewriteExpr slots owner e h
      | cons x rest =>
          cases rest with
          | nil =>
              cases hslot : slotFor? slots owner x with
              | none =>
                  cases val with
                  | none =>
                      simp [rewriteStmt, hslot, noGasStmts, noGasStmt, word, noGasExpr]
                  | some e =>
                      simp [noGasStmt] at h
                      simp [rewriteStmt, hslot, noGasStmts, noGasStmt]
                      exact noGas_rewriteExpr slots owner e h
              | some slot =>
                  cases val with
                  | none =>
                      simp [rewriteStmt, hslot, noGasStmts]
                      exact noGas_store slot (word 0) (by simp [word, noGasExpr])
                  | some e =>
                      simp [noGasStmt] at h
                      simp [rewriteStmt, hslot, noGasStmts]
                      exact noGas_store slot _ (noGas_rewriteExpr slots owner e h)
          | cons y ys =>
              cases htg : targetSlots? slots owner (x :: y :: ys) with
              | none =>
                  cases val with
                  | none =>
                      simp [rewriteStmt, htg, noGasStmts, noGasStmt]
                  | some e =>
                      simp [noGasStmt] at h
                      simp [rewriteStmt, htg, noGasStmts, noGasStmt]
                      exact noGas_rewriteExpr slots owner e h
              | some targets =>
                  cases val with
                  | none =>
                      simp [rewriteStmt, htg, noGas_zeroStores]
                  | some e =>
                      simp [noGasStmt] at h
                      simp [rewriteStmt, htg, noGasStmts, noGasStmt,
                        noGasStmts_append, noGas_distributeTemps]
                      exact noGas_rewriteExpr slots owner e h
  | assign xs e =>
      simp [noGasStmt] at h
      cases xs with
      | nil =>
          simp [rewriteStmt, targetSlots?, noGasStmts, noGasStmt,
            noGasStmts_append, noGas_distributeTemps]
          exact noGas_rewriteExpr slots owner e h
      | cons x rest =>
          cases rest with
          | nil =>
              cases hslot : slotFor? slots owner x with
              | none =>
                  simp [rewriteStmt, hslot, noGasStmts, noGasStmt]
                  exact noGas_rewriteExpr slots owner e h
              | some slot =>
                  simp [rewriteStmt, hslot, noGasStmts]
                  exact noGas_store slot _ (noGas_rewriteExpr slots owner e h)
          | cons y ys =>
              cases htg : targetSlots? slots owner (x :: y :: ys) with
              | none =>
                  simp [rewriteStmt, htg, noGasStmts, noGasStmt]
                  exact noGas_rewriteExpr slots owner e h
              | some targets =>
                  simp [rewriteStmt, htg, noGasStmts, noGasStmt,
                    noGasStmts_append, noGas_distributeTemps]
                  exact noGas_rewriteExpr slots owner e h
  | cond c body =>
      have hc : noGasExpr c = true ∧ noGasStmts body = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      simp [rewriteStmt, noGasStmts, noGasStmt]
      exact ⟨noGas_rewriteExpr slots owner c hc.1,
        noGas_rewriteStmts slots owner exitCopies hcopies body hc.2⟩
  | «switch» c cases dflt =>
      have hc : (noGasExpr c = true ∧ noGasCases cases = true) ∧ noGasDflt dflt = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      cases dflt with
      | none =>
          simp [rewriteStmt, noGasStmts, noGasStmt, noGasDflt]
          exact ⟨noGas_rewriteExpr slots owner c hc.1.1,
            noGas_rewriteCases slots owner exitCopies hcopies cases hc.1.2⟩
      | some body =>
          simp [noGasDflt] at hc
          simp [rewriteStmt, noGasStmts, noGasStmt, noGasDflt]
          exact ⟨⟨noGas_rewriteExpr slots owner c hc.1.1,
            noGas_rewriteCases slots owner exitCopies hcopies cases hc.1.2⟩,
            noGas_rewriteStmts slots owner exitCopies hcopies body hc.2⟩
  | forLoop init c post body =>
      have hc : ((noGasStmts init = true ∧ noGasExpr c = true) ∧
          noGasStmts post = true) ∧ noGasStmts body = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      simp [rewriteStmt, noGasStmts, noGasStmt]
      exact ⟨⟨⟨noGas_rewriteStmts slots owner exitCopies hcopies init hc.1.1.1,
        noGas_rewriteExpr slots owner c hc.1.1.2⟩,
        noGas_rewriteStmts slots owner exitCopies hcopies post hc.1.2⟩,
        noGas_rewriteStmts slots owner exitCopies hcopies body hc.2⟩
  | exprStmt e =>
      simp [noGasStmt] at h
      simp [rewriteStmt, noGasStmts, noGasStmt]
      exact noGas_rewriteExpr slots owner e h
  | «break» => simp [rewriteStmt, noGasStmts, noGasStmt]
  | «continue» => simp [rewriteStmt, noGasStmts, noGasStmt]
  | «leave» =>
      simp [rewriteStmt]
      split
      · simp [noGasStmts, noGasStmt]
      · simp [noGasStmts, noGasStmt, noGasStmts_append, hcopies]
termination_by sizeOf s

theorem noGas_rewriteStmts (slots : SlotMap) (owner : Owner) (exitCopies : YBlock)
    (hcopies : noGasStmts exitCopies = true) (ss : YBlock)
    (h : noGasStmts ss = true) :
    noGasStmts (rewriteStmts slots owner exitCopies ss) = true := by
  match ss with
  | [] => simp [rewriteStmts, noGasStmts]
  | s :: rest =>
      simp only [rewriteStmts]
      simp only [noGasStmts, Bool.and_eq_true] at h
      rw [noGasStmts_append, Bool.and_eq_true]
      exact ⟨noGas_rewriteStmt slots owner exitCopies hcopies s h.1,
        noGas_rewriteStmts slots owner exitCopies hcopies rest h.2⟩
termination_by sizeOf ss

theorem noGas_rewriteCases (slots : SlotMap) (owner : Owner) (exitCopies : YBlock)
    (hcopies : noGasStmts exitCopies = true)
    (cases : List (Literal × YBlock)) (h : noGasCases cases = true) :
    noGasCases (rewriteCases slots owner exitCopies cases) = true := by
  match cases with
  | [] => simp [rewriteCases, noGasCases]
  | (l, body) :: rest =>
      simp only [rewriteCases]
      simp only [noGasCases, Bool.and_eq_true] at h ⊢
      exact ⟨noGas_rewriteStmts slots owner exitCopies hcopies body h.1,
        noGas_rewriteCases slots owner exitCopies hcopies rest h.2⟩
termination_by sizeOf cases
end

mutual
theorem noGas_resolveExpr (base reserved : Nat) (e : YExpr)
    (h : noGasExpr e = true) :
    noGasExpr (resolveMemoryGuardExpr base reserved e) = true := by
  cases e with
  | lit _ => simp [resolveMemoryGuardExpr]; exact h
  | var _ => simp [resolveMemoryGuardExpr]; exact h
  | builtin op args =>
      simp [resolveMemoryGuardExpr, noGasExpr, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, noGas_resolveArgs base reserved args h.2⟩
  | call f args =>
      simp [noGasExpr] at h
      unfold resolveMemoryGuardExpr
      split
      · split <;> simp [noGasExpr, noGasExprs]
      · rename_i f' args' heq
        cases heq
        simp [noGasExpr]
        exact noGas_resolveArgs base reserved args h
      · rename_i heq
        nomatch heq
      · simp [noGasExpr]; exact h
termination_by sizeOf e

theorem noGas_resolveArgs (base reserved : Nat) (args : List YExpr)
    (h : noGasExprs args = true) :
    noGasExprs (args.map (resolveMemoryGuardExpr base reserved)) = true := by
  match args with
  | [] => simp [noGasExprs]
  | e :: rest =>
      simp only [List.map_cons, noGasExprs, Bool.and_eq_true] at h ⊢
      exact ⟨noGas_resolveExpr base reserved e h.1, noGas_resolveArgs base reserved rest h.2⟩
termination_by sizeOf args
end

mutual
theorem noGas_resolveStmt (base reserved : Nat) (s : YStmt)
    (h : noGasStmt s = true) :
    noGasStmt (resolveMemoryGuardStmt base reserved s) = true := by
  cases s with
  | block body =>
      simp [resolveMemoryGuardStmt, noGasStmt] at h ⊢
      exact noGas_resolveStmts base reserved body h
  | funDef f ps rs body =>
      simp [resolveMemoryGuardStmt, noGasStmt] at h ⊢
      exact noGas_resolveStmts base reserved body h
  | letDecl xs val =>
      simp [resolveMemoryGuardStmt]
      cases val with
      | none => simp [noGasStmt] at h ⊢
      | some e =>
          simp [noGasStmt] at h ⊢
          exact noGas_resolveExpr base reserved e h
  | assign xs e =>
      simp [resolveMemoryGuardStmt, noGasStmt] at h ⊢
      exact noGas_resolveExpr base reserved e h
  | cond c body =>
      have hc : noGasExpr c = true ∧ noGasStmts body = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      simp [resolveMemoryGuardStmt, noGasStmt]
      exact ⟨noGas_resolveExpr base reserved c hc.1,
        noGas_resolveStmts base reserved body hc.2⟩
  | «switch» c cases dflt =>
      have hc : (noGasExpr c = true ∧ noGasCases cases = true) ∧ noGasDflt dflt = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      cases dflt with
      | none =>
          simp [resolveMemoryGuardStmt, noGasStmt, noGasDflt]
          exact ⟨noGas_resolveExpr base reserved c hc.1.1,
            noGas_resolveCases base reserved cases hc.1.2⟩
      | some body =>
          simp [noGasDflt] at hc
          simp [resolveMemoryGuardStmt, noGasStmt, noGasDflt]
          exact ⟨⟨noGas_resolveExpr base reserved c hc.1.1,
            noGas_resolveCases base reserved cases hc.1.2⟩,
            noGas_resolveStmts base reserved body hc.2⟩
  | forLoop init c post body =>
      have hc : ((noGasStmts init = true ∧ noGasExpr c = true) ∧
          noGasStmts post = true) ∧ noGasStmts body = true := by
        simpa [noGasStmt, Bool.and_eq_true] using h
      simp [resolveMemoryGuardStmt, noGasStmt]
      exact ⟨⟨⟨noGas_resolveStmts base reserved init hc.1.1.1,
        noGas_resolveExpr base reserved c hc.1.1.2⟩,
        noGas_resolveStmts base reserved post hc.1.2⟩,
        noGas_resolveStmts base reserved body hc.2⟩
  | exprStmt e =>
      simp [resolveMemoryGuardStmt, noGasStmt] at h ⊢
      exact noGas_resolveExpr base reserved e h
  | «break» => simpa [resolveMemoryGuardStmt] using h
  | «continue» => simpa [resolveMemoryGuardStmt] using h
  | «leave» => simpa [resolveMemoryGuardStmt] using h
termination_by sizeOf s

theorem noGas_resolveStmts (base reserved : Nat) (ss : YBlock)
    (h : noGasStmts ss = true) :
    noGasStmts (resolveMemoryGuardStmts base reserved ss) = true := by
  match ss with
  | [] => simp [resolveMemoryGuardStmts, noGasStmts]
  | s :: rest =>
      simp only [resolveMemoryGuardStmts, noGasStmts, Bool.and_eq_true] at h ⊢
      exact ⟨noGas_resolveStmt base reserved s h.1, noGas_resolveStmts base reserved rest h.2⟩
termination_by sizeOf ss

theorem noGas_resolveCases (base reserved : Nat)
    (cases : List (Literal × YBlock)) (h : noGasCases cases = true) :
    noGasCases (resolveMemoryGuardCases base reserved cases) = true := by
  match cases with
  | [] => simp [resolveMemoryGuardCases, noGasCases]
  | (l, body) :: rest =>
      simp only [resolveMemoryGuardCases, noGasCases, Bool.and_eq_true] at h ⊢
      exact ⟨noGas_resolveStmts base reserved body h.1,
        noGas_resolveCases base reserved rest h.2⟩
termination_by sizeOf cases
end

theorem noGas_spillBlock {b : YBlock} {r : Result}
    (h : spillBlock? b = some r) (hng : noGasStmts b = true) :
    noGasStmts r.block = true := by
  obtain ⟨_, hfacts⟩ := spillBlock_facts h
  rw [hfacts.block_eq]
  exact noGas_rewriteStmts r.layout.slots none [] (by simp [noGasStmts])
    (resolveMemoryGuardStmts r.base r.reserved b)
    (noGas_resolveStmts r.base r.reserved b hng)

end Lsc.Compiler
