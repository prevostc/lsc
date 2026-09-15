import Lsc.Compiler.Proof.Call
import Lsc.Lang.CoreTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Forward packing / suffix helpers for scoped `emitExtCall`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open Lsc hiding Op Stmt
open YulSemantics.EVM

/-! ## Body split -/

def mstoreArgs (d : Nat) : Nat → List Atom → List YStmt
  | _, [] => []
  | i, a :: as =>
    .exprStmt (bop YulSemantics.EVM.Op.mstore [lit (abiAfterSel + 32 * i), atomE tag d a]) ::
      mstoreArgs d (i + 1) as

theorem foldl_mstore_stmts (d : Nat) (args : List Atom) (e : Emit) (off : Nat) :
    (args.foldl (fun (e, i) a =>
        (emitDo e YulSemantics.EVM.Op.mstore
          [lit (abiAfterSel + 32 * i), atomE tag d a], i + 1))
      (e, off)).1.stmts =
      e.stmts ++ mstoreArgs tag d off args := by
  induction args generalizing e off with
  | nil => simp [List.foldl, mstoreArgs]
  | cons a as ih =>
    simp [List.foldl, mstoreArgs, emitDo_stmts, ih, bop]

private theorem emitExtCallBody_core_stmts (d : Nat) (sel : Nat) (args : List Atom) :
    let e0 := emitDo ({} : Emit) YulSemantics.EVM.Op.mstore
      [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]]
    (args.foldl (fun (e, i) a =>
        (emitDo e YulSemantics.EVM.Op.mstore
          [lit (abiAfterSel + 32 * i), atomE tag d a], i + 1)) (e0, 0)).1.stmts =
      [.exprStmt (bop YulSemantics.EVM.Op.mstore
        [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]])] ++
      mstoreArgs tag d 0 args := by
  simp [foldl_mstore_stmts, emitDo_stmts, Emit.stmts_nil, bop]

/-- Skip `iszero(ok)` revert iff this is a `view` of `AbiRet.none` (`Tx.viewAsNat
.none` is total). -/
def skipOkGuard (isView : Bool) (ret : AbiRet) : Bool :=
  isView && decide (ret = .none)

def callOkGuard (d : Nat) (isView : Bool) (ret : AbiRet) : List YStmt :=
  if skipOkGuard isView ret then []
  else [.cond (bop EVM.Op.iszero [var (extOk tag d)]) [revert00]]

theorem emitExtCallBody_stmts (d : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (assign : Option YIdent) :
    emitExtCallBody tag d target sel args ret isView assign =
      [.exprStmt (bop YulSemantics.EVM.Op.mstore
        [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]])] ++
      mstoreArgs tag d 0 args ++
      [.letDecl [extOk tag d] (some (emitExtCallOp isView (atomE tag d target)
          (4 + 32 * args.length)))] ++
      callOkGuard tag d isView ret ++
      (match ret with
        | .boolOpt =>
          [.cond
            (bop YulSemantics.EVM.Op.iszero
              [bop YulSemantics.EVM.Op.or
                [bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.returndatasize []],
                  bop YulSemantics.EVM.Op.and
                    [bop YulSemantics.EVM.Op.iszero
                      [bop YulSemantics.EVM.Op.lt
                        [bop YulSemantics.EVM.Op.returndatasize [], lit 32]],
                      bop YulSemantics.EVM.Op.lt
                        [bop YulSemantics.EVM.Op.returndatasize [], lit 64]]]])
            [revert00]]
        | .word =>
          [.cond
            (bop YulSemantics.EVM.Op.iszero
              [bop YulSemantics.EVM.Op.and
                [bop YulSemantics.EVM.Op.iszero
                  [bop YulSemantics.EVM.Op.lt
                    [bop YulSemantics.EVM.Op.returndatasize [], lit 32]],
                  bop YulSemantics.EVM.Op.lt
                    [bop YulSemantics.EVM.Op.returndatasize [], lit 64]]])
            [revert00]]
        | .none => []) ++
      (match assign with
        | none => []
        | some name => [.assign [name] (emitCallRetVal ret)]) := by
  dsimp [emitExtCallBody, callOkGuard, skipOkGuard]
  cases isView <;> cases assign <;> cases ret <;>
    simp [emitCallRetCheck_boolOpt_stmts, emitCallRetCheck_word_stmts,
      emitCallRetCheck_none_stmts, emitIf_stmts, emitLet_stmts, emitAssign_stmts,
      emitExtCallBody_core_stmts]

def callPrefix (d : Nat) (sel : Nat) (args : List Atom) : List YStmt :=
  [.exprStmt (bop EVM.Op.mstore [lit abiPtr, bop EVM.Op.shl [lit 224, lit sel]])] ++
  mstoreArgs tag d 0 args

def callLetOk (d : Nat) (target : Atom) (args : List Atom) (isView : Bool) : YStmt :=
  .letDecl [extOk tag d] (some (emitExtCallOp isView (atomE tag d target)
    (4 + 32 * args.length)))

def callRetCheck (ret : AbiRet) : List YStmt :=
  match ret with
  | .boolOpt =>
    [.cond
      (bop EVM.Op.iszero
        [bop EVM.Op.or
          [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
            bop EVM.Op.and
              [bop EVM.Op.iszero
                [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
                bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]]])
      [revert00]]
  | .word =>
    [.cond
      (bop EVM.Op.iszero
        [bop EVM.Op.and
          [bop EVM.Op.iszero
            [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
            bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]])
      [revert00]]
  | .none => []

def callAssign (ret : AbiRet) (name : YIdent) : List YStmt :=
  [.assign [name] (emitCallRetVal ret)]

def callSuffix (d : Nat) (ret : AbiRet) (isView : Bool) (assign : Option YIdent) :
    List YStmt :=
  callOkGuard tag d isView ret ++
    callRetCheck ret ++
    match assign with
    | none => []
    | some name => callAssign ret name

theorem emitExtCallBody_split (d : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (assign : Option YIdent) :
    emitExtCallBody tag d target sel args ret isView assign =
      callPrefix tag d sel args ++ [callLetOk tag d target args isView] ++
        callSuffix tag d ret isView assign := by
  simp [emitExtCallBody_stmts, callPrefix, callLetOk, callSuffix, callRetCheck,
    callAssign, emitCallRetVal, List.append_assoc]

theorem mstoreArgs_all_notFunDef (d off : Nat) (args : List Atom) :
    (mstoreArgs tag d off args).all notFunDef = true := by
  induction args generalizing off with
  | nil => rfl
  | cons _ as ih => simp [mstoreArgs, notFunDef, ih]

theorem notFunDef_emitExtCallBody (d : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool) (assign : Option YIdent) :
    ∀ s ∈ emitExtCallBody tag d target sel args ret isView assign, notFunDef s = true := by
  intro s hs
  have hall : (emitExtCallBody tag d target sel args ret isView assign).all notFunDef = true := by
    rw [emitExtCallBody_stmts]
    cases assign <;> cases ret <;> cases isView <;>
      simp [notFunDef, mstoreArgs_all_notFunDef, emitExtCallOp, callOkGuard, skipOkGuard]
  exact (List.all_eq_true.mp hall) s hs

theorem hoist_emitExtCallBody {calls : ExternalCalls} (d : Nat) (target : Atom)
    (sel : Nat) (args : List Atom) (ret : AbiRet) (isView : Bool)
    (assign : Option YIdent) :
    hoist (yulD calls) (emitExtCallBody tag d target sel args ret isView assign) = [] :=
  hoist_nil_open (notFunDef_emitExtCallBody tag d target sel args ret isView assign)

theorem emitLetOp_call_stmts (d : Nat) (t : Atom) (sel : Nat) (args : List Atom)
    (ret : AbiRet) :
    ((emitLetOp tag ({} : ContractDef) {} d (.call t sel args ret)).getD {}).stmts =
      [.letDecl [identV tag d] (some (lit 0)),
        .block (emitExtCallBody tag d t sel args ret false (some (identV tag d)))] := by
  simp [emitLetOp_call, emitExtCall_stmts, Emit.stmts_nil]

theorem emitLetOp_view_stmts (d : Nat) (t : Atom) (sel : Nat) (args : List Atom)
    (ret : AbiRet) :
    ((emitLetOp tag ({} : ContractDef) {} d (.view t sel args ret)).getD {}).stmts =
      [.letDecl [identV tag d] (some (lit 0)),
        .block (emitExtCallBody tag d t sel args ret true (some (identV tag d)))] := by
  simp [emitLetOp_view, emitExtCall_stmts, Emit.stmts_nil]

theorem emitStmt_call_stmts (c : ContractDef) (d : Nat) (t : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) :
    (emitStmt tag c {} d (.call t sel args ret)).stmts =
      [.block (emitExtCallBody tag d t sel args ret false none)] := by
  simp [emitStmt_call, emitExtCall_stmts, Emit.stmts_nil]

theorem emitStmt_view_stmts (c : ContractDef) (d : Nat) (t : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) :
    (emitStmt tag c {} d (.view t sel args ret)).stmts =
      [.block (emitExtCallBody tag d t sel args ret true none)] := by
  simp [emitStmt_view, emitExtCall_stmts, Emit.stmts_nil]

/-! ## Binding / packing facts -/

theorem exec_let_lit_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : YIdent} {k : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st (.letDecl [n] (some (lit k))) V' st' o) :
    o = .normal ∧ st' = st ∧ V' = (n, BitVec.ofNat 256 k) :: V := by
  cases h with
  | letVal he hlen =>
    have hr := eval_lit_unique he
    injection hr with hvs hst
    subst hvs; subst hst
    exact ⟨rfl, rfl, rfl⟩
  | letHalt he =>
    have hr := eval_lit_unique he
    injection hr

theorem insize_lt_of_arity {n : Nat} (h : n ≤ 3) : 4 + 32 * n < wordBound :=
  lt_256_wordBound (by omega)

theorem toNat_abiAfterSel_off {i : Nat} (hi : i ≤ 3) :
    (BitVec.ofNat 256 (abiAfterSel + 32 * i)).toNat = abiAfterSel + 32 * i :=
  toNat_ofNat_of_lt (lt_256_wordBound (by simp [abiAfterSel]; omega))

theorem toNat_insize {n : Nat} (h : n ≤ 3) :
    (BitVec.ofNat 256 (4 + 32 * n)).toNat = 4 + 32 * n :=
  toNat_ofNat_of_lt (insize_lt_of_arity h)

theorem wordBytes_inj {a b : Nat} (ha : a < wordBound) (hb : b < wordBound)
    (h : wordBytes a = wordBytes b) : a = b := by
  have := congrArg (fun l => wordFrom l 0) h
  rw [wordFrom_wordBytes a ha, wordFrom_wordBytes b hb] at this
  have := congrArg BitVec.toNat this
  rwa [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb] at this

/-! ## `noExt` of P / S -/

theorem noExt_mstoreArgs (d off : Nat) (args : List Atom) :
    noExtBlock (mstoreArgs tag d off args) = true := by
  induction args generalizing off with
  | nil => simp [mstoreArgs]
  | cons a as ih =>
    simp [mstoreArgs, noExtBlock, noExtStmt]
    refine ⟨noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_atomE]), ?_⟩
    simpa [noExtBlock] using ih (off + 1)

theorem noExt_callPrefix (d : Nat) (sel : Nat) (args : List Atom) :
    noExtBlock (callPrefix tag d sel args) = true := by
  unfold callPrefix
  refine noExtBlock_append ?_ (noExt_mstoreArgs tag d 0 args)
  simp [noExtBlock, noExtStmt]
  exact noExt_bop rfl (by
    simp [noExtExprs, noExt_lit]
    exact noExt_bop rfl (by simp [noExtExprs, noExt_lit]))

theorem noExt_rds : noExtExpr (bop EVM.Op.returndatasize []) = true :=
  noExt_bop rfl noExtExprs_nil

theorem noExt_callRetCheck (ret : AbiRet) : noExtBlock (callRetCheck ret) = true := by
  cases ret with
  | none => simp [callRetCheck]
  | word =>
    simp [callRetCheck, noExtBlock, noExtStmt]
    refine ⟨?_, noExt_revert00⟩
    exact noExt_bop rfl (by
      simp [noExtExprs]
      exact noExt_bop rfl (by
        simp [noExtExprs]
        refine ⟨noExt_bop rfl (by
            simp [noExtExprs]
            exact noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_rds])),
          noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_rds])⟩))
  | boolOpt =>
    simp [callRetCheck, noExtBlock, noExtStmt]
    refine ⟨?_, noExt_revert00⟩
    exact noExt_bop rfl (by
      simp [noExtExprs]
      exact noExt_bop rfl (by
        simp [noExtExprs]
        refine ⟨noExt_bop rfl (by simp [noExtExprs, noExt_rds]), ?_⟩
        exact noExt_bop rfl (by
          simp [noExtExprs]
          exact ⟨noExt_bop rfl (by
              simp [noExtExprs]
              exact noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_rds])),
            noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_rds])⟩)))

theorem noExt_callAssign (ret : AbiRet) (name : YIdent) :
    noExtBlock (callAssign ret name) = true := by
  cases ret with
  | word =>
    simp [callAssign, emitCallRetVal, noExtBlock, noExtStmt]
    exact noExt_bop rfl (by simp [noExtExprs, noExt_lit])
  | none =>
    simp [callAssign, emitCallRetVal, noExtBlock, noExtStmt, noExt_lit]
  | boolOpt =>
    simp [callAssign, emitCallRetVal, noExtBlock, noExtStmt]
    exact noExt_bop rfl (by
      simp [noExtExprs]
      refine ⟨noExt_bop rfl (by simp [noExtExprs, noExt_rds]),
        noExt_bop rfl (by
          simp [noExtExprs]
          exact noExt_bop rfl (by
            simp [noExtExprs]
            exact noExt_bop rfl (by simp [noExtExprs, noExt_lit])))⟩)

theorem noExt_callOkGuard (d : Nat) (isView : Bool) (ret : AbiRet) :
    noExtBlock (callOkGuard tag d isView ret) = true := by
  unfold callOkGuard skipOkGuard
  cases isView <;> cases ret <;>
    simp [noExtBlock, noExtStmt, noExtExprs, noExt_var, noExt_revert00]
  all_goals exact noExt_bop rfl (by simp [noExtExprs, noExt_var])

theorem noExt_callSuffix (d : Nat) (ret : AbiRet) (isView : Bool) (assign : Option YIdent) :
    noExtBlock (callSuffix tag d ret isView assign) = true := by
  unfold callSuffix
  refine noExtBlock_append (noExtBlock_append (noExt_callOkGuard tag d isView ret)
      (noExt_callRetCheck ret)) ?_
  · cases assign with
    | none => simp [noExtBlock]
    | some name => exact noExt_callAssign ret name

/-! ## Prefix evaluation -/

/-- Atom evaluation from `localsOK` (`Stmt.call` / `Op.call` after `let dest`). -/
theorem eval_atom_pre (funs : FunEnv evm) {env : List Nat} {V : VEnv evm} (st : EvmState)
    (hok : localsOK tag env V) (a : Atom) :
    EvalExpr evm funs V st (atomE tag env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) :=
  eval_atom_ok tag funs st hok a

theorem VEnv.get_cons_open {D : Dialect} {x : Ident} {v : D.Value}
    {V : VEnv D} {y : Ident} :
    VEnv.get ((x, v) :: V) y = if x = y then some v else VEnv.get V y := by
  simp only [VEnv.get, List.find?]
  by_cases h : x = y <;> simp [h]

/-- `atomE` is a literal or a `localsOK` variable, so its value is unique on `yulD`. -/
theorem eval_atomE_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState} {a : Atom} {r}
    (hok : localsOK tag env V)
    (h : EvalExpr (yulD calls) funs V st (atomE tag env.length a) r) :
    r = .vals [BitVec.ofNat 256 (a.eval env)] st := by
  cases a with
  | lit n =>
    simpa [atomE, Atom.eval] using eval_lit_unique h
  | var i =>
    simp only [atomE] at h
    split_ifs at h with hi
    · have heval : Atom.eval env (.var i) = env[i] := by
        simp [Atom.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have hget := hok i hi
      have := eval_var_unique hget h
      simpa [heval] using this
    · have : Atom.eval env (.var i) = 0 := by
        simp [Atom.eval, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      simpa [this] using eval_lit_unique h

theorem CallWorld.ofState_touch (st : EvmState) (p n : Nat) :
    CallWorld.ofState (touchMemory st p n) = CallWorld.ofState st := by
  simp [CallWorld.ofState, touchMemory]

theorem memOnly_mstore_nat (st : EvmState) (p : Nat) (v : U256)
    (hp : (BitVec.ofNat 256 p).toNat = p) :
    MemOnly st { touchMemory st p 32 with memory := storeWord st.memory p v } := by
  convert memOnly_mstore st (BitVec.ofNat 256 p) v <;> rw [hp]

theorem eval_mstore_sel_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (sel : Nat) :
    EvalExpr evm funs V st
      (bop EVM.Op.mstore [lit abiPtr, bop EVM.Op.shl [lit 224, lit sel]])
      (.vals []
        { touchMemory st abiPtr 32 with
          memory := storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) }) := by
  have hshl :
      EvalExpr evm funs V st (bop EVM.Op.shl [lit 224, lit sel])
        (.vals [BitVec.ofNat 256 sel <<< 224] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
      (by simp only [litValue_number, step_shl, toNat_224])
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hshl) Step.lit) ?_
  simp only [litValue_number, step_mstore, toNat_abiPtr]

theorem eval_mstore_atom_fwd (funs : FunEnv evm) {env : List Nat} {V : VEnv evm}
    (st : EvmState) (i : Nat) (a : Atom)
    (hok : localsOK tag env V)
    (hi : i ≤ 3) :
    EvalExpr evm funs V st
      (bop EVM.Op.mstore [lit (abiAfterSel + 32 * i), atomE tag env.length a])
      (.vals []
        { touchMemory st (abiAfterSel + 32 * i) 32 with
          memory := storeWord st.memory (abiAfterSel + 32 * i)
            (BitVec.ofNat 256 (a.eval env)) }) := by
  have ha := eval_atom_pre tag funs st hok a
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil ha) Step.lit) ?_
  simp only [litValue_number, step_mstore, toNat_abiAfterSel_off hi]

/-! ## (1) `call_prefix_fwd` -/

/-- Selector `mstore` at `abiPtr` (no `sload`; the target is an atom). -/
theorem call_prefix_fwd_nil (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (sel : Nat) (hsel : sel < 2 ^ 32) {ctx : Ctx} (hctx : ctxRel ctx st) :
    ∃ st',
      ExecStmts evm funs V st (callPrefix tag 0 sel []) V st' .normal ∧
      readBytes st'.memory abiPtr 4 = selectorBytes sel ∧
      MemOnly st st' ∧
      st'.env.static = false ∧
      st'.memory = storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) ∧
      CallWorld.ofState st' = CallWorld.ofState st ∧
      ExtView.ofState st' = ExtView.ofState st := by
  have hstatic0 : st.env.static = false := by
    rcases hctx with ⟨_, _, _, _, _, hs, _⟩
    exact hs
  have hmSel := eval_mstore_sel_fwd funs V st sel
  let stSel : EvmState :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) }
  have hdoSel :
      ExecStmt evm funs V st
        (.exprStmt (bop EVM.Op.mstore
          [lit abiPtr, bop EVM.Op.shl [lit 224, lit sel]]))
        V stSel .normal :=
    Step.exprStmt hmSel
  have hMO_sel : MemOnly st stSel := by
    simpa [stSel] using memOnly_mstore_nat st abiPtr
      (BitVec.ofNat 256 sel <<< 224) toNat_abiPtr
  refine ⟨stSel, ?_, ?_, hMO_sel, ?_, rfl, ?_, ?_⟩
  · simp [callPrefix, mstoreArgs]
    exact Step.seqCons hdoSel Step.seqNil
  · simpa [stSel] using readBytes_pack0 st.memory sel hsel
  · rcases hMO_sel with ⟨_, _, _, _, _, _, _, hs, _, _, _⟩
    exact hs.trans hstatic0
  · simp [stSel, CallWorld.ofState, touchMemory]
  · simpa [stSel] using ExtView.ofState_mstore st abiPtr (BitVec.ofNat 256 sel <<< 224)

theorem callPrefix_append (d : Nat) (sel : Nat) (args : List Atom) :
    callPrefix tag d sel args = callPrefix tag d sel [] ++ mstoreArgs tag d 0 args := by
  simp [callPrefix, mstoreArgs]

/-- Pack remaining `args` at ABI offset `off` into a memory that already holds `pre`. -/
theorem mstoreArgs_exec_from {env : List Nat} {V : VEnv evm}
    (funs : FunEnv evm) (st : EvmState) (off : Nat) (args : List Atom)
    (hok : localsOK tag env V)
    (hoff : off + args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true) (hwf : EnvWF env)
    {pre : List UInt8}
    (hpre : readBytes st.memory abiPtr (4 + 32 * off) = pre) :
    ∃ st',
      ExecStmts evm funs V st (mstoreArgs tag env.length off args) V st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * (off + args.length)) =
        pre ++ args.flatMap (fun a => wordBytes (a.eval env)) ∧
      MemOnly st st' ∧
      CallWorld.ofState st' = CallWorld.ofState st ∧
      ExtView.ofState st' = ExtView.ofState st := by
  induction args generalizing st off pre with
  | nil =>
    refine ⟨st, ?_, ?_, ?_, rfl, rfl⟩
    · simp [mstoreArgs]; exact Step.seqNil
    · simpa using hpre
    · simp [MemOnly]
  | cons a rest ih =>
    have hi : off ≤ 3 := Nat.le_trans (Nat.le_add_right off (a :: rest).length) hoff
    have haLt := atom_eval_lt hwf (hvals a (by simp))
    have hmA := eval_mstore_atom_fwd tag funs st off a hok hi
    let stA : EvmState :=
      { touchMemory st (abiAfterSel + 32 * off) 32 with
        memory := storeWord st.memory (abiAfterSel + 32 * off)
          (BitVec.ofNat 256 (a.eval env)) }
    have hdoA : ExecStmt evm funs V st
        (.exprStmt (bop EVM.Op.mstore
          [lit (abiAfterSel + 32 * off), atomE tag env.length a]))
        V stA .normal :=
      Step.exprStmt hmA
    have hpreA : readBytes stA.memory abiPtr (4 + 32 * (off + 1)) =
        pre ++ wordBytes (a.eval env) := by
      simpa [stA] using readBytes_pack_snoc st.memory off (a.eval env) haLt hpre
    have hoff' : off + 1 + rest.length ≤ 3 := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hoff
    obtain ⟨st', hrest, hpack, hMO, hCW, hEV⟩ :=
      ih (st := stA) (off := off + 1) (pre := pre ++ wordBytes (a.eval env))
        hoff' (fun x hx => hvals x (List.mem_cons_of_mem a hx)) hpreA
    refine ⟨st', ?_, ?_, ?_, ?_, ?_⟩
    · simp [mstoreArgs]
      exact Step.seqCons hdoA hrest
    · have hlen : 4 + 32 * (off + (a :: rest).length) =
          4 + 32 * (off + 1 + rest.length) := by simp [List.length_cons]; omega
      rw [hlen]
      simpa [List.append_assoc] using hpack
    · have hMOA : MemOnly st stA := by
        simpa [stA] using
          memOnly_mstore_nat st (abiAfterSel + 32 * off)
            (BitVec.ofNat 256 (a.eval env)) (toNat_abiAfterSel_off hi)
      exact MemOnly.trans hMOA hMO
    · simpa [stA, CallWorld.ofState, touchMemory] using hCW
    · have hEVA : ExtView.ofState stA = ExtView.ofState st := by
        simpa [stA] using
          ExtView.ofState_mstore st (abiAfterSel + 32 * off)
            (BitVec.ofNat 256 (a.eval env))
      exact hEV.trans hEVA

/-- Pack `args` (arity ≤ 3) into memory that already holds the 4-byte selector. -/
theorem mstoreArgs_exec {env : List Nat} {V : VEnv evm}
    (funs : FunEnv evm) (st : EvmState) (orig : Nat → UInt8)
    (sel : Nat) (args : List Atom)
    (hok : localsOK tag env V)
    (hn3 : args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true) (hwf : EnvWF env)
    (hsel : sel < 2 ^ 32)
    (hmem : st.memory = storeWord orig abiPtr (BitVec.ofNat 256 sel <<< 224)) :
    ∃ st',
      ExecStmts evm funs V st (mstoreArgs tag env.length 0 args) V st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * args.length) =
        selectorBytes sel ++ args.flatMap (fun a => wordBytes (a.eval env)) ∧
      MemOnly st st' ∧
      CallWorld.ofState st' = CallWorld.ofState st ∧
      ExtView.ofState st' = ExtView.ofState st := by
  have hpre : readBytes st.memory abiPtr 4 = selectorBytes sel := by
    simp [hmem]
    exact readBytes_pack0 orig sel hsel
  simpa using
    mstoreArgs_exec_from tag (env := env) (V := V)
      funs st 0 args hok (by simpa using hn3) hvals hwf hpre

/-- Combined prefix: selector word plus argument words. `d` is unused in the
statements (`callPrefix` uses `env.length` via `atomE`). -/
theorem call_prefix_fwd {env : List Nat} {V : VEnv evm} {st : EvmState} {ctx : Ctx}
    (funs : FunEnv evm) (sel : Nat) (args : List Atom)
    (hok : localsOK tag env V)
    (hctx : ctxRel ctx st) (hwf : EnvWF env)
    (hn3 : args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true)
    (hsel : sel < 2 ^ 32) :
    ∃ st',
      ExecStmts evm funs V st (callPrefix tag env.length sel args) V st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * args.length) =
        selectorBytes sel ++ args.flatMap (fun a => wordBytes (a.eval env)) ∧
      MemOnly st st' ∧
      st'.env.static = false ∧
      CallWorld.ofState st' = CallWorld.ofState st ∧
      ExtView.ofState st' = ExtView.ofState st := by
  obtain ⟨stSel, hP, _, hMO0, hstatic, hmem, hCW0, hEV0⟩ :=
    call_prefix_fwd_nil (tag := tag) funs V st sel hsel hctx
  obtain ⟨st', hM, hpack, hMO, hCW, hEV⟩ :=
    mstoreArgs_exec tag (env := env) (V := V) funs stSel st.memory sel args
      hok hn3 hvals hwf hsel hmem
  refine ⟨st', ?_, hpack, MemOnly.trans hMO0 hMO, ?_, hCW.trans hCW0, hEV.trans hEV0⟩
  · rw [callPrefix_append]
    have hP' : ExecStmts evm funs V st (callPrefix tag env.length sel []) V stSel .normal := by
      simpa [callPrefix, mstoreArgs] using hP
    exact execStmts_append hP' hM
  · rcases hMO with ⟨_, _, _, _, _, _, _, hs, _, _, _⟩
    exact hs.trans hstatic

def suffixVal (ret : AbiRet) (st : EvmState) : U256 :=
  match ret with
  | .word => loadWord st.memory abiPtr
  | .boolOpt =>
    b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
      b2w (loadWord st.memory abiPtr ≠ 0)
  | .none => 0

def wordRetPass (st : EvmState) : Bool :=
  decide ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&
    decide ((BitVec.ofNat 256 st.returndata.length).ult 64#256 = true)

def suffixOk (ok : U256) (ret : AbiRet) (st : EvmState) (checkOk : Bool := true) : Prop :=
  (checkOk = false ∨ ok ≠ 0) ∧
    match ret with
    | .none => True
    | .word => wordRetPass st = true
    | .boolOpt =>
        BitVec.ofNat 256 st.returndata.length = 0 ∨ wordRetPass st = true

def boolOptPass (st : EvmState) : Bool :=
  decide (BitVec.ofNat 256 st.returndata.length = 0) || wordRetPass st

theorem hoist_revert00 : hoist evm [revert00] = [] := by simp [hoist, revert00]

theorem revert00_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmts evm funs V st [revert00] V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.seqStop (Step.exprStmtHalt (Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) ?_))
    halt_ne_normal
  simp only [step_revert, litValue_number]
  simp [readBytes, toNat_ofNat_of_lt zero_lt_wordBound]

theorem exec_revert00_block (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmt evm funs V st (.block [revert00]) V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have inner :
      ExecStmts evm (hoist evm [revert00] :: funs) V st [revert00] V
        { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
    rw [hoist_revert00]
    exact revert00_exec _ _ _
  simpa [restore_self] using Step.block (D := evm) inner

theorem eval_iszero_var_fwd (funs : FunEnv evm) {V : VEnv evm} {st : EvmState}
    {x : YIdent} {v : U256} (hget : VEnv.get V x = some v) :
    EvalExpr evm funs V st (bop EVM.Op.iszero [var x])
      (.vals [b2w (v = 0)] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil (Step.var hget)) (by simp only [step_iszero])

theorem eval_rds_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st (bop EVM.Op.returndatasize [])
      (.vals [BitVec.ofNat 256 st.returndata.length] st) :=
  Step.builtinOk Step.argsNil (by simp only [step_returndatasize])

theorem eval_lt_rds32_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256)] st) :=
  Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (eval_rds_fwd funs V st))
    (by simp only [litValue_number, step_lt])

theorem eval_iszero_lt_rds32_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero
        [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false)] st) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_lt_rds32_fwd funs V st)) ?_
  simp only [step_iszero]
  rw [b2w_iszero]
  cases h : (BitVec.ofNat 256 st.returndata.length).ult 32#256 <;> simp [h, b2w]

theorem eval_iszero_rds_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero [bop EVM.Op.returndatasize []])
      (.vals [b2w (BitVec.ofNat 256 st.returndata.length = 0)] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil (eval_rds_fwd funs V st))
    (by simp only [step_iszero])

theorem eval_mload_abi_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st (bop EVM.Op.mload [lit abiPtr])
      (.vals [loadWord st.memory abiPtr] (touchMemory st abiPtr 32)) := by
  refine Step.builtinOk (Step.argsCons Step.argsNil Step.lit) ?_
  simp only [litValue_number, step_mload, toNat_abiPtr]

theorem eval_lt_rds64_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 64#256)] st) :=
  Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (eval_rds_fwd funs V st))
    (by simp only [litValue_number, step_lt])

theorem eval_word_and_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.and
        [bop EVM.Op.iszero
          [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
          bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&&
          b2w ((BitVec.ofNat 256 st.returndata.length).ult 64#256)] st) :=
  Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil (eval_lt_rds64_fwd funs V st))
      (eval_iszero_lt_rds32_fwd funs V st))
    (by simp only [step_and])

theorem wordAndVal (st : EvmState) :
    b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&&
      b2w ((BitVec.ofNat 256 st.returndata.length).ult 64#256) =
      b2w (wordRetPass st) := by
  have h32 :
      decide ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) =
        ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) := by
    cases (BitVec.ofNat 256 st.returndata.length).ult 32#256 <;> simp
  have h64 :
      decide ((BitVec.ofNat 256 st.returndata.length).ult 64#256 = true) =
        ((BitVec.ofNat 256 st.returndata.length).ult 64#256) := by
    cases (BitVec.ofNat 256 st.returndata.length).ult 64#256 <;> simp
  simp only [wordRetPass, b2w_and, h32, h64, Bool.and_eq_true]

theorem eval_word_cond_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero
        [bop EVM.Op.and
          [bop EVM.Op.iszero
            [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
            bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]])
      (.vals [b2w (!wordRetPass st)] st) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_word_and_fwd funs V st)) ?_
  simp only [step_iszero]
  rw [wordAndVal, b2w_iszero]

theorem eval_boolOpt_or_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.or
        [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
          bop EVM.Op.and
            [bop EVM.Op.iszero
              [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
              bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]])
      (.vals [b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
          b2w (wordRetPass st)] st) := by
  have hand := eval_word_and_fwd funs V st
  have hisz := eval_iszero_rds_fwd funs V st
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hand) hisz) ?_
  simp only [step_or]
  rw [wordAndVal]

theorem boolOpt_orVal (st : EvmState) :
    b2w (BitVec.ofNat 256 st.returndata.length = 0) ||| b2w (wordRetPass st) =
      b2w (boolOptPass st) := by
  simp [boolOptPass, b2w_or]

theorem eval_boolOpt_cond_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero
        [bop EVM.Op.or
          [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
            bop EVM.Op.and
              [bop EVM.Op.iszero
                [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
                bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]]])
      (.vals [b2w (!boolOptPass st)] st) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_boolOpt_or_fwd funs V st)) ?_
  simp only [step_iszero]
  rw [boolOpt_orVal, b2w_iszero]

theorem call_guard_fail (funs : FunEnv evm) {V : VEnv evm} {st : EvmState}
    {d : Nat} (hget : VEnv.get V (extOk tag d) = some 0) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.iszero [var (extOk tag d)]) [revert00])
      V { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.ifTrue (D := evm) (eval_iszero_var_fwd funs hget) ?_
    (exec_revert00_block funs V st)
  simp [b2w, Dialect.zero, litValue, litValue_number]

theorem call_guard_pass (funs : FunEnv evm) {V : VEnv evm} {st : EvmState}
    {d : Nat} {ok : U256} (hget : VEnv.get V (extOk tag d) = some ok)
    (hok : ok ≠ 0) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.iszero [var (extOk tag d)]) [revert00])
      V st .normal := by
  refine Step.ifFalse (eval_iszero_var_fwd funs hget) ?_
  simp [hok, b2w, Dialect.zero, litValue, litValue_number]
  exact hok

theorem word_check_fail (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : wordRetPass st = false) :
    ExecStmt evm funs V st
      (.cond
        (bop EVM.Op.iszero
          [bop EVM.Op.and
            [bop EVM.Op.iszero
              [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
              bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]])
        [revert00])
      V { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have hcv : b2w (!wordRetPass st) ≠ evm.zero := by
    simp [h, b2w, Dialect.zero, litValue, litValue_number]
  refine Step.ifTrue (D := evm) (eval_word_cond_fwd funs V st) hcv
    (exec_revert00_block funs V st)

theorem word_check_pass (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : wordRetPass st = true) :
    ExecStmt evm funs V st
      (.cond
        (bop EVM.Op.iszero
          [bop EVM.Op.and
            [bop EVM.Op.iszero
              [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
              bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]])
        [revert00])
      V st .normal := by
  refine Step.ifFalse (eval_word_cond_fwd funs V st) ?_
  simp [h, b2w, Dialect.zero, litValue, litValue_number]

theorem boolOpt_check_fail (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : boolOptPass st = false) :
    ExecStmt evm funs V st
      (.cond
        (bop EVM.Op.iszero
          [bop EVM.Op.or
            [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
              bop EVM.Op.and
                [bop EVM.Op.iszero
                  [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
                  bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]]])
        [revert00])
      V { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have hcv : b2w (!boolOptPass st) ≠ evm.zero := by
    simp [h, b2w, Dialect.zero, litValue, litValue_number]
  refine Step.ifTrue (D := evm) (eval_boolOpt_cond_fwd funs V st) hcv
    (exec_revert00_block funs V st)

theorem boolOpt_check_pass (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : boolOptPass st = true) :
    ExecStmt evm funs V st
      (.cond
        (bop EVM.Op.iszero
          [bop EVM.Op.or
            [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
              bop EVM.Op.and
                [bop EVM.Op.iszero
                  [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
                  bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 64]]]])
        [revert00])
      V st .normal := by
  refine Step.ifFalse (eval_boolOpt_cond_fwd funs V st) ?_
  simp [h, b2w, Dialect.zero, litValue, litValue_number]

theorem eval_iszero_mload_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero [bop EVM.Op.mload [lit abiPtr]])
      (.vals [b2w (loadWord st.memory abiPtr = 0)] (touchMemory st abiPtr 32)) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_mload_abi_fwd funs V st)) ?_
  simp only [step_iszero]

theorem eval_iszero_iszero_mload_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero [bop EVM.Op.iszero [bop EVM.Op.mload [lit abiPtr]]])
      (.vals [b2w (loadWord st.memory abiPtr ≠ 0)] (touchMemory st abiPtr 32)) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_iszero_mload_fwd funs V st)) ?_
  simp only [step_iszero]
  rw [b2w_iszero]
  apply congrArg (fun v => some (BuiltinResult.ok [v] (touchMemory st abiPtr 32)))
  simp [ne_eq, b2w_decide_not]

theorem eval_boolOpt_retVal_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st (emitCallRetVal .boolOpt)
      (.vals [b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
          b2w (loadWord st.memory abiPtr ≠ 0)]
        (touchMemory st abiPtr 32)) := by
  simp only [emitCallRetVal]
  have hm := eval_iszero_iszero_mload_fwd funs V st
  have hrds := eval_iszero_rds_fwd funs V (touchMemory st abiPtr 32)
  have hlen : (touchMemory st abiPtr 32).returndata.length = st.returndata.length := by
    simp [touchMemory]
  simp only [hlen] at hrds
  exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hm) hrds)
    (by simp only [step_or])

theorem callAssign_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (ret : AbiRet) (name : YIdent) :
    ExecStmts evm funs V st (callAssign ret name)
      (VEnv.set V name (suffixVal ret st))
      (match ret with
        | .word | .boolOpt => touchMemory st abiPtr 32
        | .none => st) .normal := by
  cases ret with
  | word =>
    simp [callAssign, emitCallRetVal, suffixVal]
    have h : ExecStmts evm funs V st
        [.assign [name] (bop EVM.Op.mload [lit abiPtr])]
        (VEnv.setMany V [name] [loadWord st.memory abiPtr])
        (touchMemory st abiPtr 32) .normal :=
      Step.seqCons (Step.assignVal (D := evm) (eval_mload_abi_fwd funs V st) rfl) Step.seqNil
    rwa [VEnv.setMany_one] at h
  | boolOpt =>
    simp only [callAssign, suffixVal]
    have h : ExecStmts evm funs V st
        [.assign [name] (emitCallRetVal .boolOpt)]
        (VEnv.setMany V [name]
          [b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
            b2w (loadWord st.memory abiPtr ≠ 0)])
        (touchMemory st abiPtr 32) .normal :=
      Step.seqCons (Step.assignVal (D := evm) (eval_boolOpt_retVal_fwd funs V st) rfl)
        Step.seqNil
    rwa [VEnv.setMany_one] at h
  | none =>
    simp [callAssign, emitCallRetVal, suffixVal]
    have he : EvalExpr evm funs V st (lit 0) (.vals [0#256] st) := Step.lit
    have h : ExecStmts evm funs V st [.assign [name] (lit 0)]
        (VEnv.setMany V [name] [0#256]) st .normal :=
      Step.seqCons (Step.assignVal (D := evm) he rfl) Step.seqNil
    rwa [VEnv.setMany_one] at h

theorem suffixOk_boolOpt {ok : U256} {st : EvmState} {ck : Bool}
    (hok : ok ≠ 0) : suffixOk ok .boolOpt st ck ↔ boolOptPass st = true := by
  constructor
  · intro h
    have hp := h.2
    simp [boolOptPass, suffixOk] at hp ⊢
    cases hp with
    | inl h0 => simp [h0]
    | inr hrest => simp [hrest]
  · intro h
    refine ⟨Or.inr hok, ?_⟩
    unfold boolOptPass at h
    rcases Bool.or_eq_true_iff.mp h with h0 | hrest
    · exact .inl (of_decide_eq_true h0)
    · exact .inr hrest

theorem ult32_of_ge {n : Nat} (hn : n < wordBound) (h : 32 ≤ n) :
    (BitVec.ofNat 256 n).ult 32#256 = false := by
  have h32 : (32 : Nat) < wordBound := lt_256_wordBound (by decide)
  rw [ult_ofNat hn h32]
  simp [Nat.not_lt.mpr h]

theorem ult64_of_lt {n : Nat} (hn : n < wordBound) (h : n < 64) :
    (BitVec.ofNat 256 n).ult 64#256 = true := by
  have h64 : (64 : Nat) < wordBound := lt_256_wordBound (by decide)
  rw [ult_ofNat hn h64]
  simpa

theorem ofNat_length_rds (bs : List UInt8) :
    BitVec.ofNat 256 bs.length = BitVec.ofNat 256 (rdsNat bs) := by
  simp only [rdsNat]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

theorem wordRetPass_iff (st : EvmState) :
    wordRetPass st = true ↔
      32 ≤ rdsNat st.returndata ∧ rdsNat st.returndata < 64 := by
  have hr : rdsNat st.returndata < wordBound := (BitVec.ofNat 256 _).isLt
  have h32 : (32 : Nat) < wordBound := lt_256_wordBound (by decide)
  have h64 : (64 : Nat) < wordBound := lt_256_wordBound (by decide)
  simp only [wordRetPass]
  rw [ofNat_length_rds st.returndata, ult_ofNat hr h32, ult_ofNat hr h64]
  simp [Bool.and_eq_true, decide_eq_true_eq, Nat.not_lt]

theorem wordRetPass_of {st : EvmState}
    (h32 : 32 ≤ rdsNat st.returndata) (h64 : rdsNat st.returndata < 64) :
    wordRetPass st = true :=
  (wordRetPass_iff st).mpr ⟨h32, h64⟩

theorem decodeRet_suffixOk {ok : U256} {ret : AbiRet} {st : EvmState} {v : Nat}
    (hok : ok ≠ 0) (h : decodeRet ret st.returndata v) :
    suffixOk ok ret st := by
  refine ⟨Or.inr hok, ?_⟩
  cases ret with
  | none => trivial
  | word =>
    exact wordRetPass_of h.1 h.2.1
  | boolOpt =>
    cases h with
    | inl h0 =>
      exact .inl (by
        have : rdsNat st.returndata = 0 := h0.1
        rw [ofNat_length_rds, this]
        simp)
    | inr hrest => exact .inr (wordRetPass_of hrest.1 hrest.2.1)

/-- Forward suffix: revert on `ok = 0` (unless `view`+`.none`) or a failed ABI
check; otherwise assign the Core word. -/
theorem call_suffix_fwd (funs : FunEnv evm) {d : Nat} {ok : U256}
    {ret : AbiRet} {isView : Bool} {assign : Option YIdent}
    {V : VEnv evm} {st : EvmState}
    (hget : VEnv.get V (extOk tag d) = some ok) :
    ∃ V' st' o,
      ExecStmts evm funs V st (callSuffix tag d ret isView assign) V' st' o ∧
      (suffixOk ok ret st (!skipOkGuard isView ret) →
        o = .normal ∧ MemOnly st st' ∧
          ExtView.ofState st' = ExtView.ofState st ∧
          V' = match assign with
            | none => V
            | some name => VEnv.set V name (suffixVal ret st)) ∧
      (¬ suffixOk ok ret st (!skipOkGuard isView ret) →
        o = .halt ∧ V' = V ∧ st'.halted = some (.revert, [])) ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  unfold callSuffix
  by_cases hskip : skipOkGuard isView ret = true
  · have hnone : ret = .none := by
      revert hskip; unfold skipOkGuard; cases isView <;> cases ret <;> simp
    subst hnone
    have hview : isView = true := by
      simpa [skipOkGuard] using hskip
    subst hview
    cases assign with
    | none =>
      refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
      · simp [callOkGuard, skipOkGuard, callRetCheck]
        exact Step.seqNil (D := evm)
      · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
      · intro hS; exact (hS ⟨Or.inl rfl, trivial⟩).elim
    | some name =>
      have hasn := callAssign_exec funs V st .none name
      refine ⟨VEnv.set V name (suffixVal .none st), st, .normal, ?_, ?_, ?_, rfl⟩
      · simp [callOkGuard, skipOkGuard, callRetCheck]
        exact hasn
      · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
      · intro hS; exact (hS ⟨Or.inl rfl, trivial⟩).elim
  · have hguardOk : skipOkGuard isView ret = false := by simpa using hskip
    by_cases hok : ok = 0
    · subst hok
      refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt, ?_, ?_, ?_, ?_⟩
      · simp [callOkGuard, hguardOk]
        exact Step.seqStop (call_guard_fail tag funs hget) halt_ne_normal
      · intro hS
        have : (0 : U256) ≠ 0 := by
          cases hS.1 with
          | inl h => simp [hguardOk] at h
          | inr h => exact h
        exact (this rfl).elim
      · intro; exact ⟨rfl, rfl, rfl⟩
      · simp [CallWorld.ofState, touchMemory]
    · have hguard := call_guard_pass (tag := tag) (st := st) funs hget hok
      cases ret with
      | none =>
        cases assign with
        | none =>
          refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
          · simp [callOkGuard, hguardOk, callRetCheck]
            exact Step.seqCons hguard (Step.seqNil (D := evm))
          · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
          · intro hS; exact (hS ⟨Or.inr hok, trivial⟩).elim
        | some name =>
          have hasn := callAssign_exec funs V st .none name
          refine ⟨VEnv.set V name (suffixVal .none st), st, .normal, ?_, ?_, ?_, rfl⟩
          · simp [callOkGuard, hguardOk, callRetCheck]
            exact Step.seqCons hguard hasn
          · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
          · intro hS; exact (hS ⟨Or.inr hok, trivial⟩).elim
      | word =>
        by_cases hp : wordRetPass st = true
        · have hchk := word_check_pass funs V st hp
          cases assign with
          | none =>
            refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
            · simp [callOkGuard, hguardOk, callRetCheck]
              exact Step.seqCons hguard (Step.seqCons hchk (Step.seqNil (D := evm)))
            · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
            · intro hS; exact (hS ⟨Or.inr hok, hp⟩).elim
          | some name =>
            have hasn := callAssign_exec funs V st .word name
            refine ⟨VEnv.set V name (loadWord st.memory abiPtr),
              touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
              by simp [CallWorld.ofState, touchMemory]⟩
            · simp [callOkGuard, hguardOk, callRetCheck]
              exact Step.seqCons hguard (Step.seqCons hchk hasn)
            · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, ExtView.ofState_touch st abiPtr 32,
                by simp [suffixVal]⟩
            · intro hS; exact (hS ⟨Or.inr hok, hp⟩).elim
        · have hfail : wordRetPass st = false := by simpa using hp
          refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt,
            ?_, ?_, ?_, by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callOkGuard, hguardOk, callRetCheck]
            exact Step.seqCons hguard
              (Step.seqStop (word_check_fail funs V st hfail) halt_ne_normal)
          · intro hS; simp [suffixOk, hok, hfail] at hS
          · intro; exact ⟨rfl, rfl, rfl⟩
      | boolOpt =>
        by_cases hp : boolOptPass st = true
        · have hchk := boolOpt_check_pass funs V st hp
          cases assign with
          | none =>
            refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
            · simp [callOkGuard, hguardOk, callRetCheck]
              exact Step.seqCons hguard (Step.seqCons hchk (Step.seqNil (D := evm)))
            · intro; exact ⟨rfl, by simp [MemOnly], rfl, rfl⟩
            · intro hS
              exact (hS ((suffixOk_boolOpt hok).mpr hp)).elim
          | some name =>
            have hasn := callAssign_exec funs V st .boolOpt name
            refine ⟨VEnv.set V name (suffixVal .boolOpt st),
              touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
              by simp [CallWorld.ofState, touchMemory]⟩
            · simp [callOkGuard, hguardOk, callRetCheck]
              exact Step.seqCons hguard (Step.seqCons hchk hasn)
            · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, ExtView.ofState_touch st abiPtr 32, rfl⟩
            · intro hS
              exact (hS ((suffixOk_boolOpt hok).mpr hp)).elim
        · have hfail : boolOptPass st = false := by simpa using hp
          refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt,
            ?_, ?_, ?_, by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callOkGuard, hguardOk, callRetCheck]
            exact Step.seqCons hguard
              (Step.seqStop (boolOpt_check_fail funs V st hfail) halt_ne_normal)
          · intro hS
            have : boolOptPass st = true := (suffixOk_boolOpt hok).mp hS
            simp [hfail] at this
          · intro; exact ⟨rfl, rfl, rfl⟩

theorem R_with_ext {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} (ext' : X)
    (h : R c Γ κ w st) :
    R c Γ κ { w with ext := ext' } st := by
  rcases h with ⟨hs, hl, hk, hwf⟩
  exact ⟨hs, hl, hk, hwf⟩

theorem abiArgs_inj {sel : Nat} {xs ys : List Nat}
    (hsel : sel < 2 ^ 32)
    (hx : ∀ x ∈ xs, x < wordBound) (hy : ∀ y ∈ ys, y < wordBound)
    (hlen : xs.length = ys.length) (hn : xs.length ≤ 3)
    (h : selectorBytes sel ++ xs.flatMap wordBytes =
         selectorBytes sel ++ ys.flatMap wordBytes) :
    xs = ys := by
  have hflat : xs.flatMap wordBytes = ys.flatMap wordBytes :=
    (List.append_inj h (by simp [selectorBytes_length])).2
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a rest =>
    cases rest with
    | nil =>
      cases ys with
      | nil => simp at hlen
      | cons b resty =>
        cases resty with
        | nil =>
          have : wordBytes a = wordBytes b := by simpa [List.flatMap] using hflat
          congr 1
          exact wordBytes_inj (hx _ (by simp)) (hy _ (by simp)) this
        | cons _ _ => simp at hlen
    | cons a2 rest2 =>
      cases rest2 with
      | nil =>
        cases ys with
        | nil => simp at hlen
        | cons b resty =>
          cases resty with
          | nil => simp at hlen
          | cons b2 resty2 =>
            cases resty2 with
            | nil =>
              have ha := hx a (by simp)
              have ha2 := hx a2 (by simp)
              have hb := hy b (by simp)
              have hb2 := hy b2 (by simp)
              have h' : wordBytes a ++ wordBytes a2 = wordBytes b ++ wordBytes b2 := by
                simpa [List.flatMap] using hflat
              have ⟨heq1, heq2⟩ := List.append_inj h' (by simp [wordBytes_length])
              simp [wordBytes_inj ha hb heq1, wordBytes_inj ha2 hb2 heq2]
            | cons _ _ => simp at hlen
      | cons a3 rest3 =>
        cases rest3 with
        | nil =>
          cases ys with
          | nil => simp at hlen
          | cons b resty =>
            cases resty with
            | nil => simp at hlen
            | cons b2 resty2 =>
              cases resty2 with
              | nil => simp at hlen
              | cons b3 resty3 =>
                cases resty3 with
                | nil =>
                  have ha := hx a (by simp); have ha2 := hx a2 (by simp)
                  have ha3 := hx a3 (by simp)
                  have hb := hy b (by simp); have hb2 := hy b2 (by simp)
                  have hb3 := hy b3 (by simp)
                  have h' : wordBytes a ++ (wordBytes a2 ++ wordBytes a3) =
                            wordBytes b ++ (wordBytes b2 ++ wordBytes b3) := by
                    simpa [List.flatMap, List.append_assoc] using hflat
                  have ⟨heq1, hrest⟩ := List.append_inj h' (by simp [wordBytes_length])
                  have ⟨heq2, heq3⟩ := List.append_inj hrest (by simp [wordBytes_length])
                  simp [wordBytes_inj ha hb heq1, wordBytes_inj ha2 hb2 heq2,
                    wordBytes_inj ha3 hb3 heq3]
                | cons _ _ => simp at hlen
        | cons _ _ => simp at hn

theorem flag_eq_zero_iff (resp : CallResponse) :
    resp.flag = 0 ↔ resp.success = false := by
  simp [CallResponse.flag_of]

theorem flag_ne_zero_iff (resp : CallResponse) :
    resp.flag ≠ 0 ↔ resp.success = true := by
  simp [CallResponse.flag_of]

theorem execStmts_one {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {s : YulSemantics.Stmt D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmts D funs V st [s] V' st' o) :
    ExecStmt D funs V st s V' st' o := by
  cases execStmts_cons_inv h with
  | inl h =>
    obtain ⟨_, _, hs, hnil⟩ := h
    cases hnil
    exact hs
  | inr h => exact h.2

end Lsc.Compiler
