import Lsc.Compiler.Proof.Call
import Lsc.Lang.CoreProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Backward simulation of scoped `emitExtCall`.

The body is `P ++ [letOk] ++ S`. `call_prefix_fwd` / `call_suffix_fwd` are S1-style
forward lemmas in `evm` (call-free, deterministic); a `yulD` run is identified by
`execStmts_descend` + `execStmts_det_evm`. `call_step_inv` inverts the single CALL.
-/

namespace Lsc.Compiler

open YulSemantics
open Lsc hiding Op Stmt
open YulSemantics.EVM

/-! ## Body split -/

def mstoreArgs (d : Nat) : Nat → List Atom → List YStmt
  | _, [] => []
  | i, a :: as =>
    .exprStmt (bop YulSemantics.EVM.Op.mstore [lit (abiAfterSel + 32 * i), atomE d a]) ::
      mstoreArgs d (i + 1) as

theorem foldl_mstore_stmts (d : Nat) (args : List Atom) (e : Emit) (off : Nat) :
    (args.foldl (fun (e, i) a =>
        (emitDo e YulSemantics.EVM.Op.mstore
          [lit (abiAfterSel + 32 * i), atomE d a], i + 1))
      (e, off)).1.stmts =
      e.stmts ++ mstoreArgs d off args := by
  induction args generalizing e off with
  | nil => simp [List.foldl, mstoreArgs]
  | cons a as ih =>
    simp [List.foldl, mstoreArgs, emitDo_stmts, ih, bop]

private theorem emitExtCallBody_core_stmts (c : ContractDef) (d b m : Nat)
    (args : List Atom) :
    let tok := extTok d; let ok := extOk d
    let e0 := emitLet ({} : Emit) tok
      (bop YulSemantics.EVM.Op.sload [lit (bindingSlot c b)])
    let e1 := emitDo e0 YulSemantics.EVM.Op.mstore
      [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit (bindingMethod c b m).1]]
    (args.foldl (fun (e, i) a =>
        (emitDo e YulSemantics.EVM.Op.mstore
          [lit (abiAfterSel + 32 * i), atomE d a], i + 1)) (e1, 0)).1.stmts =
      [.letDecl [tok] (some (bop YulSemantics.EVM.Op.sload [lit (bindingSlot c b)])),
        .exprStmt (bop YulSemantics.EVM.Op.mstore
          [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit (bindingMethod c b m).1]])] ++
      mstoreArgs d 0 args := by
  simp [foldl_mstore_stmts, emitDo_stmts, emitLet_stmts, Emit.stmts_nil, bop]

theorem emitExtCallBody_stmts (c : ContractDef) (d b m : Nat)
    (args : List Atom) (assign : Option YIdent) :
    emitExtCallBody c d b m args assign =
      [.letDecl [extTok d] (some (bop YulSemantics.EVM.Op.sload [lit (bindingSlot c b)])),
        .exprStmt (bop YulSemantics.EVM.Op.mstore
          [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit (bindingMethod c b m).1]])] ++
      mstoreArgs d 0 args ++
      [.letDecl [extOk d] (some (bop YulSemantics.EVM.Op.call
          [lit extCallGas, var (extTok d), lit 0, lit abiPtr,
            lit (4 + 32 * args.length), lit abiPtr, lit 32])),
        .cond (bop YulSemantics.EVM.Op.iszero [var (extOk d)]) [revert00]] ++
      (match (bindingMethod c b m).2 with
        | .boolOpt =>
          [.cond
            (bop YulSemantics.EVM.Op.iszero
              [bop YulSemantics.EVM.Op.or
                [bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.returndatasize []],
                  bop YulSemantics.EVM.Op.and
                    [bop YulSemantics.EVM.Op.iszero
                      [bop YulSemantics.EVM.Op.lt
                        [bop YulSemantics.EVM.Op.returndatasize [], lit 32]],
                      bop YulSemantics.EVM.Op.eq
                        [bop YulSemantics.EVM.Op.mload [lit abiPtr], lit 1]]]])
            [revert00]]
        | .word =>
          [.cond (bop YulSemantics.EVM.Op.lt
            [bop YulSemantics.EVM.Op.returndatasize [], lit 32]) [revert00]]
        | .none => []) ++
      (match assign with
        | none => []
        | some name =>
          match (bindingMethod c b m).2 with
          | .word => [.assign [name] (bop YulSemantics.EVM.Op.mload [lit abiPtr])]
          | .boolOpt | .none => [.assign [name] (lit 1)]) := by
  dsimp [emitExtCallBody]
  cases assign with
  | none =>
    cases (bindingMethod c b m).2 with
    | boolOpt =>
      simp [emitCallRetCheck_boolOpt_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]
    | word =>
      simp [emitCallRetCheck_word_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]
    | none =>
      simp [emitCallRetCheck_none_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]
  | some name =>
    simp only []
    cases (bindingMethod c b m).2 with
    | boolOpt =>
      simp [emitAssign_stmts, emitCallRetCheck_boolOpt_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]
    | word =>
      simp [emitAssign_stmts, emitCallRetCheck_word_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]
    | none =>
      simp [emitAssign_stmts, emitCallRetCheck_none_stmts, emitIf_stmts, emitLet_stmts,
        emitExtCallBody_core_stmts]

def callPrefix (c : ContractDef) (d b m : Nat) (args : List Atom) : List YStmt :=
  [.letDecl [extTok d] (some (bop EVM.Op.sload [lit (bindingSlot c b)])),
    .exprStmt (bop EVM.Op.mstore [lit abiPtr, bop EVM.Op.shl [lit 224, lit (bindingMethod c b m).1]])] ++
  mstoreArgs d 0 args

def callLetOk (d : Nat) (args : List Atom) : YStmt :=
  .letDecl [extOk d] (some (bop EVM.Op.call
    [lit extCallGas, var (extTok d), lit 0, lit abiPtr,
      lit (4 + 32 * args.length), lit abiPtr, lit 32]))

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
                bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]]]])
      [revert00]]
  | .word =>
    [.cond (bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]) [revert00]]
  | .none => []

def callAssign (ret : AbiRet) (name : YIdent) : List YStmt :=
  match ret with
  | .word => [.assign [name] (bop EVM.Op.mload [lit abiPtr])]
  | .boolOpt | .none => [.assign [name] (lit 1)]

def callSuffix (d : Nat) (ret : AbiRet) (assign : Option YIdent) : List YStmt :=
  [.cond (bop EVM.Op.iszero [var (extOk d)]) [revert00]] ++
    callRetCheck ret ++
    match assign with
    | none => []
    | some name => callAssign ret name

theorem emitExtCallBody_split (c : ContractDef) (d b m : Nat)
    (args : List Atom) (assign : Option YIdent) :
    emitExtCallBody c d b m args assign =
      callPrefix c d b m args ++ [callLetOk d args] ++
        callSuffix d (bindingMethod c b m).2 assign := by
  simp [emitExtCallBody_stmts, callPrefix, callLetOk, callSuffix, callRetCheck,
    callAssign, List.append_assoc]

theorem mstoreArgs_all_notFunDef (d off : Nat) (args : List Atom) :
    (mstoreArgs d off args).all notFunDef = true := by
  induction args generalizing off with
  | nil => rfl
  | cons _ as ih => simp [mstoreArgs, notFunDef, ih]

theorem notFunDef_emitExtCallBody (c : ContractDef) (d b m : Nat) (args : List Atom)
    (assign : Option YIdent) :
    ∀ s ∈ emitExtCallBody c d b m args assign, notFunDef s = true := by
  intro s hs
  have hall : (emitExtCallBody c d b m args assign).all notFunDef = true := by
    rw [emitExtCallBody_stmts]
    cases assign <;> cases (bindingMethod c b m).2 <;>
      simp [notFunDef, mstoreArgs_all_notFunDef]
  exact (List.all_eq_true.mp hall) s hs

theorem hoist_emitExtCallBody {calls : ExternalCalls} (c : ContractDef)
    (d b m : Nat) (args : List Atom) (assign : Option YIdent) :
    hoist (yulD calls) (emitExtCallBody c d b m args assign) = [] :=
  hoist_nil_open (notFunDef_emitExtCallBody c d b m args assign)

theorem emitLetOp_call_stmts (c : ContractDef) (d b m : Nat) (args : List Atom) :
    ((emitLetOp c {} d (.call b m args)).getD {}).stmts =
      [.letDecl [identV d] (some (lit 0)),
        .block (emitExtCallBody c d b m args (some (identV d)))] := by
  simp [emitLetOp_call, emitExtCall_stmts, Emit.stmts_nil]

theorem emitStmt_call_stmts (c : ContractDef) (d b m : Nat) (args : List Atom) :
    (emitStmt c {} d (.call b m args)).stmts =
      [.block (emitExtCallBody c d b m args none)] := by
  simp [emitStmt_call, emitExtCall_stmts, Emit.stmts_nil]

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

theorem bindingMethod_of_BindWF {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {bind : Binding I S X} {b m : Nat} {meth : I.Method}
    (h : BindWF c Γ bind b m meth) :
    bindingMethod c b m = ((I.abi meth).selector, (I.abi meth).ret) := by
  rcases h.lookup with ⟨bd, hb, hm, _, _⟩
  obtain ⟨p, hp, hspec⟩ : ∃ p, bd.methods[m]? = some p ∧ p.2 = I.abi meth := by
    match hp : bd.methods[m]? with
    | none => simp [hp] at hm
    | some p =>
      refine ⟨p, rfl, ?_⟩
      simpa [hp] using hm
  rw [bindingMethod_eq hb hp, hspec]

theorem bindingSlot_of_BindWF {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {bind : Binding I S X} {b m : Nat} {meth : I.Method}
    (h : BindWF c Γ bind b m meth) :
    ∃ bd, c.bindings[b]? = some bd ∧ bindingSlot c b = bd.fieldSlot ∧
      (∀ σ, Γ.st.scalar bd.fieldSlot σ = bind.addr σ) ∧
      (c.fields[bd.fieldSlot]?).map (·.kind) = some FieldKind.scalar := by
  rcases h.lookup with ⟨bd, hb, _, hslot, hkind⟩
  exact ⟨bd, hb, bindingSlot_eq hb, hslot, hkind⟩

theorem sload_bind_addr {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ}
    {w : World S X E} {st : EvmState}
    {bind : Binding I S X} {b m : Nat} {meth : I.Method}
    (hR : R c Γ κ w st) (hbd : BindWF c Γ bind b m meth) :
    st.storage (BitVec.ofNat 256 (bindingSlot c b)) =
      BitVec.ofNat 256 (bind.addr w.self) := by
  obtain ⟨bd, hb, hbs, hslot, hkind⟩ := bindingSlot_of_BindWF hbd
  rw [hbs]
  rcases hR with ⟨hs, _, _, _⟩
  obtain ⟨fd, hfd, hk⟩ : ∃ fd, c.fields[bd.fieldSlot]? = some fd ∧ fd.kind = .scalar := by
    match hf : c.fields[bd.fieldSlot]? with
    | none => simp [hf] at hkind
    | some fd =>
      refine ⟨fd, rfl, ?_⟩
      simpa [hf] using hkind
  have hrel : st.storage (BitVec.ofNat 256 bd.fieldSlot) =
      BitVec.ofNat 256 (Γ.st.scalar bd.fieldSlot w.self) := by
    have hsc := hs bd.fieldSlot fd hfd
    simpa [hk] using hsc
  rw [hrel, hslot]

theorem callWF_arity_of_BindWF {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {bind : Binding I S X} {b m : Nat} {meth : I.Method} {args : List Atom}
    (hwf : callWF c b m args = true) (hbd : BindWF c Γ bind b m meth) :
    args.length = (I.abi meth).arity ∧ ∀ x ∈ args, atomWF x = true := by
  rcases hbd.lookup with ⟨bd, hb, hm, _, _⟩
  unfold callWF at hwf
  simp [hb] at hwf
  obtain ⟨p, hp, hspec⟩ : ∃ p, bd.methods[m]? = some p ∧ p.2 = I.abi meth := by
    match hp : bd.methods[m]? with
    | none => simp [hp] at hm
    | some p =>
      refine ⟨p, rfl, ?_⟩
      simpa [hp] using hm
  simp [hp, hspec, Bool.and_eq_true] at hwf
  exact hwf

/-! ## `noExt` of P / S -/

theorem noExt_mstoreArgs (d off : Nat) (args : List Atom) :
    noExtBlock (mstoreArgs d off args) = true := by
  induction args generalizing off with
  | nil => simp [mstoreArgs]
  | cons a as ih =>
    simp [mstoreArgs, noExtBlock, noExtStmt]
    refine ⟨noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_atomE]), ?_⟩
    simpa [noExtBlock] using ih (off + 1)

theorem noExt_callPrefix (c : ContractDef) (d b m : Nat) (args : List Atom) :
    noExtBlock (callPrefix c d b m args) = true := by
  unfold callPrefix
  refine noExtBlock_append ?_ (noExt_mstoreArgs d 0 args)
  simp [noExtBlock, noExtStmt]
  constructor
  · exact noExt_bop rfl (by simp [noExtExprs, noExt_lit])
  · exact noExt_bop rfl (by
      simp [noExtExprs, noExt_lit]
      exact noExt_bop rfl (by simp [noExtExprs, noExt_lit]))

theorem noExt_rds : noExtExpr (bop EVM.Op.returndatasize []) = true :=
  noExt_bop rfl noExtExprs_nil

theorem noExt_callRetCheck (ret : AbiRet) : noExtBlock (callRetCheck ret) = true := by
  cases ret with
  | none => simp [callRetCheck]
  | word =>
    simp [callRetCheck, noExtBlock, noExtStmt]
    exact ⟨noExt_bop rfl (by simp [noExtExprs, noExt_lit, noExt_rds]), noExt_revert00⟩
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
            noExt_bop rfl (by
              simp [noExtExprs, noExt_lit]
              exact noExt_bop rfl (by simp [noExtExprs, noExt_lit]))⟩)))

theorem noExt_callAssign (ret : AbiRet) (name : YIdent) :
    noExtBlock (callAssign ret name) = true := by
  cases ret with
  | word =>
    simp [callAssign, noExtBlock, noExtStmt]
    exact noExt_bop rfl (by simp [noExtExprs, noExt_lit])
  | boolOpt | none =>
    simp [callAssign, noExtBlock, noExtStmt, noExt_lit]

theorem noExt_callSuffix (d : Nat) (ret : AbiRet) (assign : Option YIdent) :
    noExtBlock (callSuffix d ret assign) = true := by
  unfold callSuffix
  refine noExtBlock_append (noExtBlock_append ?_ (noExt_callRetCheck ret)) ?_
  · simp [noExtBlock, noExtStmt]
    exact ⟨noExt_bop rfl (by simp [noExtExprs, noExt_var]), noExt_revert00⟩
  · cases assign with
    | none => simp [noExtBlock]
    | some name => exact noExt_callAssign ret name


/-! ## Prefix evaluation -/

theorem eval_atom_tok (funs : FunEnv evm) {env : List Nat} {V : VEnv evm}
    (st : EvmState) (tokv : U256)
    (hV : V = (extTok env.length, tokv) :: (identV env.length, (0 : U256)) :: toVEnv env)
    (hn : identsNodup (env.length + 1) = true) (a : Atom) :
    EvalExpr evm funs V st (atomE env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) := by
  have hn0 : identsNodup env.length = true := identsNodup_mono (Nat.le_succ _) hn
  cases a with
  | lit n =>
    simp [atomE, Atom.eval]
    exact Step.lit
  | var i =>
    simp only [atomE, Atom.eval]
    split_ifs with hi
    · have hneTok : extTok env.length ≠ identV (env.length - 1 - i) :=
        (identV_ne_extTok (env.length - 1 - i) env.length).symm
      have hneV : identV env.length ≠ identV (env.length - 1 - i) := by
        intro heq
        have hi' : env.length < env.length + 1 := Nat.lt_succ_self _
        have hj : env.length - 1 - i < env.length + 1 := by omega
        have : env.length = env.length - 1 - i :=
          identV_inj_of_nodup (env.length + 1) hn hi' hj heq
        omega
      have hget := get_toVEnv env hn0 hi
      have hlookup :
          VEnv.get V (identV (env.length - 1 - i)) =
            some (BitVec.ofNat 256 env[i]) := by
        rw [hV, VEnv.get_cons, if_neg hneTok, VEnv.get_cons, if_neg hneV]
        exact hget
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hlookup
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

theorem CallWorld.ofState_touch (st : EvmState) (p n : Nat) :
    CallWorld.ofState (touchMemory st p n) = CallWorld.ofState st := by
  simp [CallWorld.ofState, touchMemory]

theorem CallWorld.ofState_halt_touch (st : EvmState) (p n : Nat)
    (h : Option (HaltKind × List UInt8)) :
    CallWorld.ofState { touchMemory st p n with halted := h } = CallWorld.ofState st := by
  simp [CallWorld.ofState, touchMemory]

theorem CallWorld.ofState_mstore_nat (st : EvmState) (p : Nat) (v : U256) :
    CallWorld.ofState { touchMemory st p 32 with memory := storeWord st.memory p v } =
      CallWorld.ofState st := by
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
    (st : EvmState) (tokv : U256) (i : Nat) (a : Atom)
    (hV : V = (extTok env.length, tokv) :: (identV env.length, (0 : U256)) :: toVEnv env)
    (hn : identsNodup (env.length + 1) = true) (hi : i ≤ 3) :
    EvalExpr evm funs V st
      (bop EVM.Op.mstore [lit (abiAfterSel + 32 * i), atomE env.length a])
      (.vals []
        { touchMemory st (abiAfterSel + 32 * i) 32 with
          memory := storeWord st.memory (abiAfterSel + 32 * i)
            (BitVec.ofNat 256 (a.eval env)) }) := by
  have ha := eval_atom_tok funs st tokv hV hn a
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil ha) Step.lit) ?_
  simp only [litValue_number, step_mstore, toNat_abiAfterSel_off hi]

/-! ## (1) `call_prefix_fwd` -/

/-- Zero-argument packing: `sload` + selector `mstore`. -/
theorem call_prefix_fwd_nil {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat} {st : EvmState}
    {b m : Nat} {bind : Binding I S X} {meth : I.Method}
    (funs : FunEnv evm)
    (hR : R c Γ κ w st) (hbd : BindWF c Γ bind b m meth)
    (hctx : ctxRel ctx st) :
    ∃ st',
      ExecStmts evm funs
        ((identV env.length, (0 : U256)) :: toVEnv env) st
        (callPrefix c env.length b m [])
        ((extTok env.length, BitVec.ofNat 256 (bind.addr w.self)) ::
          (identV env.length, (0 : U256)) :: toVEnv env) st' .normal ∧
      readBytes st'.memory abiPtr 4 = selectorBytes (I.abi meth).selector ∧
      MemOnly st st' ∧
      st'.env.static = false ∧
      st'.memory = storeWord st.memory abiPtr
        (BitVec.ofNat 256 (I.abi meth).selector <<< 224) ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  let d := env.length
  let tok := extTok d
  let tokv := BitVec.ofNat 256 (bind.addr w.self)
  let V : VEnv evm := (identV d, (0 : U256)) :: toVEnv env
  have hbm := bindingMethod_of_BindWF hbd
  have hsel : (bindingMethod c b m).1 = (I.abi meth).selector := by rw [hbm]
  have hselLt := hbd.hsel meth
  have htok := sload_bind_addr (κ := κ) hR hbd
  have hstatic0 : st.env.static = false := by
    rcases hctx with ⟨_, _, _, _, _, hs, _⟩
    exact hs
  have hsload :
      EvalExpr evm funs V st (bop EVM.Op.sload [lit (bindingSlot c b)])
        (.vals [st.storage (BitVec.ofNat 256 (bindingSlot c b))] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit)
      (by simp only [litValue_number, step_sload])
  have hlet :
      ExecStmt evm funs V st
        (.letDecl [tok] (some (bop EVM.Op.sload [lit (bindingSlot c b)])))
        ((tok, st.storage (BitVec.ofNat 256 (bindingSlot c b))) :: V) st .normal :=
    Step.letVal hsload (by simp)
  rw [htok] at hlet
  let V1 : VEnv evm := (tok, tokv) :: V
  have hmSel := eval_mstore_sel_fwd funs V1 st (bindingMethod c b m).1
  let stSel : EvmState :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr
        (BitVec.ofNat 256 (bindingMethod c b m).1 <<< 224) }
  have hdoSel :
      ExecStmt evm funs V1 st
        (.exprStmt (bop EVM.Op.mstore
          [lit abiPtr, bop EVM.Op.shl [lit 224, lit (bindingMethod c b m).1]]))
        V1 stSel .normal :=
    Step.exprStmt hmSel
  have hMO_sel : MemOnly st stSel := by
    simpa [stSel] using memOnly_mstore_nat st abiPtr
      (BitVec.ofNat 256 (bindingMethod c b m).1 <<< 224) toNat_abiPtr
  refine ⟨stSel, ?_, ?_, hMO_sel, ?_, ?_, ?_⟩
  · simp [callPrefix, mstoreArgs]
    exact Step.seqCons hlet (Step.seqCons hdoSel Step.seqNil)
  · simp [stSel]
    rw [hsel]
    exact readBytes_pack0 st.memory (I.abi meth).selector hselLt
  · rcases hMO_sel with ⟨_, _, _, _, _, _, _, hs, _, _, _⟩
    exact hs.trans hstatic0
  · simp [stSel, hsel]
  · simp [stSel, CallWorld.ofState, touchMemory]

theorem callPrefix_append (c : ContractDef) (d b m : Nat) (args : List Atom) :
    callPrefix c d b m args = callPrefix c d b m [] ++ mstoreArgs d 0 args := by
  simp [callPrefix, mstoreArgs]

/-- Pack `args` (arity ≤ 3) into memory that already holds the 4-byte selector. -/
theorem mstoreArgs_exec {env : List Nat} {V : VEnv evm}
    (funs : FunEnv evm) (st : EvmState) (orig : Nat → UInt8)
    (tokv : U256) (sel : Nat) (args : List Atom)
    (hV : V = (extTok env.length, tokv) :: (identV env.length, (0 : U256)) :: toVEnv env)
    (hn : identsNodup (env.length + 1) = true)
    (hn3 : args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true) (hwf : EnvWF env)
    (hsel : sel < 2 ^ 32)
    (hmem : st.memory = storeWord orig abiPtr (BitVec.ofNat 256 sel <<< 224)) :
    ∃ st',
      ExecStmts evm funs V st (mstoreArgs env.length 0 args) V st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * args.length) =
        selectorBytes sel ++ args.flatMap (fun a => wordBytes (a.eval env)) ∧
      MemOnly st st' ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  have hi0 : (0 : Nat) ≤ 3 := by decide
  have hi1 : (1 : Nat) ≤ 3 := by decide
  have hi2 : (2 : Nat) ≤ 3 := by decide
  cases args with
  | nil =>
    refine ⟨st, Step.seqNil, ?_, ?_, rfl⟩
    · simp [hmem]
      exact readBytes_pack0 orig sel hsel
    · simp [MemOnly]
  | cons a rest =>
    cases rest with
    | nil =>
      have haLt := atom_eval_lt hwf (hvals a (by simp))
      have hmA := eval_mstore_atom_fwd (env := env) funs st tokv 0 a hV hn hi0
      let stA : EvmState :=
        { touchMemory st abiAfterSel 32 with
          memory := storeWord st.memory abiAfterSel (BitVec.ofNat 256 (a.eval env)) }
      have hdoA : ExecStmt evm funs V st
          (.exprStmt (bop EVM.Op.mstore [lit abiAfterSel, atomE env.length a]))
          V stA .normal := by
        simpa [Nat.mul_zero, Nat.add_zero] using Step.exprStmt hmA
      refine ⟨stA, ?_, ?_, ?_, ?_⟩
      · simp [mstoreArgs]
        exact Step.seqCons hdoA Step.seqNil
      · simp [stA, hmem, abiInput]
        exact readBytes_pack1 orig sel (a.eval env) hsel haLt
      · simpa [stA] using memOnly_mstore_nat st abiAfterSel
          (BitVec.ofNat 256 (a.eval env)) (toNat_abiAfterSel_off hi0)
      · simp [stA, CallWorld.ofState, touchMemory]
    | cons a2 rest2 =>
      cases rest2 with
      | nil =>
        have haLt := atom_eval_lt hwf (hvals a (by simp))
        have h2Lt := atom_eval_lt hwf (hvals a2 (by simp))
        have hmA := eval_mstore_atom_fwd (env := env) funs st tokv 0 a hV hn hi0
        let stA : EvmState :=
          { touchMemory st abiAfterSel 32 with
            memory := storeWord st.memory abiAfterSel (BitVec.ofNat 256 (a.eval env)) }
        have hdoA : ExecStmt evm funs V st
            (.exprStmt (bop EVM.Op.mstore [lit abiAfterSel, atomE env.length a]))
            V stA .normal := by
          simpa [Nat.mul_zero, Nat.add_zero] using Step.exprStmt hmA
        have hmB := eval_mstore_atom_fwd (env := env) funs stA tokv 1 a2 hV hn hi1
        let stB : EvmState :=
          { touchMemory stA (abiAfterSel + 32) 32 with
            memory := storeWord stA.memory (abiAfterSel + 32)
              (BitVec.ofNat 256 (a2.eval env)) }
        have hdoB : ExecStmt evm funs V stA
            (.exprStmt (bop EVM.Op.mstore [lit (abiAfterSel + 32), atomE env.length a2]))
            V stB .normal :=
          Step.exprStmt hmB
        refine ⟨stB, ?_, ?_, ?_, ?_⟩
        · simp [mstoreArgs]
          exact Step.seqCons hdoA (Step.seqCons hdoB Step.seqNil)
        · simp [stB, stA, hmem]
          exact readBytes_pack2 orig sel (a.eval env) (a2.eval env) hsel haLt h2Lt
        · have hMOA : MemOnly st stA := by
            simpa [stA] using
              (memOnly_mstore_nat st abiAfterSel
                (BitVec.ofNat 256 (a.eval env)) (toNat_abiAfterSel_off hi0))
          have hMOB : MemOnly stA stB := by
            simpa [stB] using
              (memOnly_mstore_nat stA (abiAfterSel + 32)
                (BitVec.ofNat 256 (a2.eval env)) (toNat_abiAfterSel_off hi1))
          exact MemOnly.trans hMOA hMOB
        · simp [stB, stA, CallWorld.ofState, touchMemory]
      | cons a3 rest3 =>
        cases rest3 with
        | nil =>
          have haLt := atom_eval_lt hwf (hvals a (by simp))
          have h2Lt := atom_eval_lt hwf (hvals a2 (by simp))
          have h3Lt := atom_eval_lt hwf (hvals a3 (by simp))
          have hmA := eval_mstore_atom_fwd (env := env) funs st tokv 0 a hV hn hi0
          let stA : EvmState :=
            { touchMemory st abiAfterSel 32 with
              memory := storeWord st.memory abiAfterSel (BitVec.ofNat 256 (a.eval env)) }
          have hdoA : ExecStmt evm funs V st
              (.exprStmt (bop EVM.Op.mstore [lit abiAfterSel, atomE env.length a]))
              V stA .normal := by
            simpa [Nat.mul_zero, Nat.add_zero] using Step.exprStmt hmA
          have hmB := eval_mstore_atom_fwd (env := env) funs stA tokv 1 a2 hV hn hi1
          let stB : EvmState :=
            { touchMemory stA (abiAfterSel + 32) 32 with
              memory := storeWord stA.memory (abiAfterSel + 32)
                (BitVec.ofNat 256 (a2.eval env)) }
          have hdoB : ExecStmt evm funs V stA
              (.exprStmt (bop EVM.Op.mstore [lit (abiAfterSel + 32), atomE env.length a2]))
              V stB .normal :=
            Step.exprStmt hmB
          have hmC := eval_mstore_atom_fwd (env := env) funs stB tokv 2 a3 hV hn hi2
          let stC : EvmState :=
            { touchMemory stB (abiAfterSel + 64) 32 with
              memory := storeWord stB.memory (abiAfterSel + 64)
                (BitVec.ofNat 256 (a3.eval env)) }
          have hdoC : ExecStmt evm funs V stB
              (.exprStmt (bop EVM.Op.mstore [lit (abiAfterSel + 64), atomE env.length a3]))
              V stC .normal := by
            simpa using Step.exprStmt hmC
          refine ⟨stC, ?_, ?_, ?_, ?_⟩
          · simp [mstoreArgs]
            exact Step.seqCons hdoA (Step.seqCons hdoB (Step.seqCons hdoC Step.seqNil))
          · simp [stC, stB, stA, hmem]
            exact readBytes_pack3 orig sel (a.eval env) (a2.eval env) (a3.eval env)
              hsel haLt h2Lt h3Lt
          · have hMOA : MemOnly st stA := by
              simpa [stA] using
                (memOnly_mstore_nat st abiAfterSel
                  (BitVec.ofNat 256 (a.eval env)) (toNat_abiAfterSel_off hi0))
            have hMOB : MemOnly stA stB := by
              simpa [stB] using
                (memOnly_mstore_nat stA (abiAfterSel + 32)
                  (BitVec.ofNat 256 (a2.eval env)) (toNat_abiAfterSel_off hi1))
            have hMOC : MemOnly stB stC := by
              simpa [stC] using
                (memOnly_mstore_nat stB (abiAfterSel + 64)
                  (BitVec.ofNat 256 (a3.eval env)) (toNat_abiAfterSel_off hi2))
            exact MemOnly.trans hMOA (MemOnly.trans hMOB hMOC)
          · simp [stC, stB, stA, CallWorld.ofState, touchMemory]
        | cons _ _ => simp at hn3

theorem call_prefix_fwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    (funs : FunEnv evm)
    (hR : R c Γ κ w st) (hbd : BindWF c Γ bind b m meth)
    (hctx : ctxRel ctx st) (hwf : EnvWF env)
    (hn : identsNodup (env.length + 1) = true)
    (hn3 : args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true) :
    ∃ st',
      ExecStmts evm funs
        ((identV env.length, (0 : U256)) :: toVEnv env) st
        (callPrefix c env.length b m args)
        ((extTok env.length, BitVec.ofNat 256 (bind.addr w.self)) ::
          (identV env.length, (0 : U256)) :: toVEnv env) st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * args.length) =
        abiInput (I.abi meth) (args.map (·.eval env)) ∧
      MemOnly st st' ∧
      st'.env.static = false ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  obtain ⟨stSel, hP, _, hMO0, hstatic, hmem, hCW0⟩ :=
    call_prefix_fwd_nil (I := I) funs hR hbd hctx
  have hselLt := hbd.hsel meth
  have hbm := bindingMethod_of_BindWF hbd
  let tokv := BitVec.ofNat 256 (bind.addr w.self)
  let V1 : VEnv evm :=
    (extTok env.length, tokv) :: (identV env.length, (0 : U256)) :: toVEnv env
  obtain ⟨st', hM, hpack, hMO, hCW⟩ :=
    mstoreArgs_exec (env := env) funs stSel st.memory tokv
      (I.abi meth).selector args rfl hn hn3 hvals hwf hselLt hmem
  refine ⟨st', ?_, ?_, MemOnly.trans hMO0 hMO, ?_, hCW.trans hCW0⟩
  · rw [callPrefix_append]
    exact execStmts_append hP hM
  · simpa [abiInput, List.flatMap_map] using hpack
  · rcases hMO with ⟨_, _, _, _, _, _, _, hs, _, _, _⟩
    exact hs.trans hstatic


/-! ## (2) `call_step_inv` -/

theorem call_step_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {d : Nat} {args : List Atom} {target : U256}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hget : VEnv.get V (extTok d) = some target)
    (hstatic : st.env.static = false)
    (hn3 : args.length ≤ 3)
    (h : ExecStmt (yulD calls) funs V st (callLetOk d args) V' st' o) :
    ∃ resp, o = .normal ∧ V' = (extOk d, resp.flag) :: V ∧
      st' = finishCall .call st resp abiPtr (4 + 32 * args.length) abiPtr 32 ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 extCallGas
          target := target
          value := 0
          input := readBytes st.memory abiPtr (4 + 32 * args.length) }
        st resp := by
  unfold callLetOk at h
  obtain ⟨resp, ho, hV, hst, hCall⟩ :=
    exec_let_call_inv (tok := extTok d) (ok := extOk d) (gas := extCallGas)
      (insize := 4 + 32 * args.length) hget hstatic h
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hst
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  exact ⟨resp, ho, hV, hst, hCall⟩

/-! ## (3) `call_suffix_fwd` -/

def suffixVal (ret : AbiRet) (st : EvmState) : U256 :=
  match ret with
  | .word => loadWord st.memory abiPtr
  | .boolOpt | .none => 1

def suffixOk (ok : U256) (ret : AbiRet) (st : EvmState) : Prop :=
  ok ≠ 0 ∧
    match ret with
    | .none => True
    | .word => (BitVec.ofNat 256 st.returndata.length).ult 32#256 = false
    | .boolOpt =>
        BitVec.ofNat 256 st.returndata.length = 0 ∨
          ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false ∧
            loadWord st.memory abiPtr = 1#256)

def boolOptPass (st : EvmState) : Bool :=
  decide (BitVec.ofNat 256 st.returndata.length = 0) ||
    (decide ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&
      decide (loadWord st.memory abiPtr = 1#256))

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

theorem eval_eq_mload1_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1])
      (.vals [b2w (loadWord st.memory abiPtr = 1#256)] (touchMemory st abiPtr 32)) :=
  Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (eval_mload_abi_fwd funs V st))
    (by simp only [litValue_number, step_eq])

theorem eval_boolOpt_and_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.and
        [bop EVM.Op.iszero
          [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
          bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&&
          b2w (loadWord st.memory abiPtr = 1#256)]
        (touchMemory st abiPtr 32)) := by
  let stM := touchMemory st abiPtr 32
  have heq := eval_eq_mload1_fwd funs V st
  have hisz : EvalExpr evm funs V stM
      (bop EVM.Op.iszero
        [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]])
      (.vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false)] stM) := by
    simpa [stM, touchMemory] using eval_iszero_lt_rds32_fwd funs V stM
  exact Step.builtinOk (Step.argsCons
    (Step.argsCons Step.argsNil heq) hisz) (by simp only [step_and]; rfl)

theorem eval_boolOpt_or_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.or
        [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
          bop EVM.Op.and
            [bop EVM.Op.iszero
              [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
              bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]]])
      (.vals [b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
          (b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&&
            b2w (loadWord st.memory abiPtr = 1#256))]
        (touchMemory st abiPtr 32)) := by
  let stM := touchMemory st abiPtr 32
  have hand := eval_boolOpt_and_fwd funs V st
  have hisz : EvalExpr evm funs V stM
      (bop EVM.Op.iszero [bop EVM.Op.returndatasize []])
      (.vals [b2w (BitVec.ofNat 256 st.returndata.length = 0)] stM) := by
    simpa [stM, touchMemory] using eval_iszero_rds_fwd funs V stM
  exact Step.builtinOk (Step.argsCons
    (Step.argsCons Step.argsNil hand) hisz) (by simp only [step_or]; rfl)

theorem boolOpt_orVal (st : EvmState) :
    b2w (BitVec.ofNat 256 st.returndata.length = 0) |||
      (b2w ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) &&&
        b2w (loadWord st.memory abiPtr = 1#256)) =
      b2w (boolOptPass st) := by
  have hult :
      decide ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) =
        ((BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) := by
    cases (BitVec.ofNat 256 st.returndata.length).ult 32#256 <;> simp
  simp only [boolOptPass, b2w_and, b2w_or, hult]

theorem eval_boolOpt_cond_fwd (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop EVM.Op.iszero
        [bop EVM.Op.or
          [bop EVM.Op.iszero [bop EVM.Op.returndatasize []],
            bop EVM.Op.and
              [bop EVM.Op.iszero
                [bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]],
                bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]]]])
      (.vals [b2w (!boolOptPass st)] (touchMemory st abiPtr 32)) := by
  refine Step.builtinOk
    (Step.argsCons Step.argsNil (eval_boolOpt_or_fwd funs V st)) ?_
  simp only [step_iszero]
  rw [boolOpt_orVal, b2w_iszero]

theorem call_guard_fail (funs : FunEnv evm) {V : VEnv evm} {st : EvmState}
    {d : Nat} (hget : VEnv.get V (extOk d) = some 0) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.iszero [var (extOk d)]) [revert00])
      V { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.ifTrue (D := evm) (eval_iszero_var_fwd funs hget) ?_
    (exec_revert00_block funs V st)
  simp [b2w, Dialect.zero, litValue, litValue_number]

theorem call_guard_pass (funs : FunEnv evm) {V : VEnv evm} {st : EvmState}
    {d : Nat} {ok : U256} (hget : VEnv.get V (extOk d) = some ok)
    (hok : ok ≠ 0) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.iszero [var (extOk d)]) [revert00])
      V st .normal := by
  refine Step.ifFalse (eval_iszero_var_fwd funs hget) ?_
  simp [hok, b2w, Dialect.zero, litValue, litValue_number]
  exact hok

theorem word_check_fail (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = true) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]) [revert00])
      V { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.ifTrue (D := evm) (eval_lt_rds32_fwd funs V st) ?_
    (exec_revert00_block funs V st)
  simp [h, b2w, Dialect.zero, litValue, litValue_number]

theorem word_check_pass (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (h : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = false) :
    ExecStmt evm funs V st
      (.cond (bop EVM.Op.lt [bop EVM.Op.returndatasize [], lit 32]) [revert00])
      V st .normal := by
  refine Step.ifFalse (eval_lt_rds32_fwd funs V st) ?_
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
                  bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]]]])
        [revert00])
      V { touchMemory (touchMemory st abiPtr 32) 0 0 with
          halted := some (.revert, []) } .halt := by
  have hcv : b2w (!boolOptPass st) ≠ evm.zero := by
    simp [h, b2w, Dialect.zero, litValue, litValue_number]
  refine Step.ifTrue (D := evm) (eval_boolOpt_cond_fwd funs V st) hcv
    (exec_revert00_block funs V (touchMemory st abiPtr 32))

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
                  bop EVM.Op.eq [bop EVM.Op.mload [lit abiPtr], lit 1]]]])
        [revert00])
      V (touchMemory st abiPtr 32) .normal := by
  refine Step.ifFalse (eval_boolOpt_cond_fwd funs V st) ?_
  simp [h, b2w, Dialect.zero, litValue, litValue_number]

theorem callAssign_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (ret : AbiRet) (name : YIdent) :
    ExecStmts evm funs V st (callAssign ret name)
      (VEnv.set V name (suffixVal ret st))
      (match ret with
        | .word => touchMemory st abiPtr 32
        | .boolOpt | .none => st) .normal := by
  cases ret with
  | word =>
    simp [callAssign, suffixVal]
    have h : ExecStmts evm funs V st
        [.assign [name] (bop EVM.Op.mload [lit abiPtr])]
        (VEnv.setMany V [name] [loadWord st.memory abiPtr])
        (touchMemory st abiPtr 32) .normal :=
      Step.seqCons (Step.assignVal (D := evm) (eval_mload_abi_fwd funs V st) rfl) Step.seqNil
    rwa [VEnv.setMany_one] at h
  | boolOpt =>
    simp [callAssign, suffixVal]
    have he : EvalExpr evm funs V st (lit 1) (.vals [1#256] st) := Step.lit
    have h : ExecStmts evm funs V st [.assign [name] (lit 1)]
        (VEnv.setMany V [name] [1#256]) st .normal :=
      Step.seqCons (Step.assignVal (D := evm) he rfl) Step.seqNil
    rwa [VEnv.setMany_one] at h
  | none =>
    simp [callAssign, suffixVal]
    have he : EvalExpr evm funs V st (lit 1) (.vals [1#256] st) := Step.lit
    have h : ExecStmts evm funs V st [.assign [name] (lit 1)]
        (VEnv.setMany V [name] [1#256]) st .normal :=
      Step.seqCons (Step.assignVal (D := evm) he rfl) Step.seqNil
    rwa [VEnv.setMany_one] at h

theorem suffixOk_boolOpt {ok : U256} {st : EvmState}
    (hok : ok ≠ 0) : suffixOk ok .boolOpt st ↔ boolOptPass st = true := by
  constructor
  · intro h
    have hp := h.2
    simp [boolOptPass]
    cases hp with
    | inl h0 => simp [h0]
    | inr hrest => simp [hrest.1, hrest.2]
  · intro h
    refine ⟨hok, ?_⟩
    unfold boolOptPass at h
    rcases Bool.or_eq_true_iff.mp h with h0 | hand
    · exact .inl (of_decide_eq_true h0)
    · have hpair := Bool.and_eq_true_iff.mp hand
      exact .inr ⟨of_decide_eq_true hpair.1, of_decide_eq_true hpair.2⟩

theorem call_suffix_fwd (funs : FunEnv evm) {d : Nat} {ok : U256}
    {ret : AbiRet} {assign : Option YIdent}
    {V : VEnv evm} {st : EvmState}
    (hget : VEnv.get V (extOk d) = some ok) :
    ∃ V' st' o,
      ExecStmts evm funs V st (callSuffix d ret assign) V' st' o ∧
      (suffixOk ok ret st →
        o = .normal ∧ MemOnly st st' ∧
          V' = match assign with
            | none => V
            | some name => VEnv.set V name (suffixVal ret st)) ∧
      (¬ suffixOk ok ret st →
        o = .halt ∧ V' = V ∧ st'.halted = some (.revert, [])) ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  unfold callSuffix
  by_cases hok : ok = 0
  · subst hok
    refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt, ?_, ?_, ?_, ?_⟩
    · exact Step.seqStop (call_guard_fail funs hget) halt_ne_normal
    · intro hS; exact (hS.1 rfl).elim
    · intro; exact ⟨rfl, rfl, rfl⟩
    · simp [CallWorld.ofState, touchMemory]
  · have hguard := call_guard_pass (st := st) funs hget hok
    cases ret with
    | none =>
      cases assign with
      | none =>
        refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard Step.seqNil
        · intro; exact ⟨rfl, by simp [MemOnly], rfl⟩
        · intro hS; exact (hS ⟨hok, trivial⟩).elim
      | some name =>
        have hasn := callAssign_exec funs V st .none name
        refine ⟨VEnv.set V name (1#256), st, .normal, ?_, ?_, ?_, rfl⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard hasn
        · intro; exact ⟨rfl, by simp [MemOnly], by simp [suffixVal]⟩
        · intro hS; exact (hS ⟨hok, trivial⟩).elim
    | word =>
      by_cases hult : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = true
      · refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt,
          ?_, ?_, ?_, by simp [CallWorld.ofState, touchMemory]⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard
            (Step.seqStop (word_check_fail funs V st hult) halt_ne_normal)
        · intro hS; simp [suffixOk, hok, hult] at hS
        · intro; exact ⟨rfl, rfl, rfl⟩
      · have hpass : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = false := by
          simpa using hult
        have hchk := word_check_pass funs V st hpass
        cases assign with
        | none =>
          refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk Step.seqNil)
          · intro; exact ⟨rfl, by simp [MemOnly], rfl⟩
          · intro hS; exact (hS ⟨hok, hpass⟩).elim
        | some name =>
          have hasn := callAssign_exec funs V st .word name
          refine ⟨VEnv.set V name (loadWord st.memory abiPtr),
            touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk hasn)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, by simp [suffixVal]⟩
          · intro hS; exact (hS ⟨hok, hpass⟩).elim
    | boolOpt =>
      by_cases hp : boolOptPass st = true
      · have hchk := boolOpt_check_pass funs V st hp
        cases assign with
        | none =>
          refine ⟨V, touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk Step.seqNil)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, rfl⟩
          · intro hS
            have : suffixOk ok .boolOpt st := (suffixOk_boolOpt hok).mpr hp
            exact (hS this).elim
        | some name =>
          have hasn := callAssign_exec funs V (touchMemory st abiPtr 32) .boolOpt name
          refine ⟨VEnv.set V name (1#256), touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk hasn)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, by simp [suffixVal]⟩
          · intro hS
            have : suffixOk ok .boolOpt st := (suffixOk_boolOpt hok).mpr hp
            exact (hS this).elim
      · have hfail : boolOptPass st = false := by simpa using hp
        refine ⟨V,
          { touchMemory (touchMemory st abiPtr 32) 0 0 with
            halted := some (.revert, []) }, .halt, ?_, ?_, ?_,
          by simp [CallWorld.ofState, touchMemory]⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard
            (Step.seqStop (boolOpt_check_fail funs V st hfail) halt_ne_normal)
        · intro hS
          have : boolOptPass st = true := (suffixOk_boolOpt hok).mp hS
          simp [hfail] at this
        · intro; exact ⟨rfl, rfl, rfl⟩

/-! ## (4) `op_sim_call_bwd` -/

theorem VEnv.set_cons_ne {x y : Ident} {vx vy : U256} {V : VEnv evm}
    (h : x ≠ y) :
    VEnv.set ((x, vx) :: V) y vy = (x, vx) :: VEnv.set V y vy := by
  simp [VEnv.set, h]

theorem ult32_of_ge {n : Nat} (hn : n < wordBound) (h : 32 ≤ n) :
    (BitVec.ofNat 256 n).ult 32#256 = false := by
  have h32 : (32 : Nat) < wordBound := lt_256_wordBound (by decide)
  rw [ult_ofNat hn h32]
  simp [Nat.not_lt.mpr h]

theorem decodeRet_suffixOk {ok : U256} {ret : AbiRet} {st : EvmState} {v : Nat}
    (hok : ok ≠ 0) (h : decodeRet ret st.returndata v)
    (hm : 32 ≤ st.returndata.length →
      loadWord st.memory abiPtr = wordFrom st.returndata 0) :
    suffixOk ok ret st := by
  refine ⟨hok, ?_⟩
  cases ret with
  | none => trivial
  | word =>
    exact ult32_of_ge h.2.1 h.1
  | boolOpt =>
    rcases h with ⟨_, hbd, hor⟩
    cases hor with
    | inl h0 => exact .inl (by simp [h0])
    | inr hrest =>
      exact .inr ⟨ult32_of_ge hbd hrest.1, by rw [hm hrest.1, hrest.2]⟩

theorem R_with_ghost {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} (ext' : X) (n' : Nat) (f' : Nat → Bool)
    (h : R c Γ κ w st) :
    R c Γ κ { w with ext := ext', ncalls := n', faults := f' } st := by
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

theorem op_sim_call_bwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (α : Abs I.Ghost)
    (hinv : Inv Γ c κ ctx w env V st)
    (hbd : BindWF c Γ bind b m meth)
    (hRX : RX α bind w st)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF c b m args = true)
    (hn : identsNodup (env.length + 1) = true)
    (h : ExecStmts (yulD calls) funs V st
      ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o) :
    ∃ bit : Bool,
      let w₁ : World S X E := { w with faults := composeFault w.ncalls bit w.faults }
      (bit = true →
        Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ = .error .callFailed ∧
        o = .halt ∧ st'.halted = some (.revert, [])) ∧
      (bit = false →
        ∃ v w', Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ = .ok (v, w') ∧
          o = .normal ∧ V' = toVEnv (v :: env) ∧
          Inv Γ c κ ctx w' (v :: env) V' st' ∧ RX α bind w' st') := by
  let d := env.length
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  have ⟨harity, hvals⟩ := callWF_arity_of_BindWF hwfCall hbd
  have hn3 : args.length ≤ 3 := by rw [harity]; exact hbd.harity
  have hret := bindingMethod_of_BindWF hbd
  rw [hVeq, emitLetOp_call_stmts] at h
  cases execStmts_cons_inv h with
  | inr hstop =>
    have ⟨ho, _, _⟩ := exec_let_lit_inv hstop.2
    exact (hstop.1 ho).elim
  | inl hlet =>
    obtain ⟨V1, st1, hdoLet, hblkStmts⟩ := hlet
    have ⟨_, hst1, hV1⟩ := exec_let_lit_inv hdoLet
    rw [hst1, hV1] at hblkStmts
    have hblkStmt : ExecStmt (yulD calls) funs
        ((identV d, (0 : U256)) :: toVEnv env) st
        (.block (emitExtCallBody c d b m args (some (identV d)))) V' st' o := by
      cases hblkStmts with
      | seqCons hb hnil =>
        cases hnil
        exact hb
      | seqStop hb _ => exact hb
    obtain ⟨Vb, hbody, hrestore⟩ := exec_block_inv hblkStmt
    have hhoist := hoist_emitExtCallBody (calls := calls) c d b m args (some (identV d))
    rw [hhoist] at hbody
    rw [emitExtCallBody_split] at hbody
    rw [List.append_assoc] at hbody
    have hfunsB : noExtFuns (([] : FScope (yulD calls)) :: funs) = true :=
      noExtFuns_cons_nil hfuns
    let funsE := funEnvUncast calls ([] :: funs)
    cases execStmts_append_inv hbody with
    | inr hPstop =>
      have hdesc := execStmts_descend hfunsB (noExt_callPrefix c d b m args) hPstop.2
      obtain ⟨stP, hfwd, _, _, _, _⟩ :=
        call_prefix_fwd (I := I) funsE hR hbd hctx henv hn hn3 hvals
      have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
      exact (hPstop.1 ho.symm).elim
    | inl hPok =>
      obtain ⟨_, _, hP, hrest⟩ := hPok
      have hPdesc := execStmts_descend hfunsB (noExt_callPrefix c d b m args) hP
      obtain ⟨stP, hPfwd, hpack, hMO, hstaticP, hCW⟩ :=
        call_prefix_fwd (I := I) funsE hR hbd hctx henv hn hn3 hvals
      have ⟨hVPeq, hstPeq, _⟩ := execStmts_det_evm hPfwd hPdesc
      rw [← hVPeq, ← hstPeq] at hrest
      have hgetTok :
          VEnv.get
            ((extTok d, BitVec.ofNat 256 (bind.addr w.self)) ::
              (identV d, (0 : U256)) :: toVEnv env)
            (extTok d) = some (BitVec.ofNat 256 (bind.addr w.self)) := by
        simp [VEnv.get]
      cases execStmts_cons_inv hrest with
      | inr hCstop =>
        have ⟨resp, ho, _, _, _⟩ :=
          call_step_inv hgetTok hstaticP hn3 hCstop.2
        exact (hCstop.1 ho).elim
      | inl hCok =>
        obtain ⟨_, _, hCall, hS⟩ := hCok
        obtain ⟨resp, _, hV2, hst2, hCallR⟩ :=
          call_step_inv hgetTok hstaticP hn3 hCall
        rw [hV2, hst2] at hS
        have hgetOk :
            VEnv.get
              ((extOk d, resp.flag) ::
                (extTok d, BitVec.ofNat 256 (bind.addr w.self)) ::
                  (identV d, (0 : U256)) :: toVEnv env)
              (extOk d) = some resp.flag := by
          simp [VEnv.get]
        rw [show (bindingMethod c b m).2 = (I.abi meth).ret from
          congrArg Prod.snd hret] at hS
        have hSdesc := execStmts_descend hfunsB
          (noExt_callSuffix d (I.abi meth).ret (some (identV d))) hS
        obtain ⟨VS, stS, oS, hSfwd, hSok, hSfail, hCWS⟩ :=
          call_suffix_fwd
            (st := finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)
            (ret := (I.abi meth).ret)
            (assign := some (identV d)) funsE hgetOk
        have ⟨hVSeq, hstSeq, hoeq⟩ := execStmts_det_evm hSfwd hSdesc
        refine ⟨!resp.success, ?_⟩
        intro w₁
        constructor
        · intro hbit
          have hsuccF : resp.success = false := by
            cases hsu : resp.success
            · rfl
            · simp [hsu] at hbit
          have hok0 : resp.flag = 0 := (flag_eq_zero_iff resp).mpr hsuccF
          have hnS : ¬ suffixOk resp.flag (I.abi meth).ret
              (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) := by
            intro hSok'
            exact hSok'.1 hok0
          have ⟨hoS, _, hh⟩ := hSfail hnS
          have hrun : Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ =
              .error .callFailed := by
            rw [Op.denote, hbd.hext]
            have hf : w₁.faults w₁.ncalls = true :=
              (composeFault_at w.ncalls (!resp.success) w.faults).trans hbit
            simp [Tx.run_call, hf]
          exact ⟨hrun, hoeq.symm.trans hoS, hstSeq ▸ hh⟩
        · intro hbit
          have hsucc : resp.success = true := by
            cases hsu : resp.success
            · simp [hsu] at hbit
            · rfl
          have haddr : stP.env.address = BitVec.ofNat 256 ctx.self := by
            rcases hMO with ⟨_, _, _, _, _, _, ha, _, _, _, _⟩
            rcases hctx with ⟨_, _, _, _, had, _⟩
            exact ha.trans had
          have hα : α.ofState stP (bind.addr w.self) = bind.get w.ext := by
            rw [α.ofState_proj, hCW, ← α.ofState_proj]
            exact hRX
          have ⟨m', args', retv, g', hin, harity', hbdargs, hmodel, hdec, hg, hni⟩ :=
            hconf
              { kind := .call
                gas := BitVec.ofNat 256 extCallGas
                target := BitVec.ofNat 256 (bind.addr w.self)
                value := 0
                input := readBytes stP.memory abiPtr (4 + 32 * args.length) }
              stP resp hCallR rfl rfl haddr hsucc
          have hsel_eq : (I.abi m').selector = (I.abi meth).selector := by
            have ht := congrArg (fun l => l.take 4) (hin.symm.trans hpack)
            have htake : ∀ spec as, (abiInput spec as).take 4 = selectorBytes spec.selector := by
              intro spec as
              simp [abiInput, selectorBytes_length, List.take_append_of_le_length]
            rw [htake, htake] at ht
            exact selectorBytes_inj (hbd.hsel m') (hbd.hsel meth) ht
          have hm' : m' = meth := hbd.huniq m' hsel_eq
          cases hm'
          have hargs : args' = args.map (·.eval env) := by
            refine abiArgs_inj (hbd.hsel meth) hbdargs ?_ ?_ ?_ (hin.symm.trans hpack)
            · intro x hx
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact atom_eval_lt henv (hvals a ha)
            · simp [harity', harity]
            · rw [harity']; exact hbd.harity
          subst hargs
          have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
          have hmload : 32 ≤ resp.returndata.length →
              loadWord (finishCall .call stP resp abiPtr (4 + 32 * args.length)
                  abiPtr 32).memory abiPtr =
                wordFrom resp.returndata 0 := by
            intro hlen
            exact finishCall_mload_ge32 .call stP resp abiPtr (4 + 32 * args.length)
              abiPtr 32 hlen (by decide)
          have hSok' : suffixOk resp.flag (I.abi meth).ret
              (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) := by
            simpa [finishCall_returndata] using
              decodeRet_suffixOk hflag hdec hmload
          have ⟨hoS, hMOS, hVeq⟩ := hSok hSok'
          have hrun : Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ =
              .ok (retv,
                { w₁ with ext := bind.set w₁.ext g', ncalls := w₁.ncalls + 1 }) := by
            rw [Op.denote, hbd.hext]
            have hf : w₁.faults w₁.ncalls = false :=
              (composeFault_at w.ncalls (!resp.success) w.faults).trans hbit
            simp [Tx.run_call, hf]
            have hgext : bind.get w₁.ext = bind.get w.ext := rfl
            rw [hgext, ← hα, hmodel]
          have hset :
              VEnv.set ((extOk d, resp.flag) :: (extTok d,
                  BitVec.ofNat 256 (bind.addr w.self)) ::
                (identV d, (0 : U256)) :: toVEnv env)
                (identV d)
                (suffixVal (I.abi meth).ret
                  (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)) =
              (extOk d, resp.flag) :: (extTok d,
                  BitVec.ofNat 256 (bind.addr w.self)) ::
                (identV d,
                  suffixVal (I.abi meth).ret
                    (finishCall .call stP resp abiPtr (4 + 32 * args.length)
                      abiPtr 32)) :: toVEnv env := by
            rw [VEnv.set_cons_ne (identV_ne_extOk d d).symm,
              VEnv.set_cons_ne (identV_ne_extTok d d).symm, VEnv.set_head]
          have hval : suffixVal (I.abi meth).ret
              (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) =
              BitVec.ofNat 256 retv := by
            cases hrt : (I.abi meth).ret
            · simp [suffixVal, decodeRet, hrt, finishCall_returndata] at hdec ⊢
              rcases hdec with ⟨hlen, _, hto⟩
              rw [hmload hlen]
              have hv : (wordFrom resp.returndata 0).toNat < wordBound := by
                simpa [wordBound] using (wordFrom resp.returndata 0).isLt
              exact (BitVec.eq_of_toNat_eq (toNat_ofNat_of_lt hv)).symm.trans
                (congrArg (BitVec.ofNat 256) hto)
            · simp [suffixVal, decodeRet, hrt] at hdec ⊢
              simp [hdec.1]
            · rcases hbd.hret with h | h <;> simp [h] at hrt
          have hVS :
              VS = VEnv.set
                ((extOk d, resp.flag) :: (extTok d,
                    BitVec.ofNat 256 (bind.addr w.self)) ::
                  (identV d, (0 : U256)) :: toVEnv env)
                (identV d)
                (suffixVal (I.abi meth).ret
                  (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)) := by
            simpa using hVeq
          have hVeq' : V' = toVEnv (retv :: env) := by
            rw [hrestore, ← hVSeq, hVS, hset, hval, toVEnv_cons]
            exact restore_call_result
          have hvlt : retv < wordBound := by
            cases hrt : (I.abi meth).ret
            · simp [decodeRet, hrt] at hdec
              rw [← hdec.2.2]
              simpa [wordBound] using (wordFrom resp.returndata 0).isLt
            · simp [decodeRet, hrt] at hdec
              simp [hdec.1]; decide
            · rcases hbd.hret with h | h <;> simp [h] at hrt
          have hR2 := R_finishCall_success (α := α) (callee := bind.addr w.self)
            (iOff := abiPtr) (iSz := 4 + 32 * args.length)
            (oOff := abiPtr) (oSz := 32)
            (R_memOnly hR hMO) hsucc hni
          have hR3 := R_memOnly hR2 hMOS
          rw [hstSeq] at hR3 hMOS hCWS
          have hctx2 := ctxRel_finishCall (ctxRel_memOnly hctx hMO) .call
            resp abiPtr (4 + 32 * args.length) abiPtr 32
          have hRX2 := RX_finishCall_success (iOff := abiPtr)
            (iSz := 4 + 32 * args.length) (oOff := abiPtr) (oSz := 32)
            hα hsucc hg hni hbd.hgetset
          refine ⟨retv, { w₁ with ext := bind.set w₁.ext g', ncalls := w₁.ncalls + 1 },
            hrun, hoeq.symm.trans hoS, hVeq',
            ⟨hVeq', envWF_cons hvlt henv,
              R_with_ghost (bind.set w.ext g') (w.ncalls + 1) w₁.faults hR3,
              ctxRel_memOnly hctx2 hMOS⟩, ?_⟩
          unfold RX at hRX2 ⊢
          rw [α.ofState_proj, hCWS, ← α.ofState_proj]
          exact hRX2

end Lsc.Compiler
