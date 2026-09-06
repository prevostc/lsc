import Lsc.Compiler.Proof.Layout
import Lsc.Compiler.Proof.Emit
import YulSemantics.BigStep

set_option linter.unusedSimpArgs false

/-!
M1 operator / statement simulation: `load`, `addChecked`, `store`, `emit` (one word), `stop`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

def M1Op : Lsc.Op → Prop
  | .load _ | .loadMap _ _ | .loadMap2 _ _ _ => True
  | .sender | .value | .timestamp | .blockNumber | .selfAddress => True
  | .addChecked _ _ | .subChecked _ _ | .mulChecked _ _ | .divChecked _ _ => True
  | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .pure _ => True
  | _ => False

def M1Cond : Lsc.Cond → Prop
  | _ => True

def M1Stmt : Lsc.Stmt → Prop
  | .store _ _ | .storeMap _ _ _ | .storeMap2 _ _ _ _ => True
  | .emit _ args => args.length = 0 ∨ args.length = 1 ∨ args.length = 3
  | .require c _ args => M1Cond c ∧ args.length = 0
  | .revert _ args => args.length = 0
  | _ => False

theorem memOnly_mstore (st : EvmState) (p v : U256) :
    MemOnly st { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v } := by
  simp [MemOnly, touchMemory]

theorem emitLet_stmts (e : Emit) (n : YIdent) (x : YExpr) :
    (emitLet e n x).stmts = e.stmts ++ [.letDecl [n] (some x)] :=
  Emit.stmts_push _ _

theorem emitDo_stmts (e : Emit) (op : YOp) (args : List YExpr) :
    (emitDo e op args).stmts =
      e.stmts ++ [.exprStmt (YulSemantics.Expr.builtin (Op := YOp) op args)] :=
  Emit.stmts_push _ _

theorem emitIf_stmts (e : Emit) (cnd : YExpr) (body : YBlock) :
    (emitIf e cnd body).stmts = e.stmts ++ [.cond cnd body] :=
  Emit.stmts_push _ _

theorem emitLetOp_load (c : ContractDef) (e : Emit) (d f : Nat) :
    emitLetOp c e d (.load f) =
      some (emitLet e (identV d) (bop Op.sload [lit f])) := rfl

theorem emitLetOp_addChecked (c : ContractDef) (e : Emit) (d : Nat) (a b : Atom) :
    emitLetOp c e d (.addChecked a b) =
      some (emitAddChecked e (identV d) (atomE d a) (atomE d b)) := rfl

theorem emitLetOp_subChecked (c : ContractDef) (e : Emit) (d : Nat) (a b : Atom) :
    emitLetOp c e d (.subChecked a b) =
      some (emitSubChecked e (identV d) (atomE d a) (atomE d b)) := rfl

theorem emitLetOp_pure (c : ContractDef) (e : Emit) (d : Nat) (a : Atom) :
    emitLetOp c e d (.pure a) = some (emitLet e (identV d) (atomE d a)) := rfl

theorem emitAddChecked_stmts (e : Emit) (name : YIdent) (a b : YExpr) :
    (emitAddChecked e name a b).stmts =
      e.stmts ++
        [.letDecl [name] (some (bop Op.add [a, b])),
          .cond (bop Op.lt [var name, a]) (emitPanic {} 0x11).stmts] := by
  simp [emitAddChecked, emitLet_stmts, emitIf_stmts]

theorem emitStmt_store (c : ContractDef) (e : Emit) (d f : Nat) (v : Atom) :
    (emitStmt c e d (.store f v)).stmts =
      e.stmts ++ [.exprStmt (bop Op.sstore [lit f, atomE d v])] :=
  emitDo_stmts _ _ _

theorem emitLog1_one (e : Emit) (topic : Nat) (a : YExpr) :
    (emitLog1 e topic [a]).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, a]),
          .exprStmt (bop Op.log1 [lit abiPtr, lit 32, lit topic])] := by
  simp [emitLog1, emitDo, Emit.push, Emit.stmts]
  constructor <;> rfl

theorem emitStmt_emit_one (c : ContractDef) (e : Emit) (d ev : Nat) (a : Atom)
    {ed : EventDef} (h : c.events[ev]? = some ed) :
    (emitStmt c e d (.emit ev [a])).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, atomE d a]),
          .exprStmt (bop Op.log1 [lit abiPtr, lit 32, lit ed.topic0])] := by
  simp [emitStmt, h, emitLog1_one]

theorem toNat_abiPtr : (BitVec.ofNat 256 abiPtr).toNat = abiPtr :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_abiAfterSel : (BitVec.ofNat 256 abiAfterSel).toNat = abiAfterSel :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_36 : (BitVec.ofNat 256 36).toNat = 36 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_32 : (BitVec.ofNat 256 32).toNat = 32 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_224 : (BitVec.ofNat 256 224).toNat = 224 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem step_add (st : EvmState) (a b : U256) :
    stepOp Op.add [a, b] st = some (.ok [a + b] st) := rfl

theorem step_lt (st : EvmState) (a b : U256) :
    stepOp Op.lt [a, b] st = some (.ok [b2w (a.ult b)] st) := rfl

theorem step_shl (st : EvmState) (shift val : U256) :
    stepOp Op.shl [shift, val] st = some (.ok [val <<< shift.toNat] st) := rfl

theorem step_sload (st : EvmState) (k : U256) :
    stepOp Op.sload [k] st = some (.ok [st.storage k] st) := rfl

theorem evm_litValue_number (n : Nat) :
    evm.litValue (.number n) = BitVec.ofNat 256 n := rfl

theorem step_sstore (st : EvmState) (k v : U256) (h : st.env.static = false) :
    stepOp Op.sstore [k, v] st = some (.ok []
      { st with
        storage := upd st.storage k v
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address k v } }) := by
  simp only [stepOp, guardStatic, h]
  rw [if_neg Bool.false_ne_true]

theorem step_log1 (st : EvmState) (p n t : U256) (h : st.env.static = false) :
    stepOp Op.log1 [p, n, t] st = some (.ok [] (appendLog st [t] p n)) := by
  simp only [stepOp, guardStatic, h]
  rw [if_neg Bool.false_ne_true]

theorem step_mstore (st : EvmState) (p v : U256) :
    stepOp Op.mstore [p, v] st = some (.ok []
      { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v }) := rfl

theorem step_revert (st : EvmState) (p s : U256) :
    stepOp Op.revert [p, s] st = some (.halt
      { touchMemory st p.toNat s.toNat with
        halted := some (.revert, readBytes st.memory p.toNat s.toNat) }) := rfl

theorem step_stop (st : EvmState) :
    stepOp Op.stop [] st = some (.halt { st with halted := some (.stop, []) }) := rfl

theorem stop_sim (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmts evm funs V st [stopStmt] V { st with halted := some (.stop, []) } .halt :=
  Step.seqStop (Step.exprStmtHalt (Step.builtinHalt Step.argsNil (step_stop _)))
    halt_ne_normal

/-- Overflow / underflow Panic block. Revert path exposes only `halted`. -/
theorem panic_sim (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (code : Nat)
    (hcode : code < wordBound) :
    ∃ st', ExecStmts evm funs V st (emitPanic {} code).stmts V st' .halt ∧
      st'.halted = some (.revert, panicBytes code) := by
  simp only [emitPanic, emitDo, Emit.push, Emit.stmts, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  let vSel : U256 := BitVec.ofNat 256 panicSelector <<< 224
  let st1 : EvmState :=
    { touchMemory st abiPtr 32 with memory := storeWord st.memory abiPtr vSel }
  let st2 : EvmState :=
    { touchMemory st1 abiAfterSel 32 with
      memory := storeWord st1.memory abiAfterSel (BitVec.ofNat 256 code) }
  let bytes := readBytes st2.memory abiPtr 36
  let st3 : EvmState :=
    { touchMemory st2 abiPtr 36 with halted := some (.revert, bytes) }
  refine ⟨st3, ?_, ?_⟩
  · have hshl :
        EvalExpr evm funs V st (bop Op.shl [lit 224, lit panicSelector])
          (.vals [vSel] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
        (by
          simp only [evm_litValue_number, step_shl, toNat_224]
          rfl)
    have hm1 :
        ExecStmt evm funs V st
          (.exprStmt (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit panicSelector]]))
          V st1 .normal :=
      Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hshl) Step.lit)
        (by
          simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
          rfl))
    have hm2 :
        ExecStmt evm funs V st1
          (.exprStmt (bop Op.mstore [lit abiAfterSel, lit code]))
          V st2 .normal :=
      Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
        (by
          simp only [evm_litValue_number, step_mstore, toNat_abiAfterSel]
          rfl))
    have hrev :
        ExecStmt evm funs V st2
          (.exprStmt (bop Op.revert [lit abiPtr, lit 36]))
          V st3 .halt :=
      Step.exprStmtHalt (Step.builtinHalt
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
        (by
          simp only [evm_litValue_number, step_revert, toNat_abiPtr, toNat_36]
          rfl))
    exact Step.seqCons hm1 (Step.seqCons hm2 (Step.seqStop hrev halt_ne_normal))
  · have hhalt : st3.halted = some (.revert, readBytes st2.memory abiPtr 36) := rfl
    rw [hhalt]
    refine congrArg (fun b => some (HaltKind.revert, b)) ?_
    have hmem : st2.memory =
        storeWord (storeWord st.memory abiPtr vSel) abiAfterSel (BitVec.ofNat 256 code) := rfl
    rw [hmem, show vSel = BitVec.ofNat 256 panicSelector <<< 224 from rfl]
    exact panicBytes_mem st.memory code hcode

theorem op_sim_load {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.load f) = true) :
    let v := Γ.st.scalar f w.self
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop Op.sload [lit f])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env) ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv with ⟨hV, henv, ⟨hs, hl, hκe, hW⟩, hctx⟩
  have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.scalar).mp (by simpa [opWF] using hwf)
  have hslot : st.storage (BitVec.ofNat 256 f) = BitVec.ofNat 256 (Γ.st.scalar f w.self) := by
    have := hs f fd hfd
    simpa [hk] using this
  have hv : Γ.st.scalar f w.self < wordBound := by
    have := hW f fd hfd
    simpa [hk] using this
  refine ⟨st, ?_, ?_⟩
  · simp only [emitLet, Emit.push, Emit.stmts, List.reverse_cons, List.reverse_nil, List.nil_append]
    have hsload :
        EvalExpr evm funs V st (bop Op.sload [lit f])
          (.vals [st.storage (BitVec.ofNat 256 f)] st) :=
      Step.builtinOk (Step.argsCons Step.argsNil Step.lit)
        (by
          simp only [step_sload]
          rw [litValue_number])
    have hlet :
        ExecStmt evm funs V st
          (.letDecl [identV env.length]
            (some (bop Op.sload [lit f])))
          ((identV env.length, st.storage (BitVec.ofNat 256 f)) :: V) st .normal :=
      Step.letVal hsload rfl
    rw [hslot] at hlet
    exact Step.seqCons hlet Step.seqNil
  · refine ⟨?_, envWF_cons hv henv, ⟨hs, hl, hκe, hW⟩, hctx⟩
    rw [hV, toVEnv_cons]

theorem op_sim_addChecked {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.addChecked a b) = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.addChecked a b)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitAddChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitAddChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : atomWF a = true ∧ atomWF b = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ha := atom_eval_lt henv hwf'.1
  have hb := atom_eval_lt henv hwf'.2
  have hn0 : identsNodup env.length = true := identsNodup_mono (by omega) hn
  have hea := eval_atom funs (st := st) hV hn0 a
  have heb := eval_atom funs (st := st) hV hn0 b
  have hadd :
      EvalExpr evm funs V st
        (bop Op.add [atomE env.length a, atomE env.length b])
        (.vals [BitVec.ofNat 256 (a.eval env) + BitVec.ofNat 256 (b.eval env)] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_add _ _ _)
  rw [ofNat_add] at hadd
  let V₁ := (identV env.length, BitVec.ofNat 256 (a.eval env + b.eval env)) :: V
  have hlet : ExecStmt evm funs V st
      (.letDecl [identV env.length]
        (some (bop Op.add [atomE env.length a, atomE env.length b])))
      V₁ st .normal :=
    Step.letVal hadd rfl
  have hlt :
      EvalExpr evm funs V₁ st
        (bop Op.lt [var (identV env.length), atomE env.length a])
        (.vals [b2w ((BitVec.ofNat 256 (a.eval env + b.eval env)).ult
          (BitVec.ofNat 256 (a.eval env)))] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil
          (eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env + b.eval env)) hV hn a))
        (Step.var (by
          simp only [V₁]
          rw [VEnv.get_cons, if_pos rfl])))
      (step_lt _ _ _)
  simp only [Op.denote, Tx.run_addChecked]
  split_ifs with hsum
  · simp
    have hult :
        (BitVec.ofNat 256 (a.eval env + b.eval env)).ult (BitVec.ofNat 256 (a.eval env))
          = false := by
      rw [ult_ofNat hsum ha]
      simp [Nat.not_lt.mpr (Nat.le_add_right _ _)]
    refine ⟨st, ?_, ?_⟩
    · simp only [emitAddChecked_stmts, Emit.stmts_nil, List.nil_append]
      refine Step.seqCons hlet (Step.seqCons (Step.ifFalse hlt ?_) Step.seqNil)
      simp [hult, b2w, Dialect.zero, litValue]
    · exact ⟨by rw [hV, toVEnv_cons], envWF_cons hsum henv, hR, hctx⟩
  · simp
    have hult :
        (BitVec.ofNat 256 (a.eval env + b.eval env)).ult (BitVec.ofNat 256 (a.eval env))
          = true := by
      have hiff := ult_add_overflow ha hb
      rw [ofNat_add] at hiff
      exact hiff.mpr (Nat.le_of_not_gt hsum)
    have hcode : (0x11 : Nat) < wordBound := lt_256_wordBound (by decide)
    obtain ⟨st', hp, hh⟩ := panic_sim ([] :: funs) V₁ st 0x11 hcode
    have hif :
        ExecStmt evm funs V₁ st
          (.cond (bop Op.lt [var (identV env.length), atomE env.length a])
            (emitPanic {} 0x11).stmts) V₁ st' .halt := by
      refine Step.ifTrue (D := evm) hlt ?_ ?_
      · simp [hult, b2w, Dialect.zero, litValue]
      · have inner :
            ExecStmts evm (hoist evm (emitPanic {} 0x11).stmts :: funs) V₁ st
              (emitPanic {} 0x11).stmts V₁ st' .halt := by
          rw [hoist_panic]
          exact hp
        simpa [restore_self] using Step.block (D := evm) inner
    have hexec :
        ExecStmts evm funs V st
          (emitAddChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
          V₁ st' .halt := by
      simp only [emitAddChecked_stmts, Emit.stmts_nil, List.nil_append]
      exact Step.seqCons hlet (Step.seqStop hif halt_ne_normal)
    exact ⟨V₁, st', hexec, panicBytes 0x11, hh, rfl⟩

theorem stmt_sim_store {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat} {val : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hwf : stmtWF c (.store f val) = true)
    (hn : identsNodup env.length = true) :
    let v := val.eval env
    let w' := { w with self := Γ.st.scalarUpd f w.self v }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.store f val)).stmts V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : fieldKindOK c f .scalar = true ∧ atomWF val = true := by
    simpa [stmtWF, Bool.and_eq_true] using hwf
  have hv := atom_eval_lt henv hwf'.2
  have hstatic := ctxRel_static hctx
  have hev := eval_atom funs (st := st) hV hn val
  let st' :=
    { st with
      storage := upd st.storage (BitVec.ofNat 256 f) (BitVec.ofNat 256 (val.eval env))
      env := { st.env with
        storageOf := updAccount st.env.storageOf st.env.address
          (BitVec.ofNat 256 f) (BitVec.ofNat 256 (val.eval env)) } }
  refine ⟨st', ?_, ?_⟩
  · simp only [emitStmt_store, Emit.stmts_nil, List.nil_append]
    refine Step.seqCons (Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hev) Step.lit)
      (by
        simp only [evm_litValue_number, step_sstore st _ _ hstatic]
        rfl))) Step.seqNil
  · exact ⟨hV, henv, R_sstore hR hctx hΓ hκ hlen hwf'.1 hv, ctxRel_sstore hctx _ _⟩

theorem stmt_sim_emit {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {ev : Nat} {a : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : stmtWF c (.emit ev [a]) = true)
    (hn : identsNodup env.length = true) :
    let args := [a.eval env]
    let w' := { w with log := w.log ++ [Γ.ev.build ev args] }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.emit ev [a])).stmts V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : eventOK c ev 1 = true ∧ atomWF a = true := by
    simpa [stmtWF, Bool.and_eq_true] using hwf
  have ⟨ed, hed, _hplen⟩ := (eventOK_iff c ev 1).mp hwf'.1
  have hev : ev < c.events.length := (List.getElem?_eq_some_iff.mp hed).1
  have hv := atom_eval_lt henv hwf'.2
  have hstatic := ctxRel_static hctx
  have hea := eval_atom funs (st := st) hV hn a
  have hptr := toNat_abiPtr
  have hn32 := toNat_32
  let stM :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr (BitVec.ofNat 256 (a.eval env)) }
  have hmstore :
      ExecStmt evm funs V st
        (.exprStmt (bop Op.mstore [lit abiPtr, atomE env.length a])) V stM .normal := by
    refine Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hea) Step.lit) ?_)
    simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
    rfl
  let stL := appendLog stM [BitVec.ofNat 256 ed.topic0]
    (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 32)
  have hstaticM : stM.env.static = false := by
    simp [stM, touchMemory, hstatic]
  have hlog :
      ExecStmt evm funs V stM
        (.exprStmt (bop Op.log1 [lit abiPtr, lit 32, lit ed.topic0])) V stL .normal := by
    refine Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) Step.lit) ?_)
    simp only [litValue, step_log1 stM _ _ _ hstaticM]
    rfl
  refine ⟨stL, ?_, ?_⟩
  · simp only [emitStmt_emit_one (h := hed), Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hmstore (Step.seqCons hlog Step.seqNil)
  · have hR' : R c Γ κ { w with log := w.log ++ [Γ.ev.build ev [a.eval env]] } stL := by
      rcases hR with ⟨hs, hl, hk, hW⟩
      have hl' := logsRel_emit (c := c) (Γ := Γ) (st := stM) (args := [a.eval env])
        (by
          unfold logsRel at hl ⊢
          simp [stM, touchMemory]
          exact hl) hev
      have hdata :
          readBytes stM.memory abiPtr 32 = abiBytes [a.eval env] := by
        simp [stM, abiBytes_singleton, readBytes_storeWord_wordBytes _ _ _ hv]
      have : stL.logs = stM.logs ++
          [LogEntry.mk stM.env.address [BitVec.ofNat 256 ed.topic0]
            (readBytes stM.memory abiPtr 32)] := by
        simp [stL, appendLog, hptr, hn32]
      have haddr : stL.env.address = stM.env.address := by
        simp [stL, appendLog, touchMemory]
      refine ⟨?_, ?_, ?_, hW⟩
      · simpa [stL, appendLog, touchMemory, stM] using hs
      · unfold logsRel at hl' ⊢
        simp [this, haddr, hdata, stM, touchMemory] at hl' ⊢
        -- `c.events[ev] = ed`
        have hget : c.events[ev] = ed := (List.getElem?_eq_some_iff.mp hed).2
        simpa [hget, hdata, abiBytes_singleton] using hl'
      · simpa [stL, appendLog, touchMemory, stM] using hk
    exact ⟨hV, henv, hR',
      ctxRel_appendLog (st := stM)
        (ctxRel_memOnly hctx (by simp [MemOnly, stM, touchMemory]))
        [BitVec.ofNat 256 ed.topic0]
        (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 32)⟩

end Lsc.Compiler
