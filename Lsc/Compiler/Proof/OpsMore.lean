import Lsc.Compiler.Proof.Ops

set_option linter.unusedSimpArgs false

/-!
Counter-fragment simulation: `subChecked`, 0-arg `require`, `eq`/`ne`, one-word `return`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem toNat_4 : (BitVec.ofNat 256 4).toNat = 4 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem step_sub (st : EvmState) (a b : U256) :
    stepOp Op.sub [a, b] st = some (.ok [a - b] st) := rfl

theorem step_eq (st : EvmState) (a b : U256) :
    stepOp Op.eq [a, b] st = some (.ok [b2w (a = b)] st) := rfl

theorem step_iszero (st : EvmState) (a : U256) :
    stepOp Op.iszero [a] st = some (.ok [b2w (a = 0)] st) := rfl

theorem step_ret (st : EvmState) (p s : U256) :
    stepOp Op.ret [p, s] st = some (.halt
      { touchMemory st p.toNat s.toNat with
        halted := some (.ret, readBytes st.memory p.toNat s.toNat) }) := rfl

theorem emitSubChecked_stmts (e : Emit) (name : YIdent) (a b : YExpr) :
    (emitSubChecked e name a b).stmts =
      e.stmts ++
        [.cond (bop Op.lt [a, b]) (emitPanic {} 0x11).stmts,
          .letDecl [name] (some (bop Op.sub [a, b]))] := by
  simp [emitSubChecked, emitIf_stmts, emitLet_stmts]

theorem emitStmt_require (c : ContractDef) (e : Emit) (d : Nat)
    (cond : Cond) (err : Nat) (args : List Atom) :
    (emitStmt tag c e d (.require cond err args)).stmts =
      e.stmts ++
        [.cond (bop Op.iszero [emitCond tag d cond])
          (emitCustomError c {} err (args.map (atomE tag d))).stmts] :=
  emitIf_stmts _ _ _

theorem emitCustomError_nil_stmts (c : ContractDef) (err : Nat) {ed : ErrorDef}
    (h : c.errors[err]? = some ed) :
    (emitCustomError c {} err []).stmts =
      [.exprStmt (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit ed.selector]]),
        .exprStmt (bop Op.revert [lit abiPtr, lit 4])] := by
  simp [emitCustomError, h, emitDo, Emit.push, Emit.stmts]
  constructor <;> rfl

theorem emitReturnWords_one (e : Emit) (x : YExpr) :
    (emitReturnWords e [x]).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, x]),
          .exprStmt (bop Op.ret [lit abiPtr, lit 32])] := by
  simp [emitReturnWords, emitDo, Emit.push, Emit.stmts]
  constructor <;> rfl

theorem b2w_decide_eq {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    b2w (BitVec.ofNat 256 a = BitVec.ofNat 256 b) = b2w (decide (a = b)) := by
  have hiff := ofNat_eq_iff ha hb
  cases h : decide (a = b)
  · have : a ≠ b := of_decide_eq_false h
    have : ¬ BitVec.ofNat 256 a = BitVec.ofNat 256 b := mt hiff.mp this
    simp [this, b2w]
  · have : a = b := of_decide_eq_true h
    simp [this, b2w]

theorem step_and (st : EvmState) (a b : U256) :
    stepOp Op.and [a, b] st = some (.ok [a &&& b] st) := rfl

theorem step_or (st : EvmState) (a b : U256) :
    stepOp Op.or [a, b] st = some (.ok [a ||| b] st) := rfl

theorem b2w_iszero (c : Bool) :
    b2w (b2w c = 0) = b2w (!c) := by
  cases c <;> simp [b2w]

theorem b2w_decide_not (p : Prop) [Decidable p] :
    b2w (!decide p) = b2w (decide (¬ p)) := by
  by_cases h : p <;> simp [h, b2w]

theorem b2w_decide_and (p q : Prop) [Decidable p] [Decidable q] :
    b2w (decide p && decide q) = b2w (decide (p ∧ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, b2w]

theorem b2w_decide_or (p q : Prop) [Decidable p] [Decidable q] :
    b2w (decide p || decide q) = b2w (decide (p ∨ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, b2w]

theorem eval_cond tag {env : List Nat} {V : VEnv evm} {st : EvmState} {c : Cond}
    (funs : FunEnv evm) (hV : V = toVEnv tag env) (henv : EnvWF env)
    (hn : identsNodup tag env.length = true) (_hC : M1Cond c)
    (hwf : condWF c = true) :
    EvalExpr evm funs V st (emitCond tag env.length c)
      (.vals [b2w (decide (c.denote env))] st) := by
  revert _hC hwf
  induction c <;> intro _hC hwf
  case eq a b =>
    have hwf' : atomWF a = true ∧ atomWF b = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have ha := atom_eval_lt henv hwf'.1
    have hb := atom_eval_lt henv hwf'.2
    have hea := eval_atom tag funs (st := st) hV hn a
    have heb := eval_atom tag funs (st := st) hV hn b
    have heq :
        EvalExpr evm funs V st (bop Op.eq [atomE tag env.length a, atomE tag env.length b])
          (.vals [b2w (BitVec.ofNat 256 (a.eval env) = BitVec.ofNat 256 (b.eval env))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_eq _ _ _)
    rw [b2w_decide_eq ha hb] at heq
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    exact heq
  case ne a b =>
    have hwf' : atomWF a = true ∧ atomWF b = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have ha := atom_eval_lt henv hwf'.1
    have hb := atom_eval_lt henv hwf'.2
    have hea := eval_atom tag funs (st := st) hV hn a
    have heb := eval_atom tag funs (st := st) hV hn b
    have heq :
        EvalExpr evm funs V st (bop Op.eq [atomE tag env.length a, atomE tag env.length b])
          (.vals [b2w (BitVec.ofNat 256 (a.eval env) = BitVec.ofNat 256 (b.eval env))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_eq _ _ _)
    rw [b2w_decide_eq ha hb] at heq
    have hisz :
        EvalExpr evm funs V st
          (bop Op.iszero [bop Op.eq [atomE tag env.length a, atomE tag env.length b]])
          (.vals [b2w (b2w (decide (a.eval env = b.eval env)) = 0)] st) :=
      Step.builtinOk (Step.argsCons Step.argsNil heq) (step_iszero _ _)
    rw [b2w_iszero, b2w_decide_not] at hisz
    simp only [emitCond]
    exact hisz
  case lt a b =>
    have hwf' : atomWF a = true ∧ atomWF b = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have ha := atom_eval_lt henv hwf'.1
    have hb := atom_eval_lt henv hwf'.2
    have hea := eval_atom tag funs (st := st) hV hn a
    have heb := eval_atom tag funs (st := st) hV hn b
    have hlt :
        EvalExpr evm funs V st (bop Op.lt [atomE tag env.length a, atomE tag env.length b])
          (.vals [b2w ((BitVec.ofNat 256 (a.eval env)).ult (BitVec.ofNat 256 (b.eval env)))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_lt _ _ _)
    rw [ult_ofNat ha hb] at hlt
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    exact hlt
  case le a b =>
    have hwf' : atomWF a = true ∧ atomWF b = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have ha := atom_eval_lt henv hwf'.1
    have hb := atom_eval_lt henv hwf'.2
    have hea := eval_atom tag funs (st := st) hV hn a
    have heb := eval_atom tag funs (st := st) hV hn b
    have hlt :
        EvalExpr evm funs V st (bop Op.lt [atomE tag env.length b, atomE tag env.length a])
          (.vals [b2w ((BitVec.ofNat 256 (b.eval env)).ult (BitVec.ofNat 256 (a.eval env)))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hea) heb) (step_lt _ _ _)
    rw [ult_ofNat hb ha] at hlt
    have hisz :
        EvalExpr evm funs V st
          (bop Op.iszero [bop Op.lt [atomE tag env.length b, atomE tag env.length a]])
          (.vals [b2w (b2w (decide (b.eval env < a.eval env)) = 0)] st) :=
      Step.builtinOk (Step.argsCons Step.argsNil hlt) (step_iszero _ _)
    rw [b2w_iszero] at hisz
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    have hdec : (!decide (b.eval env < a.eval env)) = decide (a.eval env ≤ b.eval env) := by
      by_cases h : b.eval env < a.eval env
      · rw [decide_eq_true h, Bool.not_true, decide_eq_false (Nat.not_le.mpr h)]
      · rw [decide_eq_false h, Bool.not_false, decide_eq_true (Nat.le_of_not_gt h)]
    rw [hdec] at hisz
    exact hisz
  case and c d ihc ihd =>
    have hwf' : condWF c = true ∧ condWF d = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have hec := ihc trivial hwf'.1
    have hed := ihd trivial hwf'.2
    have hand :
        EvalExpr evm funs V st (bop Op.and [emitCond tag env.length c, emitCond tag env.length d])
          (.vals [b2w (decide (c.denote env)) &&& b2w (decide (d.denote env))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hed) hec) (step_and _ _ _)
    rw [b2w_and, b2w_decide_and] at hand
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    exact hand
  case or c d ihc ihd =>
    have hwf' : condWF c = true ∧ condWF d = true := by
      simpa [condWF, Bool.and_eq_true] using hwf
    have hec := ihc trivial hwf'.1
    have hed := ihd trivial hwf'.2
    have hor :
        EvalExpr evm funs V st (bop Op.or [emitCond tag env.length c, emitCond tag env.length d])
          (.vals [b2w (decide (c.denote env)) ||| b2w (decide (d.denote env))] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hed) hec) (step_or _ _ _)
    rw [b2w_or, b2w_decide_or] at hor
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    exact hor
  case not c ih =>
    have hc := ih trivial (by simpa [condWF] using hwf)
    have hisz :
        EvalExpr evm funs V st (bop Op.iszero [emitCond tag env.length c])
          (.vals [b2w (b2w (decide (c.denote env)) = 0)] st) :=
      Step.builtinOk (Step.argsCons Step.argsNil hc) (step_iszero _ _)
    rw [b2w_iszero, b2w_decide_not] at hisz
    simp only [emitCond, Cond.denote, Cond.instDecidable]
    exact hisz
  case tt =>
    simp only [emitCond, Cond.denote, Cond.instDecidable, decide_true, b2w]
    exact Step.lit
  case ff =>
    simp only [emitCond, Cond.denote, Cond.instDecidable, decide_false, b2w]
    exact Step.lit


theorem eval_iszero_cond tag {env : List Nat} {V : VEnv evm} {st : EvmState} {c : Cond}
    (funs : FunEnv evm) (hV : V = toVEnv tag env) (henv : EnvWF env)
    (hn : identsNodup tag env.length = true) (hC : M1Cond c)
    (hwf : condWF c = true) :
    EvalExpr evm funs V st (bop Op.iszero [emitCond tag env.length c])
      (.vals [b2w (decide (¬ c.denote env))] st) := by
  have hc := eval_cond tag (st := st) funs hV henv hn hC hwf
  have hisz :
      EvalExpr evm funs V st (bop Op.iszero [emitCond tag env.length c])
        (.vals [b2w (b2w (decide (c.denote env)) = 0)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil hc) (step_iszero _ _)
  have hbool :
      b2w (b2w (decide (c.denote env)) = 0) = b2w (decide (¬ c.denote env)) := by
    cases h : decide (c.denote env) <;> simp [b2w, h, decide_not]
  rw [hbool] at hisz
  exact hisz

theorem customError_nil_sim (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (c : ContractDef) (err : Nat) {ed : ErrorDef}
    (h : c.errors[err]? = some ed) :
    ∃ st', ExecStmts evm funs V st (emitCustomError c {} err []).stmts V st' .halt ∧
      st'.halted = some (.revert, selectorBytes ed.selector) := by
  have hsel : ed.selector < 2 ^ 32 := by
    simpa [ErrorDef.selector] using selectorOf_lt ed.name ed.params
  let vSel : U256 := BitVec.ofNat 256 ed.selector <<< 224
  let st1 : EvmState :=
    { touchMemory st abiPtr 32 with memory := storeWord st.memory abiPtr vSel }
  let bytes := readBytes st1.memory abiPtr 4
  let st2 : EvmState :=
    { touchMemory st1 abiPtr 4 with halted := some (.revert, bytes) }
  refine ⟨st2, ?_, ?_⟩
  · have hshl :
        EvalExpr evm funs V st (bop Op.shl [lit 224, lit ed.selector])
          (.vals [vSel] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
        (by
          simp only [evm_litValue_number, step_shl, toNat_224]
          rfl)
    have hm :
        ExecStmt evm funs V st
          (.exprStmt (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit ed.selector]]))
          V st1 .normal :=
      Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hshl) Step.lit)
        (by
          simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
          rfl))
    have hrev :
        ExecStmt evm funs V st1 (.exprStmt (bop Op.revert [lit abiPtr, lit 4]))
          V st2 .halt :=
      Step.exprStmtHalt (Step.builtinHalt
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
        (by
          simp only [evm_litValue_number, step_revert, toNat_abiPtr, toNat_4]
          rfl))
    simp only [emitCustomError_nil_stmts (h := h)]
    exact Step.seqCons hm (Step.seqStop hrev halt_ne_normal)
  · have hhalt : st2.halted = some (.revert, readBytes st1.memory abiPtr 4) := rfl
    rw [hhalt]
    refine congrArg (fun b => some (HaltKind.revert, b)) ?_
    simp [st1]
    exact selectorBytes_mem st.memory ed.selector hsel

theorem op_sim_subChecked {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b : Atom}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hwf : opWF c (.subChecked a b) = true)
    (hn : identsNodup tag (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.subChecked a b)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitSubChecked {} (identV tag env.length) (atomE tag env.length a) (atomE tag env.length b)).stmts
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv tag Γ c κ ctx w' (v :: env)
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitSubChecked {} (identV tag env.length) (atomE tag env.length a) (atomE tag env.length b)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : atomWF a = true ∧ atomWF b = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ha := atom_eval_lt henv hwf'.1
  have hb := atom_eval_lt henv hwf'.2
  have hn0 : identsNodup tag env.length = true := identsNodup_mono tag (by omega) hn
  have hea := eval_atom tag funs (st := st) hV hn0 a
  have heb := eval_atom tag funs (st := st) hV hn0 b
  have hlt :
      EvalExpr evm funs V st
        (bop Op.lt [atomE tag env.length a, atomE tag env.length b])
        (.vals [b2w ((BitVec.ofNat 256 (a.eval env)).ult (BitVec.ofNat 256 (b.eval env)))] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_lt _ _ _)
  simp only [Op.denote, Tx.run_subChecked]
  split_ifs with hle
  · simp
    have hult :
        (BitVec.ofNat 256 (a.eval env)).ult (BitVec.ofNat 256 (b.eval env)) = false := by
      rw [ult_ofNat ha hb]
      simp [Nat.not_lt.mpr hle]
    have hsub :
        EvalExpr evm funs V st
          (bop Op.sub [atomE tag env.length a, atomE tag env.length b])
          (.vals [BitVec.ofNat 256 (a.eval env) - BitVec.ofNat 256 (b.eval env)] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_sub _ _ _)
    rw [ofNat_sub_of_le hle ha] at hsub
    let V₁ := (identV tag env.length, BitVec.ofNat 256 (a.eval env - b.eval env)) :: V
    have hlet : ExecStmt evm funs V st
        (.letDecl [identV tag env.length]
          (some (bop Op.sub [atomE tag env.length a, atomE tag env.length b])))
        V₁ st .normal :=
      Step.letVal hsub rfl
    refine ⟨st, ?_, ?_⟩
    · simp only [emitSubChecked_stmts, Emit.stmts_nil, List.nil_append]
      refine Step.seqCons (Step.ifFalse hlt ?_) (Step.seqCons hlet Step.seqNil)
      simp [hult, b2w, Dialect.zero, litValue]
    · exact ⟨by rw [hV, toVEnv_cons],
        envWF_cons (Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha) henv, hR, hctx⟩
  · simp
    have hult :
        (BitVec.ofNat 256 (a.eval env)).ult (BitVec.ofNat 256 (b.eval env)) = true := by
      rw [ult_ofNat ha hb]
      simp [Nat.lt_of_not_ge hle]
    have hcode : (0x11 : Nat) < wordBound := lt_256_wordBound (by decide)
    obtain ⟨st', hp, hh⟩ := panic_sim ([] :: funs) V st 0x11 hcode
    have hif :
        ExecStmt evm funs V st
          (.cond (bop Op.lt [atomE tag env.length a, atomE tag env.length b])
            (emitPanic {} 0x11).stmts) V st' .halt := by
      refine Step.ifTrue (D := evm) hlt ?_ ?_
      · simp [hult, b2w, Dialect.zero, litValue]
      · have inner :
            ExecStmts evm (hoist evm (emitPanic {} 0x11).stmts :: funs) V st
              (emitPanic {} 0x11).stmts V st' .halt := by
          rw [hoist_panic]
          exact hp
        simpa [restore_self] using Step.block (D := evm) inner
    have hexec :
        ExecStmts evm funs V st
          (emitSubChecked {} (identV tag env.length) (atomE tag env.length a) (atomE tag env.length b)).stmts
          V st' .halt := by
      simp only [emitSubChecked_stmts, Emit.stmts_nil, List.nil_append]
      exact Step.seqStop hif halt_ne_normal
    exact ⟨V, st', hexec, panicBytes 0x11, hh, rfl⟩

theorem stmt_sim_require {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {cond : Cond} {err : Nat}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hC : M1Cond cond)
    (hwf : stmtWF c (.require cond err []) = true)
    (hn : identsNodup tag env.length = true) :
    match Tx.run (Stmt.denote Γ env (.require cond err [])) ctx w with
    | .ok (_, w') =>
        ∃ st',
          ExecStmts evm funs V st (emitStmt tag c {} env.length (.require cond err [])).stmts
            V st' .normal ∧
          Inv tag Γ c κ ctx w' env V st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st (emitStmt tag c {} env.length (.require cond err [])).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : condWF cond = true ∧ errorOK c err 0 = true ∧ ([] : List Atom).all atomWF = true := by
    simpa [stmtWF, Bool.and_eq_true] using hwf
  have ⟨ed, hed, _⟩ := (errorOK_iff c err 0).mp hwf'.2.1
  have hisz := eval_iszero_cond tag (st := st) funs hV henv hn hC hwf'.1
  simp only [Stmt.denote, Tx.run_require]
  split_ifs with hc
  · simp
    have hz : decide (¬ cond.denote env) = false := by
      simp [hc]
    refine ⟨st, ?_, ⟨hV, henv, hR, hctx⟩⟩
    simp only [emitStmt_require, Emit.stmts_nil, List.nil_append]
    refine Step.seqCons (Step.ifFalse hisz ?_) Step.seqNil
    simp [hz, b2w, Dialect.zero, litValue]
  · simp
    have hz : decide (¬ cond.denote env) = true := by
      simp [hc]
    obtain ⟨st', hp, hh⟩ := customError_nil_sim ([] :: funs) V st c err hed
    have hif :
        ExecStmt evm funs V st
          (.cond (bop Op.iszero [emitCond tag env.length cond])
            (emitCustomError c {} err []).stmts) V st' .halt := by
      refine Step.ifTrue (D := evm) hisz ?_ ?_
      · simp [hz, b2w, Dialect.zero, litValue]
      · have inner :
            ExecStmts evm (hoist evm (emitCustomError c {} err []).stmts :: funs) V st
              (emitCustomError c {} err []).stmts V st' .halt := by
          rw [hoist_customError]
          exact hp
        simpa [restore_self] using Step.block (D := evm) inner
    refine ⟨V, st', ?_, selectorBytes ed.selector, hh, ?_⟩
    · simp only [emitStmt_require, Emit.stmts_nil, List.nil_append]
      exact Step.seqStop hif halt_ne_normal
    · exact ⟨err, [], rfl, (customErrorBytes_nil c hed).symm⟩

theorem return_word_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState}
    (funs : FunEnv evm) (V : VEnv evm)
    {x : YExpr} {v : Nat} (hv : v < wordBound)
    (he : EvalExpr evm funs V st x (.vals [BitVec.ofNat 256 v] st))
    (hR : R c Γ κ w st) :
    ∃ st', ExecStmts evm funs V st (emitReturnWords {} [x]).stmts V st' .halt ∧
      st'.halted = some (.ret, wordBytes v) ∧ R c Γ κ w st' := by
  let stM : EvmState :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr (BitVec.ofNat 256 v) }
  have hm :
      ExecStmt evm funs V st (.exprStmt (bop Op.mstore [lit abiPtr, x])) V stM .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil he) Step.lit)
      (by
        simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
        rfl))
  let bytes := readBytes stM.memory abiPtr 32
  let stR : EvmState :=
    { touchMemory stM abiPtr 32 with halted := some (.ret, bytes) }
  have hret :
      ExecStmt evm funs V stM (.exprStmt (bop Op.ret [lit abiPtr, lit 32])) V stR .halt :=
    Step.exprStmtHalt (Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
      (by
        simp only [evm_litValue_number, step_ret, toNat_abiPtr, toNat_32]
        rfl))
  refine ⟨stR, ?_, ?_, ?_⟩
  · simp only [emitReturnWords_one, Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hm (Step.seqStop hret halt_ne_normal)
  · have hhalt : stR.halted = some (.ret, readBytes stM.memory abiPtr 32) := rfl
    rw [hhalt]
    refine congrArg (fun b => some (HaltKind.ret, b)) ?_
    simp [stM, readBytes_storeWord_wordBytes _ _ _ hv]
  · exact R_touch_halted (R_memOnly hR (by simp [MemOnly, stM, touchMemory])) abiPtr 32 _

theorem emitReturnWords_two (e : Emit) (x y : YExpr) :
    (emitReturnWords e [x, y]).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, x]),
          .exprStmt (bop Op.mstore [lit (abiPtr + 32), y]),
          .exprStmt (bop Op.ret [lit abiPtr, lit 64])] := by
  simp [emitReturnWords, emitDo, Emit.push, Emit.stmts, bop]

theorem toNat_64_ops : (BitVec.ofNat 256 64).toNat = 64 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem readBytes_abi_two (mem : Nat → UInt8) (n0 n1 : Nat)
    (h0 : n0 < wordBound) (h1 : n1 < wordBound) :
    readBytes
      (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
        (abiPtr + 32) (BitVec.ofNat 256 n1))
      abiPtr 64 = wordBytes n0 ++ wordBytes n1 := by
  have h64 : (64 : Nat) = 32 + 32 := rfl
  rw [h64, readBytes_split]
  have h1' :
      readBytes (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1))
        (abiPtr + 32) 32 = wordBytes n1 := by
    have hout0 : ∀ i ∈ List.range 32,
        storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + 32 + i) =
        storeWord mem (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + 32 + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      have hin : abiPtr + 32 ≤ abiPtr + 32 + i ∧ abiPtr + 32 + i < abiPtr + 32 + 32 := by omega
      rw [storeWord_in (h := hin), storeWord_in (h := hin)]
    unfold readBytes
    refine Eq.trans (List.map_congr_left hout0) ?_
    change readBytes (storeWord mem (abiPtr + 32) (BitVec.ofNat 256 n1))
      (abiPtr + 32) 32 = wordBytes n1
    exact readBytes_storeWord_wordBytes _ _ _ h1
  have h0' :
      readBytes (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1))
        abiPtr 32 = wordBytes n0 := by
    have hout32 : ∀ i ∈ List.range 32,
        storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + i) =
        storeWord mem abiPtr (BitVec.ofNat 256 n0) (abiPtr + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      exact storeWord_out _ _ _ _ (.inl (by simp only [abiPtr]; omega))
    unfold readBytes
    refine Eq.trans (List.map_congr_left hout32) ?_
    change readBytes (storeWord mem abiPtr (BitVec.ofNat 256 n0)) abiPtr 32 = wordBytes n0
    exact readBytes_storeWord_wordBytes _ _ _ h0
  rw [h0', h1']

theorem return_pair_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState}
    (funs : FunEnv evm) (V : VEnv evm)
    {x y : YExpr} {v0 v1 : Nat} (hv0 : v0 < wordBound) (hv1 : v1 < wordBound)
    (he0 : EvalExpr evm funs V st x (.vals [BitVec.ofNat 256 v0] st))
    (he1 : ∀ st', EvalExpr evm funs V st' y (.vals [BitVec.ofNat 256 v1] st'))
    (hR : R c Γ κ w st) :
    ∃ st', ExecStmts evm funs V st (emitReturnWords {} [x, y]).stmts V st' .halt ∧
      st'.halted = some (.ret, wordBytes v0 ++ wordBytes v1) ∧ R c Γ κ w st' := by
  let stM0 : EvmState :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr (BitVec.ofNat 256 v0) }
  have hm0 :
      ExecStmt evm funs V st (.exprStmt (bop Op.mstore [lit abiPtr, x])) V stM0 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil he0) Step.lit)
      (by
        simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
        rfl))
  let stM1 : EvmState :=
    { touchMemory stM0 (abiPtr + 32) 32 with
      memory := storeWord stM0.memory (abiPtr + 32) (BitVec.ofNat 256 v1) }
  have hm1 :
      ExecStmt evm funs V stM0 (.exprStmt (bop Op.mstore [lit (abiPtr + 32), y])) V stM1 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil (he1 stM0)) Step.lit)
      (by
        simp only [evm_litValue_number, step_mstore, toNat_abiPtr32]
        rfl))
  let bytes := readBytes stM1.memory abiPtr 64
  let stR : EvmState :=
    { touchMemory stM1 abiPtr 64 with halted := some (.ret, bytes) }
  have hret :
      ExecStmt evm funs V stM1 (.exprStmt (bop Op.ret [lit abiPtr, lit 64])) V stR .halt :=
    Step.exprStmtHalt (Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
      (by
        simp only [evm_litValue_number, step_ret, toNat_abiPtr, toNat_64_ops]
        rfl))
  refine ⟨stR, ?_, ?_, ?_⟩
  · simp only [emitReturnWords_two, Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hm0 (Step.seqCons hm1 (Step.seqStop hret halt_ne_normal))
  · have hhalt : stR.halted = some (.ret, readBytes stM1.memory abiPtr 64) := rfl
    rw [hhalt]
    refine congrArg (fun b => some (HaltKind.ret, b)) ?_
    simp [stM1, stM0, readBytes_abi_two _ _ _ hv0 hv1]
  · have hR0 := R_memOnly hR (memOnly_mstore st (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 v0))
    have hR1 := R_memOnly hR0 (memOnly_mstore stM0 (BitVec.ofNat 256 (abiPtr + 32)) (BitVec.ofNat 256 v1))
    exact R_touch_halted hR1 abiPtr 64 _

theorem op_sim_pure {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a : Atom}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hwf : opWF c (.pure a) = true)
    (hn : identsNodup tag (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.pure a)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitLet {} (identV tag env.length) (atomE tag env.length a)).stmts
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv tag Γ c κ ctx w' (v :: env)
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitLet {} (identV tag env.length) (atomE tag env.length a)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwfA : atomWF a = true := by simpa [opWF] using hwf
  have hv := atom_eval_lt henv hwfA
  have hn0 : identsNodup tag env.length = true := identsNodup_mono tag (by omega) hn
  have he := eval_atom tag funs (st := st) hV hn0 a
  simp [Op.denote, Tx.run_pure]
  refine ⟨st, ?_, ⟨by rw [hV, toVEnv_cons], envWF_cons hv henv, hR, hctx⟩⟩
  simp only [emitLet_stmts, Emit.stmts_nil, List.nil_append]
  exact Step.seqCons (Step.letVal he rfl) Step.seqNil

end Lsc.Compiler
