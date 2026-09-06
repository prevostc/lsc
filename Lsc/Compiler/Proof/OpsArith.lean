import Lsc.Compiler.Proof.OpsToken

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Checked `mul` / `div` simulation, plus the shared mul-overflow guard.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem step_mul (st : EvmState) (a b : U256) :
    stepOp Op.mul [a, b] st = some (.ok [a * b] st) := rfl

theorem step_div (st : EvmState) (a b : U256) :
    stepOp Op.div [a, b] st = some (.ok [if b = 0 then 0 else a / b] st) := rfl

theorem step_mod (st : EvmState) (a b : U256) :
    stepOp Op.mod [a, b] st = some (.ok [if b = 0 then 0 else a % b] st) := rfl

theorem code_0x11_lt : (0x11 : Nat) < wordBound := lt_256_wordBound (by decide)
theorem code_0x12_lt : (0x12 : Nat) < wordBound := lt_256_wordBound (by decide)

def mulOverflowCnd (a b p : YExpr) : YExpr :=
  bop Op.iszero
    [bop Op.or
      [bop Op.iszero [a],
        bop Op.eq [bop Op.div [p, a], b]]]

theorem emitMulOverflowGuard_stmts (e : Emit) (a b p : YExpr) :
    (emitMulOverflowGuard e a b p).stmts =
      e.stmts ++ [.cond (mulOverflowCnd a b p) (emitPanic {} 0x11).stmts] :=
  emitIf_stmts _ _ _

theorem emitLetOp_mulChecked (c : ContractDef) (e : Emit) (d : Nat) (a b : Atom) :
    emitLetOp c e d (.mulChecked a b) =
      some (emitMulChecked e (identV d) (atomE d a) (atomE d b)) := rfl

theorem emitLetOp_divChecked (c : ContractDef) (e : Emit) (d : Nat) (a b : Atom) :
    emitLetOp c e d (.divChecked a b) =
      some (emitDivChecked e (identV d) (atomE d a) (atomE d b)) := rfl

theorem emitMulChecked_stmts (e : Emit) (name : YIdent) (a b : YExpr) :
    (emitMulChecked e name a b).stmts =
      e.stmts ++
        [.letDecl [name] (some (bop Op.mul [a, b])),
          .cond (mulOverflowCnd a b (var name)) (emitPanic {} 0x11).stmts] := by
  simp [emitMulChecked, emitLet_stmts, emitMulOverflowGuard_stmts, mulOverflowCnd]

theorem emitDivChecked_stmts (e : Emit) (name : YIdent) (a b : YExpr) :
    (emitDivChecked e name a b).stmts =
      e.stmts ++
        [.cond (bop Op.iszero [b]) (emitPanic {} 0x12).stmts,
          .letDecl [name] (some (bop Op.div [a, b]))] := by
  simp [emitDivChecked, emitIf_stmts, emitLet_stmts]

theorem b2w_ofNat_eq_zero {n : Nat} (hn : n < wordBound) :
    b2w (BitVec.ofNat 256 n = 0) = b2w (decide (n = 0)) := by
  cases h : decide (n = 0)
  · have hn0 : n ≠ 0 := of_decide_eq_false h
    have hne : BitVec.ofNat 256 n ≠ 0#256 := mt (ofNat_eq_zero hn).mp hn0
    simp [hne, b2w]
  · have hn0 : n = 0 := of_decide_eq_true h
    have : BitVec.ofNat 256 n = 0 := (ofNat_eq_zero hn).mpr hn0
    simp [this, b2w]

theorem eval_iszero_ofNat {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {e : YExpr} {n : Nat} (hn : n < wordBound)
    (he : EvalExpr evm funs V st e (.vals [BitVec.ofNat 256 n] st)) :
    EvalExpr evm funs V st (bop Op.iszero [e])
      (.vals [b2w (decide (n = 0))] st) := by
  have hisz :
      EvalExpr evm funs V st (bop Op.iszero [e])
        (.vals [b2w (BitVec.ofNat 256 n = 0)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil he) (step_iszero _ _)
  rwa [b2w_ofNat_eq_zero hn] at hisz

/-- Yul `iszero(or(iszero(a), eq(div(p,a), b)))` with `p = mul(a,b)` is the overflow bit. -/
theorem mul_overflow_guard_b2w {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    b2w ((b2w (BitVec.ofNat 256 a = 0) |||
        b2w ((if BitVec.ofNat 256 a = 0 then (0 : U256)
              else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
            BitVec.ofNat 256 b)) = 0) =
      b2w (decide (wordBound ≤ a * b)) := by
  have hfits := mul_fits_iff ha hb
  change b2w ((b2w (decide (BitVec.ofNat 256 a = 0)) |||
      b2w (decide ((if BitVec.ofNat 256 a = 0 then (0 : U256)
        else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
          BitVec.ofNat 256 b))) = 0) =
    b2w (decide (wordBound ≤ a * b))
  rw [b2w_or, b2w_iszero]
  have hor :
      (decide (BitVec.ofNat 256 a = 0) ||
        decide ((if BitVec.ofNat 256 a = 0 then (0 : U256)
          else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
            BitVec.ofNat 256 b)) =
      decide (a * b < wordBound) := by
    cases hA : decide (BitVec.ofNat 256 a = 0)
    · have h0 : ¬ BitVec.ofNat 256 a = 0 := of_decide_eq_false hA
      simp only [hA, Bool.false_or, if_neg h0]
      cases hB : decide (BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a =
          BitVec.ofNat 256 b)
      · have hq : ¬ (BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a =
            BitVec.ofNat 256 b) := of_decide_eq_false hB
        have hlt : ¬ a * b < wordBound := fun h => hq ((hfits.mp h).resolve_left h0)
        simp [hB, hlt]
      · have hq : BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a =
            BitVec.ofNat 256 b := of_decide_eq_true hB
        have hlt : a * b < wordBound := hfits.mpr (.inr hq)
        simp [hB, hlt]
    · have h0 : BitVec.ofNat 256 a = 0 := of_decide_eq_true hA
      have ha0 : a = 0 := (ofNat_eq_zero ha).mp h0
      subst ha0
      have hfit : 0 * b < wordBound := by simpa using zero_lt_wordBound
      simp only [hA, Bool.true_or]
      exact (decide_eq_true hfit).symm
  rw [hor, b2w_decide_not]
  simp [Nat.not_lt]

theorem eval_mulOverflowGuard {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {aE bE pE : YExpr} {a b : Nat}
    (ha : a < wordBound) (hb : b < wordBound)
    (hea : EvalExpr evm funs V st aE (.vals [BitVec.ofNat 256 a] st))
    (heb : EvalExpr evm funs V st bE (.vals [BitVec.ofNat 256 b] st))
    (hep : EvalExpr evm funs V st pE
      (.vals [BitVec.ofNat 256 (a * b)] st)) :
    EvalExpr evm funs V st (mulOverflowCnd aE bE pE)
      (.vals [b2w (decide (wordBound ≤ a * b))] st) := by
  have hep' : EvalExpr evm funs V st pE
      (.vals [BitVec.ofNat 256 a * BitVec.ofNat 256 b] st) := by
    rw [ofNat_mul]; exact hep
  have hisza :
      EvalExpr evm funs V st (bop Op.iszero [aE])
        (.vals [b2w (BitVec.ofNat 256 a = 0)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil hea) (step_iszero _ _)
  have hdiv :
      EvalExpr evm funs V st (bop Op.div [pE, aE])
        (.vals [if BitVec.ofNat 256 a = 0 then 0
          else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hea) hep') (step_div _ _ _)
  have heq :
      EvalExpr evm funs V st (bop Op.eq [bop Op.div [pE, aE], bE])
        (.vals [b2w ((if BitVec.ofNat 256 a = 0 then 0
          else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
            BitVec.ofNat 256 b)] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hdiv) (step_eq _ _ _)
  have hor :
      EvalExpr evm funs V st
        (bop Op.or [bop Op.iszero [aE], bop Op.eq [bop Op.div [pE, aE], bE]])
        (.vals [b2w (BitVec.ofNat 256 a = 0) |||
          b2w ((if BitVec.ofNat 256 a = 0 then 0
            else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
              BitVec.ofNat 256 b)] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heq) hisza) (step_or _ _ _)
  have hisz :
      EvalExpr evm funs V st (mulOverflowCnd aE bE pE)
        (.vals [b2w ((b2w (BitVec.ofNat 256 a = 0) |||
          b2w ((if BitVec.ofNat 256 a = 0 then 0
            else BitVec.ofNat 256 a * BitVec.ofNat 256 b / BitVec.ofNat 256 a) =
              BitVec.ofNat 256 b)) = 0)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil hor) (step_iszero _ _)
  rwa [mul_overflow_guard_b2w ha hb] at hisz

theorem panic_ifTrue (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    {cnd : YExpr} {cv : U256} (code : Nat)
    (he : EvalExpr evm funs V st cnd (.vals [cv] st))
    (hcv : cv ≠ 0) (hcode : code < wordBound) :
    ∃ st', ExecStmt evm funs V st (.cond cnd (emitPanic {} code).stmts) V st' .halt ∧
      st'.halted = some (.revert, panicBytes code) := by
  obtain ⟨st', hp, hh⟩ := panic_sim ([] :: funs) V st code hcode
  refine ⟨st', ?_, hh⟩
  refine Step.ifTrue (D := evm) he hcv ?_
  have inner :
      ExecStmts evm (hoist evm (emitPanic {} code).stmts :: funs) V st
        (emitPanic {} code).stmts V st' .halt := by
    rw [hoist_panic]
    exact hp
  simpa [restore_self] using Step.block (D := evm) inner

theorem op_sim_mulChecked {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.mulChecked a b) = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.mulChecked a b)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitMulChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitMulChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
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
  have hmul :
      EvalExpr evm funs V st (bop Op.mul [atomE env.length a, atomE env.length b])
        (.vals [BitVec.ofNat 256 (a.eval env) * BitVec.ofNat 256 (b.eval env)] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_mul _ _ _)
  rw [ofNat_mul] at hmul
  let V₁ := (identV env.length, BitVec.ofNat 256 (a.eval env * b.eval env)) :: V
  have hlet : ExecStmt evm funs V st
      (.letDecl [identV env.length]
        (some (bop Op.mul [atomE env.length a, atomE env.length b])))
      V₁ st .normal :=
    Step.letVal hmul rfl
  have hea1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn a
  have heb1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn b
  have hep :
      EvalExpr evm funs V₁ st (var (identV env.length))
        (.vals [BitVec.ofNat 256 (a.eval env * b.eval env)] st) :=
    Step.var (by
      simp only [V₁]
      rw [VEnv.get_cons, if_pos rfl])
  have hguard := eval_mulOverflowGuard (V := V₁) (st := st) ha hb hea1 heb1 hep
  simp only [Op.denote, Tx.run_mulChecked]
  by_cases hfit : a.eval env * b.eval env < wordBound
  · simp [hfit]
    have hcv : b2w (decide (wordBound ≤ a.eval env * b.eval env)) = 0 := by
      simp [Nat.not_le.mpr hfit, b2w]
    refine ⟨st, ?_, ?_⟩
    · simp only [emitMulChecked_stmts, Emit.stmts_nil, List.nil_append]
      refine Step.seqCons hlet (Step.seqCons (Step.ifFalse hguard ?_) Step.seqNil)
      simp [hcv, Dialect.zero, litValue]
    · exact ⟨by rw [hV, toVEnv_cons], envWF_cons hfit henv, hR, hctx⟩
  · simp [hfit]
    have hcv : b2w (decide (wordBound ≤ a.eval env * b.eval env)) ≠ 0 := by
      simp [Nat.le_of_not_gt hfit, b2w]
    obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V₁ st 0x11 hguard (by
      simp [Nat.le_of_not_gt hfit, b2w, Dialect.zero, litValue]) code_0x11_lt
    refine ⟨V₁, st', ?_, panicBytes 0x11, hh, rfl⟩
    simp only [emitMulChecked_stmts, Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hlet (Step.seqStop hp halt_ne_normal)

theorem op_sim_divChecked {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.divChecked a b) = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.divChecked a b)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitDivChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitDivChecked {} (identV env.length) (atomE env.length a) (atomE env.length b)).stmts
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
  have hisz := eval_iszero_ofNat hb heb
  simp only [Op.denote, Tx.run_divChecked]
  by_cases hb0 : b.eval env = 0
  · simp [hb0]
    have hcv : b2w (decide (b.eval env = 0)) ≠ 0 := by simp [hb0, b2w]
    obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V st 0x12 hisz (by
      simp [hb0, b2w, Dialect.zero, litValue]) code_0x12_lt
    refine ⟨V, st', ?_, panicBytes 0x12, hh, rfl⟩
    simp only [emitDivChecked_stmts, Emit.stmts_nil, List.nil_append]
    exact Step.seqStop hp halt_ne_normal
  · simp [hb0]
    have hdiv :
        EvalExpr evm funs V st (bop Op.div [atomE env.length a, atomE env.length b])
          (.vals [if BitVec.ofNat 256 (b.eval env) = 0 then 0
            else BitVec.ofNat 256 (a.eval env) / BitVec.ofNat 256 (b.eval env)] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_div _ _ _)
    rw [evm_div_ofNat ha hb hb0] at hdiv
    let V₁ := (identV env.length, BitVec.ofNat 256 (a.eval env / b.eval env)) :: V
    have hlet : ExecStmt evm funs V st
        (.letDecl [identV env.length]
          (some (bop Op.div [atomE env.length a, atomE env.length b])))
        V₁ st .normal :=
      Step.letVal hdiv rfl
    have hcv : b2w (decide (b.eval env = 0)) = 0 := by simp [hb0, b2w]
    refine ⟨st, ?_, ?_⟩
    · simp only [emitDivChecked_stmts, Emit.stmts_nil, List.nil_append]
      refine Step.seqCons (Step.ifFalse hisz ?_) (Step.seqCons hlet Step.seqNil)
      simp [hcv, Dialect.zero, litValue]
    ·     exact ⟨by rw [hV, toVEnv_cons],
        envWF_cons (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha) henv, hR, hctx⟩

theorem exec_switch_stmt {funs V st V' st' o} {cnd : YExpr} {eA eB body : YBlock} {cv : U256}
    (he : EvalExpr evm funs V st cnd (.vals [cv] st))
    (hsel : selectSwitch evm cv [(YulSemantics.Literal.number 0, eB)] (some eA) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: funs) V st body V' st' o) :
    ExecStmt evm funs V st
      (.switch cnd [(YulSemantics.Literal.number 0, eB)] (some eA))
      (restore V V') st' o := by
  refine Step.switchExec he ?_
  refine Step.block (D := evm) ?_
  rwa [hsel, hhoist]

theorem selectSwitch_zero {eA eB : YBlock} :
    selectSwitch evm (0 : U256) [(YulSemantics.Literal.number 0, eB)] (some eA) = eB := by
  simp [selectSwitch, litValue_number]

theorem selectSwitch_nonzero {eA eB : YBlock} {cv : U256} (h : cv ≠ 0) :
    selectSwitch evm cv [(YulSemantics.Literal.number 0, eB)] (some eA) = eA := by
  have hne : cv ≠ evm.litValue (.number 0) := by
    rw [evm_litValue_number]; exact h
  simp [selectSwitch, List.find?, decide_eq_false hne]

end Lsc.Compiler
