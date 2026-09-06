import Lsc.Compiler.Proof.OpsArith

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`mulDivDown` / `mulDivUp` simulation (`let v := mul(a,b)` + overflow guard + `div` / `switch mod`).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem emitLetOp_mulDivDown (c : ContractDef) (e : Emit) (d : Nat) (a b c' : Atom) :
    emitLetOp c e d (.mulDivDown a b c') =
      some (emitMulDivDown e (identV d) (atomE d a) (atomE d b) (atomE d c')) := rfl

theorem emitLetOp_mulDivUp (c : ContractDef) (e : Emit) (d : Nat) (a b c' : Atom) :
    emitLetOp c e d (.mulDivUp a b c') =
      some (emitMulDivUp e (identV d) (atomE d a) (atomE d b) (atomE d c')) := rfl

theorem emitMulDivDown_stmts (e : Emit) (name : YIdent) (a b c : YExpr) :
    (emitMulDivDown e name a b c).stmts =
      e.stmts ++
        [.cond (bop Op.iszero [c]) (emitPanic {} 0x12).stmts,
          .letDecl [name] (some (bop Op.mul [a, b])),
          .cond (mulOverflowCnd a b (var name)) (emitPanic {} 0x11).stmts,
          .assign [name] (bop Op.div [var name, c])] := by
  simp [emitMulDivDown, emitIf_stmts, emitLet_stmts, emitMulOverflowGuard_stmts,
    Emit.stmts_push, mulOverflowCnd]

def mulDivUpDefault (name : YIdent) (c : YExpr) : YBlock :=
  [.assign [name] (bop Op.add [bop Op.div [var name, c], lit 1])]

def mulDivUpZero (name : YIdent) (c : YExpr) : YBlock :=
  [.assign [name] (bop Op.div [var name, c])]

theorem emitMulDivUp_stmts (e : Emit) (name : YIdent) (a b c : YExpr) :
    (emitMulDivUp e name a b c).stmts =
      e.stmts ++
        [.cond (bop Op.iszero [c]) (emitPanic {} 0x12).stmts,
          .letDecl [name] (some (bop Op.mul [a, b])),
          .cond (mulOverflowCnd a b (var name)) (emitPanic {} 0x11).stmts,
          .switch (bop Op.mod [var name, c])
            [(YulSemantics.Literal.number 0, mulDivUpZero name c)]
            (some (mulDivUpDefault name c))] := by
  simp [emitMulDivUp, emitIf_stmts, emitLet_stmts, emitMulOverflowGuard_stmts,
    Emit.stmts_push, mulOverflowCnd, mulDivUpZero, mulDivUpDefault]

private theorem eval_mul_ofNat {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {aE bE : YExpr} {a b : Nat}
    (hea : EvalExpr evm funs V st aE (.vals [BitVec.ofNat 256 a] st))
    (heb : EvalExpr evm funs V st bE (.vals [BitVec.ofNat 256 b] st)) :
    EvalExpr evm funs V st (bop Op.mul [aE, bE])
      (.vals [BitVec.ofNat 256 (a * b)] st) := by
  have h :
      EvalExpr evm funs V st (bop Op.mul [aE, bE])
        (.vals [BitVec.ofNat 256 a * BitVec.ofNat 256 b] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) hea) (step_mul _ _ _)
  rw [ofNat_mul] at h
  exact h

theorem op_sim_mulDivDown {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b d : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.mulDivDown a b d) = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.mulDivDown a b d)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitMulDivDown {} (identV env.length)
              (atomE env.length a) (atomE env.length b) (atomE env.length d)).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitMulDivDown {} (identV env.length)
              (atomE env.length a) (atomE env.length b) (atomE env.length d)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : (atomWF a = true ∧ atomWF b = true) ∧ atomWF d = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ha := atom_eval_lt henv hwf'.1.1
  have hb := atom_eval_lt henv hwf'.1.2
  have hd := atom_eval_lt henv hwf'.2
  have hn0 : identsNodup env.length = true := identsNodup_mono (by omega) hn
  have hea := eval_atom funs (st := st) hV hn0 a
  have heb := eval_atom funs (st := st) hV hn0 b
  have hed := eval_atom funs (st := st) hV hn0 d
  have hisz := eval_iszero_ofNat hd hed
  let name := identV env.length
  simp only [Op.denote, Tx.run_mulDivDown]
  by_cases hc0 : d.eval env = 0
  · rw [if_pos hc0]; simp
    obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V st 0x12 hisz (by
      simp [hc0, b2w, Dialect.zero, litValue]) code_0x12_lt
    refine ⟨V, st', ?_, panicBytes 0x12, hh, rfl⟩
    simp only [emitMulDivDown_stmts, Emit.stmts_nil, List.nil_append]
    exact Step.seqStop hp halt_ne_normal
  · rw [if_neg hc0]
    have hcv0 : b2w (decide (d.eval env = 0)) = 0 := by simp [hc0, b2w]
    have hmul := eval_mul_ofNat hea heb
    let V₁ : VEnv evm := (name, BitVec.ofNat 256 (a.eval env * b.eval env)) :: V
    have hlet : ExecStmt evm funs V st
        (.letDecl [name] (some (bop Op.mul [atomE env.length a, atomE env.length b])))
        V₁ st .normal :=
      Step.letVal hmul rfl
    have hea1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn a
    have heb1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn b
    have hed1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn d
    have hep : EvalExpr evm funs V₁ st (var name)
        (.vals [BitVec.ofNat 256 (a.eval env * b.eval env)] st) :=
      Step.var (by
        simp only [V₁, name]
        rw [VEnv.get_cons, if_pos rfl])
    have hguard := eval_mulOverflowGuard (V := V₁) (st := st) ha hb hea1 heb1 hep
    by_cases hfit : a.eval env * b.eval env < wordBound
    · rw [if_pos hfit]; simp
      have hcvG : b2w (decide (wordBound ≤ a.eval env * b.eval env)) = 0 := by
        simp [Nat.not_le.mpr hfit, b2w]
      have hdiv :
          EvalExpr evm funs V₁ st (bop Op.div [var name, atomE env.length d])
            (.vals [if BitVec.ofNat 256 (d.eval env) = 0 then 0
              else BitVec.ofNat 256 (a.eval env * b.eval env) /
                BitVec.ofNat 256 (d.eval env)] st) :=
        Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hed1) hep) (step_div _ _ _)
      rw [evm_div_ofNat hfit hd hc0] at hdiv
      have hset :
          VEnv.setMany V₁ [name] [BitVec.ofNat 256 (a.eval env * b.eval env / d.eval env)] =
            (name, BitVec.ofNat 256 (a.eval env * b.eval env / d.eval env)) :: V := by
        simp only [V₁]
        rw [VEnv.setMany_one, VEnv.set_head]
      have hassign : ExecStmt evm funs V₁ st
          (.assign [name] (bop Op.div [var name, atomE env.length d]))
          ((name, BitVec.ofNat 256 (a.eval env * b.eval env / d.eval env)) :: V) st .normal := by
        rw [← hset]
        exact Step.assignVal (D := evm) hdiv rfl
      refine ⟨st, ?_, ?_⟩
      · simp only [emitMulDivDown_stmts, Emit.stmts_nil, List.nil_append]
        exact Step.seqCons (Step.ifFalse hisz (by simp [hcv0, Dialect.zero, litValue]))
          (Step.seqCons hlet
            (Step.seqCons (Step.ifFalse hguard (by simp [hcvG, Dialect.zero, litValue]))
              (Step.seqCons hassign Step.seqNil)))
      · exact ⟨by rw [hV, toVEnv_cons],
          envWF_cons (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hfit) henv, hR, hctx⟩
    · rw [if_neg hfit]; simp
      obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V₁ st 0x11 hguard (by
        simp [Nat.le_of_not_gt hfit, b2w, Dialect.zero, litValue]) code_0x11_lt
      refine ⟨V₁, st', ?_, panicBytes 0x11, hh, rfl⟩
      simp only [emitMulDivDown_stmts, Emit.stmts_nil, List.nil_append]
      exact Step.seqCons (Step.ifFalse hisz (by simp [hcv0, Dialect.zero, litValue]))
        (Step.seqCons hlet (Step.seqStop hp halt_ne_normal))

theorem op_sim_mulDivUp {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a b d : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : opWF c (.mulDivUp a b d) = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.mulDivUp a b d)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitMulDivUp {} (identV env.length)
              (atomE env.length a) (atomE env.length b) (atomE env.length d)).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitMulDivUp {} (identV env.length)
              (atomE env.length a) (atomE env.length b) (atomE env.length d)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : (atomWF a = true ∧ atomWF b = true) ∧ atomWF d = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ha := atom_eval_lt henv hwf'.1.1
  have hb := atom_eval_lt henv hwf'.1.2
  have hd := atom_eval_lt henv hwf'.2
  have hn0 : identsNodup env.length = true := identsNodup_mono (by omega) hn
  have hea := eval_atom funs (st := st) hV hn0 a
  have heb := eval_atom funs (st := st) hV hn0 b
  have hed := eval_atom funs (st := st) hV hn0 d
  have hisz := eval_iszero_ofNat hd hed
  let name := identV env.length
  simp only [Op.denote, Tx.run_mulDivUp]
  by_cases hc0 : d.eval env = 0
  · rw [if_pos hc0]; simp
    obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V st 0x12 hisz (by
      simp [hc0, b2w, Dialect.zero, litValue]) code_0x12_lt
    refine ⟨V, st', ?_, panicBytes 0x12, hh, rfl⟩
    simp only [emitMulDivUp_stmts, Emit.stmts_nil, List.nil_append]
    exact Step.seqStop hp halt_ne_normal
  · rw [if_neg hc0]
    have hcv0 : b2w (decide (d.eval env = 0)) = 0 := by simp [hc0, b2w]
    have hmul := eval_mul_ofNat hea heb
    let V₁ : VEnv evm := (name, BitVec.ofNat 256 (a.eval env * b.eval env)) :: V
    have hlet : ExecStmt evm funs V st
        (.letDecl [name] (some (bop Op.mul [atomE env.length a, atomE env.length b])))
        V₁ st .normal :=
      Step.letVal hmul rfl
    have hea1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn a
    have heb1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn b
    have hed1 := eval_atom_cons funs st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn d
    have hep : EvalExpr evm funs V₁ st (var name)
        (.vals [BitVec.ofNat 256 (a.eval env * b.eval env)] st) :=
      Step.var (by
        simp only [V₁, name]
        rw [VEnv.get_cons, if_pos rfl])
    have hguard := eval_mulOverflowGuard (V := V₁) (st := st) ha hb hea1 heb1 hep
    by_cases hfit : a.eval env * b.eval env < wordBound
    · rw [if_pos hfit]; simp
      have hcvG : b2w (decide (wordBound ≤ a.eval env * b.eval env)) = 0 := by
        simp [Nat.not_le.mpr hfit, b2w]
      let funsB : FunEnv evm := [] :: funs
      have hed1B := eval_atom_cons funsB st (BitVec.ofNat 256 (a.eval env * b.eval env)) hV hn d
      have hepB : EvalExpr evm funsB V₁ st (var name)
          (.vals [BitVec.ofNat 256 (a.eval env * b.eval env)] st) :=
        Step.var (by
          simp only [V₁, name]
          rw [VEnv.get_cons, if_pos rfl])
      have hmod :
          EvalExpr evm funs V₁ st (bop Op.mod [var name, atomE env.length d])
            (.vals [if BitVec.ofNat 256 (d.eval env) = 0 then 0
              else BitVec.ofNat 256 (a.eval env * b.eval env) %
                BitVec.ofNat 256 (d.eval env)] st) :=
        Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hed1) hep) (step_mod _ _ _)
      rw [evm_mod_ofNat hfit hd hc0] at hmod
      have hdivB :
          EvalExpr evm funsB V₁ st (bop Op.div [var name, atomE env.length d])
            (.vals [if BitVec.ofNat 256 (d.eval env) = 0 then 0
              else BitVec.ofNat 256 (a.eval env * b.eval env) /
                BitVec.ofNat 256 (d.eval env)] st) :=
        Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hed1B) hepB) (step_div _ _ _)
      rw [evm_div_ofNat hfit hd hc0] at hdivB
      let q := a.eval env * b.eval env / d.eval env
      let r := a.eval env * b.eval env % d.eval env
      have hrlt : r < wordBound := Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0)) hd
      by_cases hrem : a.eval env * b.eval env % d.eval env = 0
      · have hsel :
            selectSwitch evm (BitVec.ofNat 256 r)
              [(YulSemantics.Literal.number 0, mulDivUpZero name (atomE env.length d))]
              (some (mulDivUpDefault name (atomE env.length d))) =
              mulDivUpZero name (atomE env.length d) := by
          have : BitVec.ofNat 256 r = 0 := (ofNat_eq_zero hrlt).mpr (by simp [r, hrem])
          simpa [this] using
            selectSwitch_zero (eA := mulDivUpDefault name (atomE env.length d))
              (eB := mulDivUpZero name (atomE env.length d))
        have hset :
            VEnv.setMany V₁ [name] [BitVec.ofNat 256 q] =
              (name, BitVec.ofNat 256 q) :: V := by
          simp only [V₁]
          rw [VEnv.setMany_one, VEnv.set_head]
        have hassign : ExecStmt evm funsB V₁ st
            (.assign [name] (bop Op.div [var name, atomE env.length d]))
            ((name, BitVec.ofNat 256 q) :: V) st .normal := by
          rw [← hset]
          exact Step.assignVal (D := evm) hdivB rfl
        have hexec :
            ExecStmts evm funsB V₁ st (mulDivUpZero name (atomE env.length d))
              ((name, BitVec.ofNat 256 q) :: V) st .normal := by
          simp only [mulDivUpZero]
          exact Step.seqCons hassign Step.seqNil
        have hsw := exec_switch_stmt (funs := funs) (V := V₁) hmod hsel
          (by simp [mulDivUpZero, hoist]) hexec
        have hrestore :
            restore V₁ ((name, BitVec.ofNat 256 q) :: V) =
              (name, BitVec.ofNat 256 q) :: V :=
          restore_length (by simp [V₁])
        rw [hrestore] at hsw
        have hv : q + (if a.eval env * b.eval env % d.eval env = 0 then 0 else 1) = q := by
          simp [hrem]
        rw [hv]
        refine ⟨st, ?_, ?_⟩
        · simp only [emitMulDivUp_stmts, Emit.stmts_nil, List.nil_append]
          exact Step.seqCons (Step.ifFalse hisz (by simp [hcv0, Dialect.zero, litValue]))
            (Step.seqCons hlet
              (Step.seqCons (Step.ifFalse hguard (by simp [hcvG, Dialect.zero, litValue]))
                (Step.seqCons hsw Step.seqNil)))
        · exact ⟨by rw [hV, toVEnv_cons],
            envWF_cons (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hfit) henv, hR, hctx⟩
      · have hsel :
            selectSwitch evm (BitVec.ofNat 256 r)
              [(YulSemantics.Literal.number 0, mulDivUpZero name (atomE env.length d))]
              (some (mulDivUpDefault name (atomE env.length d))) =
              mulDivUpDefault name (atomE env.length d) :=
          selectSwitch_nonzero (eA := mulDivUpDefault name (atomE env.length d))
            (eB := mulDivUpZero name (atomE env.length d))
            (mt (ofNat_eq_zero hrlt).mp (by simp [r, hrem]))
        have h1 : EvalExpr evm funsB V₁ st (lit 1)
            (.vals [evm.litValue (.number 1)] st) := Step.lit (D := evm)
        have hadd :
            EvalExpr evm funsB V₁ st
              (bop Op.add [bop Op.div [var name, atomE env.length d], lit 1])
              (.vals [BitVec.ofNat 256 q + BitVec.ofNat 256 1] st) := by
          rw [evm_litValue_number] at h1
          exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil h1) hdivB)
            (step_add _ _ _)
        rw [ofNat_add] at hadd
        have hset :
            VEnv.setMany V₁ [name] [BitVec.ofNat 256 (q + 1)] =
              (name, BitVec.ofNat 256 (q + 1)) :: V := by
          simp only [V₁]
          rw [VEnv.setMany_one, VEnv.set_head]
        have hassign : ExecStmt evm funsB V₁ st
            (.assign [name]
              (bop Op.add [bop Op.div [var name, atomE env.length d], lit 1]))
            ((name, BitVec.ofNat 256 (q + 1)) :: V) st .normal := by
          rw [← hset]
          exact Step.assignVal (D := evm) hadd rfl
        have hexec :
            ExecStmts evm funsB V₁ st (mulDivUpDefault name (atomE env.length d))
              ((name, BitVec.ofNat 256 (q + 1)) :: V) st .normal := by
          simp only [mulDivUpDefault]
          exact Step.seqCons hassign Step.seqNil
        have hsw := exec_switch_stmt (funs := funs) (V := V₁) hmod hsel
          (by simp [mulDivUpDefault, hoist]) hexec
        have hrestore :
            restore V₁ ((name, BitVec.ofNat 256 (q + 1)) :: V) =
              (name, BitVec.ofNat 256 (q + 1)) :: V :=
          restore_length (by simp [V₁])
        rw [hrestore] at hsw
        have hv : q + (if a.eval env * b.eval env % d.eval env = 0 then 0 else 1) = q + 1 := by
          simp [hrem]
        have hq1 : q + 1 < wordBound := mulDiv_up_lt hfit hc0 hrem
        rw [hv]
        refine ⟨st, ?_, ?_⟩
        · simp only [emitMulDivUp_stmts, Emit.stmts_nil, List.nil_append]
          exact Step.seqCons (Step.ifFalse hisz (by simp [hcv0, Dialect.zero, litValue]))
            (Step.seqCons hlet
              (Step.seqCons (Step.ifFalse hguard (by simp [hcvG, Dialect.zero, litValue]))
                (Step.seqCons hsw Step.seqNil)))
        · exact ⟨by rw [hV, toVEnv_cons], envWF_cons hq1 henv, hR, hctx⟩
    · rw [if_neg hfit]; simp
      obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V₁ st 0x11 hguard (by
        simp [Nat.le_of_not_gt hfit, b2w, Dialect.zero, litValue]) code_0x11_lt
      refine ⟨V₁, st', ?_, panicBytes 0x11, hh, rfl⟩
      simp only [emitMulDivUp_stmts, Emit.stmts_nil, List.nil_append]
      exact Step.seqCons (Step.ifFalse hisz (by simp [hcv0, Dialect.zero, litValue]))
        (Step.seqCons hlet (Step.seqStop hp halt_ne_normal))

end Lsc.Compiler
