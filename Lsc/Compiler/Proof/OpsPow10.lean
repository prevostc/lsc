import Lsc.Compiler.Proof.OpsMulDiv
import Lsc.Lang.Word

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`pow10` simulation: `if gt(d, 77) { panic 0x11 }` then `let v := exp(10, d)`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem emitLetOp_pow10 (c : ContractDef) (e : Emit) (d : Nat) (a : Atom) :
    emitLetOp tag c e d (.pow10 a) =
      some (emitPow10 e (identV tag d) (atomE tag d a)) := rfl

theorem emitPow10_stmts (e : Emit) (name : YIdent) (d : YExpr) :
    (emitPow10 e name d).stmts =
      e.stmts ++
        [.cond (bop Op.gt [d, lit 77]) (emitPanic {} 0x11).stmts,
          .letDecl [name] (some (bop Op.exp [lit 10, d]))] := by
  simp [emitPow10, emitIf_stmts, emitLet_stmts]

theorem step_gt (st : EvmState) (a b : U256) :
    stepOp Op.gt [a, b] st = some (.ok [b2w (b.ult a)] st) := rfl

theorem step_exp (st : EvmState) (a b : U256) :
    stepOp Op.exp [a, b] st = some (.ok [BitVec.ofNat 256 (a.toNat ^ b.toNat)] st) := rfl

theorem ten_lt_wordBound : (10 : Nat) < wordBound := lt_256_wordBound (by decide)
theorem seventySeven_lt_wordBound : (77 : Nat) < wordBound := lt_256_wordBound (by decide)

theorem op_sim_pow10 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {a : Atom}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hwf : opWF c (.pow10 a) = true)
    (hn : identsNodup tag (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env (.pow10 a)) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st
            (emitPow10 {} (identV tag env.length) (atomE tag env.length a)).stmts
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv tag Γ c κ ctx w' (v :: env)
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st
            (emitPow10 {} (identV tag env.length) (atomE tag env.length a)).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : atomWF a = true := by simpa [opWF] using hwf
  have ha := atom_eval_lt henv hwf'
  have hn0 : identsNodup tag env.length = true := identsNodup_mono tag (by omega) hn
  have hea := eval_atom tag funs (st := st) hV hn0 a
  have he77 := eval_lit funs V st 77
  have he10 := eval_lit funs V st 10
  have hgt :
      EvalExpr evm funs V st
        (bop Op.gt [atomE tag env.length a, lit 77])
        (.vals [b2w ((BitVec.ofNat 256 77).ult (BitVec.ofNat 256 (a.eval env)))] st) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil he77) hea) (step_gt _ _ _)
  rw [ult_ofNat seventySeven_lt_wordBound ha] at hgt
  simp only [Op.denote, Tx.run_pow10]
  by_cases hbig : a.eval env > Tx.pow10Max
  · simp [hbig]
    have hlt : 77 < a.eval env := by
      simpa [Tx.pow10Max] using hbig
    have hcv : b2w (decide (77 < a.eval env)) ≠ 0 := by simp [hlt, b2w]
    obtain ⟨st', hp, hh⟩ := panic_ifTrue funs V st 0x11 hgt (by
      simp [hlt, b2w, Dialect.zero, litValue]) code_0x11_lt
    refine ⟨V, st', ?_, panicBytes 0x11, hh, rfl⟩
    simp only [emitPow10_stmts, Emit.stmts_nil, List.nil_append]
    exact Step.seqStop hp halt_ne_normal
  · simp [hbig]
    have hle : a.eval env ≤ 77 := by
      simpa [Tx.pow10Max] using Nat.le_of_not_gt hbig
    have hpow : 10 ^ a.eval env < wordBound := Word.tenPow_of_le_max hle
    have hexp :
        EvalExpr evm funs V st
          (bop Op.exp [lit 10, atomE tag env.length a])
          (.vals [BitVec.ofNat 256
            ((BitVec.ofNat 256 10).toNat ^ (BitVec.ofNat 256 (a.eval env)).toNat)] st) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hea) he10) (step_exp _ _ _)
    rw [toNat_ofNat_of_lt ten_lt_wordBound, toNat_ofNat_of_lt ha] at hexp
    let V₁ := (identV tag env.length, BitVec.ofNat 256 (10 ^ a.eval env)) :: V
    have hlet : ExecStmt evm funs V st
        (.letDecl [identV tag env.length]
          (some (bop Op.exp [lit 10, atomE tag env.length a])))
        V₁ st .normal :=
      Step.letVal hexp rfl
    have hcv : b2w (decide (77 < a.eval env)) = 0 := by
      have : ¬ 77 < a.eval env := Nat.not_lt.mpr hle
      simp [this, b2w]
    refine ⟨st, ?_, ?_⟩
    · simp only [emitPow10_stmts, Emit.stmts_nil, List.nil_append]
      refine Step.seqCons (Step.ifFalse hgt ?_) (Step.seqCons hlet Step.seqNil)
      simp [hcv, Dialect.zero, litValue]
    · exact ⟨by rw [hV, toVEnv_cons], envWF_cons hpow henv, hR, hctx⟩

end Lsc.Compiler
