import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.Words
import YulSemantics.BigStep
import YulSemantics.Dialect.EVM

/-!
Environment / `Step` plumbing for `toYulFn_correct` (M1).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

theorem envWF_nil : EnvWF [] := by
  intro _ h; cases h

theorem envWF_cons {v env} (hv : v < wordBound) (h : EnvWF env) : EnvWF (v :: env) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hv
  · exact h x hx

theorem toVEnv_nil : toVEnv ([] : List Nat) = [] := rfl

theorem toVEnv_cons (v : Nat) (env : List Nat) :
    toVEnv (v :: env) =
      (identV env.length, BitVec.ofNat 256 v) :: toVEnv env := by
  unfold toVEnv
  rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons]
  have hhead : env.length + 1 - 1 - 0 = env.length := by omega
  simp only [hhead]
  congr 1
  rw [List.zip_map_right, List.map_map]
  apply List.map_congr_left
  intro p _hp
  rcases p with ⟨x, j⟩
  simp only [Function.comp, Prod.map, id]
  congr 1
  rw [Nat.add_sub_cancel, Nat.sub_succ, Nat.pred_eq_sub_one, Nat.sub_right_comm]

theorem VEnv.get_cons {x : Ident} {v : U256} {V : VEnv evm} {y : Ident} :
    VEnv.get ((x, v) :: V) y = if x = y then some v else VEnv.get V y := by
  simp only [VEnv.get, List.find?]
  by_cases h : x = y
  · simp [h]
  · simp [h]

theorem get_toVEnv (env : List Nat) (hn : identsNodup env.length = true)
    {i : Nat} (hi : i < env.length) :
    VEnv.get (toVEnv env) (identV (env.length - 1 - i)) =
      some (BitVec.ofNat 256 env[i]) := by
  induction env generalizing i with
  | nil => cases hi
  | cons v env ih =>
    rw [toVEnv_cons]
    simp only [List.length_cons]
    have hlookup : env.length + 1 - 1 - i = env.length - i := by omega
    rw [hlookup, VEnv.get_cons]
    cases i with
    | zero =>
      simp
    | succ i =>
      have hi' : i < env.length := Nat.succ_lt_succ_iff.mp hi
      have hidx : env.length - (i + 1) = env.length - 1 - i := by omega
      rw [hidx]
      have hn' : identsNodup (env.length + 1) = true := by simpa using hn
      have hne : identV env.length ≠ identV (env.length - 1 - i) := by
        intro heq
        have hlt : env.length - 1 - i < env.length + 1 :=
          Nat.lt_succ_of_le (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))
        have := identV_inj_of_nodup (env.length + 1) hn' (Nat.lt_succ_self _) hlt heq
        omega
      simp only [hne, ↓reduceIte]
      exact ih (identsNodup_mono (by omega) hn') hi'

theorem restore_nil (Vb : VEnv evm) : restore ([] : VEnv evm) Vb = [] := by
  simp [restore]

theorem restore_self (V : VEnv evm) : restore V V = V := by
  simp [restore]

theorem eval_lit (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : Nat) :
    EvalExpr evm funs V st (lit n) (.vals [BitVec.ofNat 256 n] st) :=
  Step.lit

theorem eval_atom (funs : FunEnv evm) {env : List Nat} {V : VEnv evm} (st : EvmState)
    (hV : V = toVEnv env) (hn : identsNodup env.length = true) :
    ∀ a, EvalExpr evm funs V st (atomE env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) := by
  intro a
  cases a with
  | lit n =>
    simp [atomE, Atom.eval]
    exact Step.lit
  | var i =>
    simp only [atomE, Atom.eval]
    split_ifs with hi
    · subst hV
      have hget := get_toVEnv env hn hi
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hget
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

/-- Evaluating `atomE d a` after binding `v_d` — the new name is not among `a`'s lookups. -/
theorem eval_atom_cons (funs : FunEnv evm) {env : List Nat} {V : VEnv evm} (st : EvmState)
    (v : U256) (hV : V = toVEnv env) (hn : identsNodup (env.length + 1) = true) :
    ∀ a, EvalExpr evm funs ((identV env.length, v) :: V) st (atomE env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) := by
  intro a
  cases a with
  | lit n =>
    simp [atomE, Atom.eval]
    exact Step.lit
  | var i =>
    simp only [atomE, Atom.eval]
    split_ifs with hi
    · have hget :
          VEnv.get ((identV env.length, v) :: V) (identV (env.length - 1 - i)) =
            some (BitVec.ofNat 256 env[i]) := by
        rw [VEnv.get_cons]
        have hne : identV env.length ≠ identV (env.length - 1 - i) := by
          intro heq
          have := identV_inj_of_nodup (env.length + 1) hn (by omega) (by omega) heq
          omega
        simp only [hne, ↓reduceIte]
        subst hV
        exact get_toVEnv env (identsNodup_mono (by omega) hn) hi
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hget
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

theorem execStmts_append {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv evm} {st1 : EvmState} {ss2 : YBlock}
    {V2 : VEnv evm} {st2 : EvmState} {o : Outcome}
    (h1 : ExecStmts evm funs V st ss1 V1 st1 .normal)
    (h2 : ExecStmts evm funs V1 st1 ss2 V2 st2 o) :
    ExecStmts evm funs V st (ss1 ++ ss2) V2 st2 o := by
  induction ss1 generalizing V st V1 st1 with
  | nil =>
    cases h1
    exact h2
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail =>
      exact Step.seqCons hhead (ih htail h2)
    | seqStop _ hne =>
      exact (hne rfl).elim

theorem execStmts_append_halt {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv evm} {st1 : EvmState} {ss2 : YBlock}
    (h1 : ExecStmts evm funs V st ss1 V1 st1 .halt) :
    ExecStmts evm funs V st (ss1 ++ ss2) V1 st1 .halt := by
  induction ss1 generalizing V st with
  | nil =>
    cases h1
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail =>
      exact Step.seqCons hhead (ih htail)
    | seqStop hs ho =>
      exact Step.seqStop hs ho

def notFunDef : YStmt → Bool
  | .funDef .. => false
  | _ => true

theorem hoist_nil_of {ss : YBlock} (h : ∀ s ∈ ss, notFunDef s = true) :
    hoist evm ss = [] := by
  simp only [hoist]
  refine List.filterMap_eq_nil_iff.mpr ?_
  intro s hs
  have hs' := h s hs
  cases s <;> simp [notFunDef] at hs' ⊢

theorem Emit.stmts_nil : ({} : Emit).stmts = [] := rfl

theorem Emit.stmts_push (e : Emit) (s : YStmt) :
    (e.push s).stmts = e.stmts ++ [s] := by
  simp [Emit.push, Emit.stmts, List.reverse_cons]

theorem emitParams_zero (e : Emit) (off : Nat) : emitParams e off 0 = e := rfl

theorem halt_ne_normal : Outcome.halt ≠ .normal := by decide

end Lsc.Compiler
