import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.Words
import YulSemantics.BigStep
import YulSemantics.Dialect.EVM

/-!
Environment / `Step` plumbing for `toYulFn_correct` (M1).
-/

namespace Lsc.Compiler

variable (tag : String)

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

theorem toVEnv_nil : toVEnv tag ([] : List Nat) = [] := rfl

theorem toVEnv_cons (v : Nat) (env : List Nat) :
    toVEnv tag (v :: env) =
      (identV tag env.length, BitVec.ofNat 256 v) :: toVEnv tag env := by
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

theorem get_toVEnv tag (env : List Nat) (hn : identsNodup tag env.length = true)
    {i : Nat} (hi : i < env.length) :
    VEnv.get (toVEnv tag env) (identV tag (env.length - 1 - i)) =
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
      have hn' : identsNodup tag (env.length + 1) = true := by simpa using hn
      have hne : identV tag env.length ≠ identV tag (env.length - 1 - i) := by
        intro heq
        have hlt : env.length - 1 - i < env.length + 1 :=
          Nat.lt_succ_of_le (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))
        have := identV_inj_of_nodup tag (env.length + 1) hn' (Nat.lt_succ_self _) hlt heq
        omega
      simp only [hne, ↓reduceIte]
      exact ih (identsNodup_mono tag (by omega) hn') hi'

/-- `V` agrees with `env` on every `identV` looked up at this depth.
Word `seqIf` keeps dest/phi in front of `toVEnv`; atoms only need this. -/
def localsOK (env : List Nat) (V : VEnv evm) : Prop :=
  ∀ i (hi : i < env.length),
    VEnv.get V (identV tag (env.length - 1 - i)) =
      some (BitVec.ofNat 256 (env[i]'hi))

theorem localsOK_toVEnv (env : List Nat)
    (hn : identsNodup tag env.length = true) :
    localsOK tag env (toVEnv tag env) :=
  fun _i hi => get_toVEnv tag env hn hi

theorem localsOK_of_eq {env : List Nat} {V : VEnv evm}
    (hV : V = toVEnv tag env) (hn : identsNodup tag env.length = true) :
    localsOK tag env V := by
  subst hV
  exact localsOK_toVEnv tag env hn

theorem localsOK_skip_head {env : List Nat} {V : VEnv evm} {x : YIdent} {vx : U256}
    (hok : localsOK tag env V)
    (hne : ∀ i, i < env.length → x ≠ identV tag (env.length - 1 - i)) :
    localsOK tag env ((x, vx) :: V) := by
  intro i hi
  rw [VEnv.get_cons, if_neg (hne i hi)]
  exact hok i hi

/-- `identV d` is not among the `env`-depth lookups, so it may sit in front. -/
theorem localsOK_identV_front {env : List Nat} {V : VEnv evm} (v : U256)
    (hn : identsNodup tag (env.length + 1) = true)
    (hok : localsOK tag env V) :
    localsOK tag env ((identV tag env.length, v) :: V) := by
  refine localsOK_skip_head (tag := tag) hok ?_
  intro i hi heq
  have := identV_inj_of_nodup tag (env.length + 1) hn (Nat.lt_succ_self _)
    (by omega) heq
  omega

theorem localsOK_of_identV_front {env : List Nat} {V : VEnv evm} {v : U256}
    (hn : identsNodup tag (env.length + 1) = true)
    (hok : localsOK tag env ((identV tag env.length, v) :: V)) :
    localsOK tag env V := by
  intro i hi
  have hget := hok i hi
  rw [VEnv.get_cons] at hget
  have hne : identV tag env.length ≠ identV tag (env.length - 1 - i) := by
    intro heq
    have := identV_inj_of_nodup tag (env.length + 1) hn (Nat.lt_succ_self _)
      (by omega) heq
    omega
  simp only [hne, ↓reduceIte] at hget
  exact hget

theorem ofNat_toNat_u256 (v : U256) : BitVec.ofNat 256 v.toNat = v :=
  BitVec.eq_of_toNat_eq (toNat_ofNat_of_lt (by simpa [wordBound] using v.isLt))

theorem localsOK_cons {env : List Nat} {V : VEnv evm} (v : Nat)
    (hn : identsNodup tag (env.length + 1) = true)
    (hok : localsOK tag env V) :
    localsOK tag (v :: env)
      ((identV tag env.length, BitVec.ofNat 256 v) :: V) := by
  intro i hi
  rw [VEnv.get_cons]
  cases i with
  | zero =>
    have hidx : (v :: env).length - 1 - 0 = env.length := by simp
    rw [hidx, if_pos rfl]
    rfl
  | succ i =>
    have hi' : i < env.length := by
      simp [List.length_cons] at hi
      omega
    have hidx : (v :: env).length - 1 - i.succ = env.length - 1 - i := by
      simp [List.length_cons]; omega
    have hne : identV tag env.length ≠ identV tag (env.length - 1 - i) := by
      intro heq
      have := identV_inj_of_nodup tag (env.length + 1) hn (Nat.lt_succ_self _)
        (by omega) heq
      omega
    rw [hidx, if_neg hne]
    simpa [List.getElem_cons_succ] using hok i hi'

theorem localsOK_phi_dest {env : List Nat} {V : VEnv evm} (p d0 : U256)
    (hn : identsNodup tag (env.length + 1) = true)
    (hok : localsOK tag env V) :
    localsOK tag env
      ((identPhi tag env.length, p) :: (identV tag env.length, d0) :: V) := by
  have hφ : ∀ i, i < env.length →
      identPhi tag env.length ≠ identV tag (env.length - 1 - i) :=
    fun i _ => identPhi_ne_identV tag env.length (env.length - 1 - i)
  have hd : ∀ i, i < env.length →
      identV tag env.length ≠ identV tag (env.length - 1 - i) := by
    intro i hi heq
    have := identV_inj_of_nodup tag (env.length + 1) hn (Nat.lt_succ_self _)
      (by omega) heq
    omega
  exact localsOK_skip_head tag
    (localsOK_skip_head tag hok hd) hφ

theorem restore_nil (Vb : VEnv evm) : restore ([] : VEnv evm) Vb = [] := by
  simp [restore]

theorem restore_self (V : VEnv evm) : restore V V = V := by
  simp [restore]

theorem eval_lit (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : Nat) :
    EvalExpr evm funs V st (lit n) (.vals [BitVec.ofNat 256 n] st) :=
  Step.lit

theorem eval_atom tag (funs : FunEnv evm) {env : List Nat} {V : VEnv evm} (st : EvmState)
    (hV : V = toVEnv tag env) (hn : identsNodup tag env.length = true) :
    ∀ a, EvalExpr evm funs V st (atomE tag env.length a)
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
      have hget := get_toVEnv tag env hn hi
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hget
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

/-- Atom evaluation from `localsOK` (dest/phi may sit in front of `toVEnv`). -/
theorem eval_atom_ok tag (funs : FunEnv evm) {env : List Nat} {V : VEnv evm}
    (st : EvmState) (hok : localsOK tag env V) :
    ∀ a, EvalExpr evm funs V st (atomE tag env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) := by
  intro a
  cases a with
  | lit n =>
    simp [atomE, Atom.eval]
    exact Step.lit
  | var i =>
    simp only [atomE, Atom.eval]
    split_ifs with hi
    · have hget := hok i hi
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hget
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

/-- `atomE` at the original depth after `let identV_d`. -/
theorem eval_atom_ok_cons tag (funs : FunEnv evm) {env : List Nat} {V : VEnv evm}
    (st : EvmState) (v : U256) (hok : localsOK tag env V)
    (hn : identsNodup tag (env.length + 1) = true) :
    ∀ a, EvalExpr evm funs ((identV tag env.length, v) :: V) st
      (atomE tag env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) :=
  eval_atom_ok tag funs st (by
    refine localsOK_skip_head (tag := tag) hok ?_
    intro i hi heq
    have := identV_inj_of_nodup tag (env.length + 1) hn (Nat.lt_succ_self _)
      (by omega) heq
    omega)

/-- Evaluating `atomE tag d a` after binding `v_d` — the new name is not among `a`'s lookups. -/
theorem eval_atom_cons tag (funs : FunEnv evm) {env : List Nat} {V : VEnv evm} (st : EvmState)
    (v : U256) (hV : V = toVEnv tag env) (hn : identsNodup tag (env.length + 1) = true) :
    ∀ a, EvalExpr evm funs ((identV tag env.length, v) :: V) st (atomE tag env.length a)
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
          VEnv.get ((identV tag env.length, v) :: V) (identV tag (env.length - 1 - i)) =
            some (BitVec.ofNat 256 env[i]) := by
        rw [VEnv.get_cons]
        have hne : identV tag env.length ≠ identV tag (env.length - 1 - i) := by
          intro heq
          have := identV_inj_of_nodup tag (env.length + 1) hn (by omega) (by omega) heq
          omega
        simp only [hne, ↓reduceIte]
        subst hV
        exact get_toVEnv tag env (identsNodup_mono tag (by omega) hn) hi
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact Step.var hget
    · have : env.getD i 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      rw [this]
      exact Step.lit

/-- `atomE` after `let dest` and `let phi` — neither name is among the source locals. -/
theorem eval_atom_phi_dest tag (funs : FunEnv evm) {env : List Nat} {V : VEnv evm}
    (st : EvmState) (p d0 : U256)
    (hV : V = toVEnv tag env) (hn : identsNodup tag (env.length + 1) = true) :
    ∀ a, EvalExpr evm funs
      ((identPhi tag env.length, p) :: (identV tag env.length, d0) :: V) st
      (atomE tag env.length a)
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
          VEnv.get ((identPhi tag env.length, p) ::
            (identV tag env.length, d0) :: V)
            (identV tag (env.length - 1 - i)) =
          some (BitVec.ofNat 256 env[i]) := by
        rw [VEnv.get_cons]
        have hneΦ : identPhi tag env.length ≠ identV tag (env.length - 1 - i) :=
          identPhi_ne_identV tag env.length (env.length - 1 - i)
        simp only [hneΦ, ↓reduceIte]
        rw [VEnv.get_cons]
        have hneD : identV tag env.length ≠ identV tag (env.length - 1 - i) := by
          intro heq
          have := identV_inj_of_nodup tag (env.length + 1) hn (by omega) (by omega) heq
          omega
        simp only [hneD, ↓reduceIte]
        subst hV
        exact get_toVEnv tag env (identsNodup_mono tag (by omega) hn) hi
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

theorem emitParams_zero tag (e : Emit) (off : Nat) : emitParams tag e off 0 = e := rfl

theorem emitParams_succ (e : Emit) (off n : Nat) :
    emitParams tag e off (n + 1) =
      (emitParams tag e off n).push
        (.letDecl [identV tag n]
          (some (bop Op.calldataload [lit (off + 32 * n)]))) := by
  have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
  dsimp only [emitParams]
  rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem step_calldataload (st : EvmState) (p : U256) :
    stepOp Op.calldataload [p] st = some (.ok [wordFrom st.env.calldata p.toNat] st) := rfl

theorem wordFrom_toNat_lt (cd : List UInt8) (p : Nat) :
    (wordFrom cd p).toNat < wordBound := by
  simpa [wordBound] using (wordFrom cd p).isLt

theorem decodeArgs_wf (f : FnDef) (cd : List UInt8) : EnvWF (decodeArgs f cd).reverse := by
  intro v hv
  have hv' : v ∈ decodeArgs f cd := List.mem_reverse.mp hv
  unfold decodeArgs at hv'
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv'
  exact wordFrom_toNat_lt _ _

theorem decodeArgs_length (f : FnDef) (cd : List UInt8) :
    (decodeArgs f cd).length = f.params.length := by
  simp [decodeArgs]

theorem decodeArgs_reverse_length (f : FnDef) (cd : List UInt8) :
    (decodeArgs f cd).reverse.length = f.params.length := by
  simp [decodeArgs]

theorem decodeArgs_runtime {f : FnDef} {cd : List UInt8} (hk : f.kind ≠ .constructor) :
    decodeArgs f cd =
      (List.range f.params.length).map fun i =>
        (wordFrom cd (4 + 32 * i)).toNat := by
  simp [decodeArgs, hk]

theorem params_sim (funs : FunEnv evm) (st : EvmState) (off n : Nat)
    (hbound : off + 32 * n < wordBound) :
    ExecStmts evm funs [] st (emitParams tag {} off n).stmts
      (toVEnv tag ((List.range n).map (fun i =>
        (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse) st .normal := by
  induction n with
  | zero =>
    simp [emitParams_zero, Emit.stmts_nil, toVEnv_nil]
    exact Step.seqNil
  | succ n ih =>
    have hbound' : off + 32 * n < wordBound := by
      have : 32 * n ≤ 32 * (n + 1) := Nat.mul_le_mul_left 32 (Nat.le_succ n)
      omega
    have ih' := ih hbound'
    have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    have hmap :
        (List.range (n + 1)).map (fun i => (wordFrom st.env.calldata (off + 32 * i)).toNat) =
          (List.range n).map (fun i => (wordFrom st.env.calldata (off + 32 * i)).toNat) ++
            [(wordFrom st.env.calldata (off + 32 * n)).toNat] := by
      rw [hrange, List.map_append, List.map_cons, List.map_nil]
    rw [emitParams_succ, Emit.stmts_push, hmap, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, toVEnv_cons]
    simp only [List.length_reverse, List.length_map, List.length_range]
    have hlit : (BitVec.ofNat 256 (off + 32 * n)).toNat = off + 32 * n :=
      toNat_ofNat_of_lt hbound'
    have hload :
        EvalExpr evm funs
          (toVEnv tag ((List.range n).map (fun i =>
            (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse) st
          (bop Op.calldataload [lit (off + 32 * n)])
          (.vals [wordFrom st.env.calldata (off + 32 * n)] st) :=
      Step.builtinOk (Step.argsCons Step.argsNil Step.lit)
        (by
          simp only [litValue_number, step_calldataload, hlit])
    have hlet :
        ExecStmt evm funs
          (toVEnv tag ((List.range n).map (fun i =>
            (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse) st
          (.letDecl [identV tag n]
            (some (bop Op.calldataload [lit (off + 32 * n)])))
          ((identV tag n, wordFrom st.env.calldata (off + 32 * n)) ::
            toVEnv tag ((List.range n).map (fun i =>
              (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse)
          st .normal :=
      Step.letVal hload rfl
    have hlet' :
        ExecStmt evm funs
          (toVEnv tag ((List.range n).map (fun i =>
            (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse) st
          (.letDecl [identV tag n]
            (some (bop Op.calldataload [lit (off + 32 * n)])))
          ((identV tag n,
              BitVec.ofNat 256 (wordFrom st.env.calldata (off + 32 * n)).toNat) ::
            toVEnv tag ((List.range n).map (fun i =>
              (wordFrom st.env.calldata (off + 32 * i)).toNat)).reverse)
          st .normal := by
      convert hlet using 1
      congr 1
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [toNat_ofNat_of_lt (wordFrom_toNat_lt _ _)]
    exact execStmts_append ih' (Step.seqCons hlet' Step.seqNil)

theorem hoist_append (a b : YBlock) :
    hoist evm (a ++ b) = hoist evm a ++ hoist evm b := by
  simp [hoist, List.filterMap_append]

theorem hoist_params (off n : Nat) : hoist evm (emitParams tag {} off n).stmts = [] := by
  induction n with
  | zero => simp [emitParams_zero, Emit.stmts_nil, hoist]
  | succ n ih =>
    rw [emitParams_succ, Emit.stmts_push, hoist_append, ih]
    simp [hoist]

theorem halt_ne_normal : Outcome.halt ≠ .normal := by decide

theorem VEnv.set_head (x : Ident) (v w : U256) (V : VEnv evm) :
    VEnv.set ((x, v) :: V) x w = (x, w) :: V := by
  simp [VEnv.set]

theorem VEnv.set_cons_ne {x y : Ident} {vx : U256} {V : VEnv evm} {w : U256}
    (h : x ≠ y) :
    VEnv.set ((x, vx) :: V) y w = (x, vx) :: VEnv.set V y w := by
  simp [VEnv.set, h]

theorem VEnv.get_set (V : VEnv evm) (x : Ident) (v : U256)
    (h : VEnv.get V x ≠ none) :
    VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => simp [VEnv.get] at h
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    unfold VEnv.set
    split_ifs with hx
    · subst hx
      simp [VEnv.get]
    · have h' : VEnv.get rest x ≠ none := by
        intro hn
        apply h
        rw [VEnv.get_cons, if_neg hx, hn]
      rw [VEnv.get_cons, if_neg hx]
      exact ih h'

theorem VEnv.get_set_ne {V : VEnv evm} {x y : Ident} {v : U256}
    (h : x ≠ y) :
    VEnv.get (VEnv.set V y v) x = VEnv.get V x := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨z, w⟩
    unfold VEnv.set
    split_ifs with hz
    · subst hz
      rw [VEnv.get_cons, if_neg h.symm, VEnv.get_cons, if_neg h.symm]
    · rw [VEnv.get_cons, VEnv.get_cons]
      split_ifs
      · rfl
      · exact ih

theorem VEnv.get_set_of_some {V : VEnv evm} {x : Ident} {old v : U256}
    (h : VEnv.get V x = some old) :
    VEnv.get (VEnv.set V x v) x = some v :=
  VEnv.get_set V x v (by simp [h])

theorem VEnv.setMany_one (V : VEnv evm) (x : Ident) (v : U256) :
    VEnv.setMany V [x] [v] = VEnv.set V x v := rfl

theorem localsOK_set {env : List Nat} {V : VEnv evm} {dest : YIdent} (v : U256)
    (hok : localsOK tag env V)
    (hne : ∀ i, i < env.length → dest ≠ identV tag (env.length - 1 - i)) :
    localsOK tag env (VEnv.set V dest v) := by
  intro i hi
  rw [VEnv.get_set_ne (hne i hi).symm]
  exact hok i hi

theorem restore_length {V Vb : VEnv evm} (h : V.length = Vb.length) :
    restore V Vb = Vb := by
  simp [restore, h]

theorem VEnv.set_length (V : VEnv evm) (x : Ident) (v : U256) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => simp [VEnv.set]
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    by_cases hx : y = x
    · subst hx; simp [VEnv.set]
    · rw [VEnv.set_cons_ne hx]; simp [ih]

theorem restore_set (V : VEnv evm) (dest : YIdent) (v : U256) :
    restore V (VEnv.set V dest v) = VEnv.set V dest v :=
  restore_length (VEnv.set_length V dest v).symm

/-- Extra head + in-place `dest` update restores to the in-place update. -/
theorem restore_cons_set {x dest : Ident} {vx r : U256} {V : VEnv evm}
    (h : x ≠ dest) :
    restore V (VEnv.set ((x, vx) :: V) dest r) = VEnv.set V dest r := by
  rw [VEnv.set_cons_ne h]
  unfold restore
  simp only [List.length_cons]
  rw [VEnv.set_length, Nat.add_sub_cancel_left]
  simp [List.drop]

theorem restore_tail_of_restore_cons_set {x dest : Ident} {vx r : U256}
    {V V' : VEnv evm} (hne : x ≠ dest)
    (h : restore ((x, vx) :: V) V' = VEnv.set ((x, vx) :: V) dest r) :
    restore V V' = VEnv.set V dest r := by
  rw [VEnv.set_cons_ne hne] at h
  unfold restore at h ⊢
  simp [List.length_cons] at h ⊢
  have hlen : V.length + 1 ≤ V'.length := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hz : V'.length - (V.length + 1) = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    simp [hz] at h
    have hlenV' : V'.length = V.length + 1 := by
      have := congrArg List.length h
      simp [List.length_cons] at this
      rwa [VEnv.set_length] at this
    omega
  have hsub : V'.length - V.length = V'.length - (V.length + 1) + 1 := by omega
  rw [hsub, ← List.drop_drop, h]
  simp [List.drop]

end Lsc.Compiler
