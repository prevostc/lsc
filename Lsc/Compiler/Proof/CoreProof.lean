import Lsc.Compiler.Proof.OpsMulDiv
import Lsc.Compiler.Proof.OpsPow10
import Lsc.Compiler.Proof.OpsCtx
import Lsc.Compiler.Proof.CallState
import Lsc.Compiler.CoreDefs
import YulSemantics.Observation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of S1 Core → Yul simulation. The exported guarantee is
`Lsc.Compiler.CoreTheorems.toYulFn_correct_callFree`; helpers stay in
`Lsc.Compiler` so the rest of the proof tree keeps its names.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem m1frag_letOp {t op} {k : Core t} :
    M1Frag (.letOp op k) ↔ M1Op op ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_seq {t s} {k : Core t} :
    M1Frag (.seq s k) ↔ M1Stmt s ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_letPure {t p args} {k : Core t} :
    M1Frag (.letPure p args k) ↔ p = .id ∧ args.length = 1 ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_ite {t c} {a b : Core t} :
    M1Frag (.ite c a b) ↔ M1Cond c ∧ M1Frag a ∧ M1Frag b := by
  simp [M1Frag]

theorem m1frag_seqIf {t u c} {th el : Core t} {k : Core u} :
    M1Frag (.seqIf c th el k) ↔
      match t with
      | .pair _ _ => False
      | _ => M1Cond c ∧ M1Frag th ∧ M1Frag el ∧ M1Frag k := by
  cases t <;> simp [M1Frag]

/-- Word-like Core results as `Nat` (for dest/phi assignment). -/
def retAsNat {t : RetTy} (v : t.denote) : Nat :=
  match t with
  | .word => v
  | .addr => v
  | .flag => v
  | .unit | .pair _ _ => 0

def retTyWordLike : RetTy → Prop
  | .word | .addr | .flag => True
  | .unit | .pair _ _ => False

theorem retTyWordLike_cases {t : RetTy} (ht : retTyWordLike t) :
    t = .word ∨ t = .addr ∨ t = .flag := by
  cases t <;> simp [retTyWordLike] at ht <;> simp

instance (t : RetTy) : Decidable (retTyWordLike t) :=
  match t with
  | .word | .addr | .flag => isTrue trivial
  | .unit | .pair _ _ => isFalse fun h => False.elim h

theorem coreExtraDepth_seqIf_wordLike {t u : RetTy} (ht : retTyWordLike t)
    (cond : Cond) (th el : Core t) (k : Core u) :
    coreExtraDepth (.seqIf cond th el k) =
      max (max (coreExtraDepth th) (coreExtraDepth el)) (coreExtraDepth k + 1) := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t <;> rfl

theorem seqIf_wordLike_depth_le {t u : RetTy} (ht : retTyWordLike t)
    (cond : Cond) (th el : Core t) (k : Core u) :
    coreExtraDepth th ≤ coreExtraDepth (.seqIf cond th el k) ∧
    coreExtraDepth el ≤ coreExtraDepth (.seqIf cond th el k) ∧
    1 ≤ coreExtraDepth (.seqIf cond th el k) ∧
    coreExtraDepth k + 1 ≤ coreExtraDepth (.seqIf cond th el k) := by
  rw [coreExtraDepth_seqIf_wordLike ht]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem except_ok_prod {ε α β γ} (p : α × β) (f : α → β → γ) (g : ε → γ) :
    (match (Except.ok p : Except ε (α × β)) with
      | .ok (a, b) => f a b
      | .error e => g e) = f p.1 p.2 := by
  rcases p with ⟨a, b⟩
  rfl

theorem except_error_prod {ε α β γ} (err : ε) (f : α → β → γ) (g : ε → γ) :
    (match (Except.error err : Except ε (α × β)) with
      | .ok (a, b) => f a b
      | .error e => g e) = g err := rfl

theorem coreWF_letOp {c op t} {k : Core t} :
    coreWF c (.letOp op k) = true ↔ opWF c op = true ∧ coreWF c k = true := by
  simp [coreWF, Bool.and_eq_true]

theorem coreWF_seq {c s t} {k : Core t} :
    coreWF c (.seq s k) = true ↔ stmtWF c s = true ∧ coreWF c k = true := by
  simp [coreWF, Bool.and_eq_true]

theorem coreWF_seqIf {c t u cond} {th el : Core t} {k : Core u} :
    coreWF c (.seqIf cond th el k) = true ↔
      condWF cond = true ∧ coreWF c th = true ∧ coreWF c el = true ∧
        coreWF c k = true ∧
        match t with
        | .pair _ _ => False
        | _ => True := by
  cases t <;> simp [coreWF, and_assoc]

theorem m1frag_seqIf_wordLike {t u c} {th el : Core t} {k : Core u}
    (ht : retTyWordLike t) :
    M1Frag (.seqIf c th el k) ↔
      M1Cond c ∧ M1Frag th ∧ M1Frag el ∧ M1Frag k := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t <;> simp [M1Frag]

theorem coreWF_seqIf_wordLike {c t u cond} {th el : Core t} {k : Core u}
    (ht : retTyWordLike t) :
    coreWF c (.seqIf cond th el k) = true ↔
      condWF cond = true ∧ coreWF c th = true ∧ coreWF c el = true ∧
        coreWF c k = true := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t
    <;> simp [coreWF, and_assoc]

theorem length_eq_one {α} {l : List α} : l.length = 1 ↔ ∃ a, l = [a] := by
  cases l with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons _ _ => simp

theorem length_eq_three {α} {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp
  | cons a l1 =>
    cases l1 with
    | nil => simp
    | cons b l2 =>
      cases l2 with
      | nil => simp
      | cons c l3 =>
        cases l3 with
        | nil => simp
        | cons _ _ => simp

theorem length_eq_four {α} {l : List α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] := by
  cases l with
  | nil => simp
  | cons a l1 =>
    cases l1 with
    | nil => simp
    | cons b l2 =>
      cases l2 with
      | nil => simp
      | cons c l3 =>
        cases l3 with
        | nil => simp
        | cons d l4 =>
          cases l4 with
          | nil => simp
          | cons _ _ => simp

theorem HaltKind.stop_commits : HaltKind.stop.commits = true := rfl
theorem HaltKind.revert_commits : HaltKind.revert.commits = false := rfl
theorem HaltKind.ret_commits : HaltKind.ret.commits = true := rfl

theorem haltSuccess_commits {t : RetTy} {v : t.denote} {h} (hs : haltSuccess t v h) :
    ∃ k bs, h = some (k, bs) ∧ k.commits = true := by
  unfold haltSuccess at hs
  split at hs
  · exact ⟨.stop, [], hs, rfl⟩
  · exact ⟨.ret, abiBytes (retWords (t := t) v), hs, rfl⟩

theorem haltSuccess_word {v : Nat} {h}
    (hh : h = some (.ret, wordBytes v)) : haltSuccess .word v h := by
  simp [haltSuccess, hh, retWords, abiBytes_singleton]

theorem haltSuccess_addr {v : Address} {h}
    (hh : h = some (.ret, wordBytes (v : Nat))) : haltSuccess .addr v h := by
  simp [haltSuccess, hh, retWords]
  exact (abiBytes_singleton (v : Nat)).symm

theorem haltSuccess_flag {v : Flag} {h}
    (hh : h = some (.ret, wordBytes (v : Nat))) : haltSuccess .flag v h := by
  simp [haltSuccess, hh, retWords]
  exact (abiBytes_singleton (v : Nat)).symm

theorem haltSuccess_pair_ww {v0 v1 : Nat} {h}
    (hh : h = some (.ret, wordBytes v0 ++ wordBytes v1)) :
    haltSuccess (.pair .word .word) (v0, v1) h := by
  simp [haltSuccess, hh, retWords, abiBytes]

theorem exec_switch_halt {funs V st V' st'} {cnd : YExpr} {eA eB body : YBlock} {cv : U256}
    (he : EvalExpr evm funs V st cnd (.vals [cv] st))
    (hsel : selectSwitch evm cv [(YulSemantics.Literal.number 0, eB)] (some eA) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: funs) V st body V' st' .halt) :
    ExecStmts evm funs V st
      [.switch cnd [(YulSemantics.Literal.number 0, eB)] (some eA)]
      (restore V V') st' .halt := by
  refine Step.seqStop ?_ halt_ne_normal
  exact exec_switch_stmt he hsel hhoist hexec

/-- `switch` as a singleton statement list, any outcome (fall-through or halt). -/
theorem exec_switch {funs V st V' st' o} {cnd : YExpr} {eA eB body : YBlock} {cv : U256}
    (he : EvalExpr evm funs V st cnd (.vals [cv] st))
    (hsel : selectSwitch evm cv [(YulSemantics.Literal.number 0, eB)] (some eA) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: funs) V st body V' st' o) :
    ExecStmts evm funs V st
      [.switch cnd [(YulSemantics.Literal.number 0, eB)] (some eA)]
      (restore V V') st' o := by
  cases o with
  | normal =>
    exact Step.seqCons (exec_switch_stmt he hsel hhoist hexec) Step.seqNil
  | halt =>
    exact Step.seqStop (exec_switch_stmt he hsel hhoist hexec) halt_ne_normal
  | «leave» | «break» | «continue» =>
    exact Step.seqStop (exec_switch_stmt he hsel hhoist hexec) (by simp)

theorem exec_let_zero {funs V st} (n : YIdent) :
    ExecStmt evm funs V st (.letDecl [n] (some (lit 0)))
      ((n, (0 : U256)) :: V) st .normal :=
  Step.letVal (eval_lit funs V st 0) rfl

/-- Unfold `seqIf` as bind into `seqIfCont` when the branch type is word-like. -/
theorem denote_seqIf_wordLike {S X E ε} {Γ : ContractSchema S X E ε}
    {t u : RetTy} (ht : retTyWordLike t) (c : Cond) (th el : Core t) (k : Core u)
    (env : List Nat) :
    Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Core.seqIfCont Γ v k env := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t <;> rfl

/-- `seqIf` continuation for word-like branches is `k` under `retAsNat v`. -/
theorem seqIfCont_retAsNat {S X E ε} {Γ : ContractSchema S X E ε}
    {t u : RetTy} (v : t.denote) (k : Core u) (env : List Nat)
    (ht : t = .word ∨ t = .addr ∨ t = .flag) :
    Core.seqIfCont Γ v k env = Core.denote Γ k (retAsNat v :: env) := by
  rcases ht with h | h | h <;> subst t <;> rfl

/-- Successful `emitSeqIfWord`: dest holds `n` after the selected branch. -/
theorem exec_seqIfWord_ok {funs : FunEnv evm} {V : VEnv evm}
    {st st' : EvmState} {VBr : VEnv evm} {n d : Nat}
    {cond : Cond} {eA eB : Emit} {cv : U256} {body : YBlock}
    (hcond : EvalExpr evm ([] :: funs)
      ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
      st (emitCond tag d cond) (.vals [cv] st))
    (hsel : selectSwitch evm cv
      [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: [] :: funs)
      ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
      st body VBr st' Outcome.normal)
    (hrest : restore
        ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr =
      VEnv.set
        ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
        (identPhi tag d) (BitVec.ofNat 256 n)) :
    ExecStmts evm funs V st
      (emitSeqIfWord tag {} d cond eA eB).stmts
      ((identV tag d, BitVec.ofNat 256 n) :: V) st' Outcome.normal := by
  have hΦV : identPhi tag d ≠ identV tag d := identPhi_ne_identV tag d d
  have hletD := exec_let_zero (funs := funs) (V := V) (st := st) (identV tag d)
  have hletP := exec_let_zero (funs := [] :: funs)
    (V := (identV tag d, (0 : U256)) :: V) (st := st) (identPhi tag d)
  have hVsw :
      restore
        ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr =
      (identPhi tag d, BitVec.ofNat 256 n) ::
        (identV tag d, (0 : U256)) :: V := by
    rw [hrest, VEnv.set_head]
  have hePhi :
      EvalExpr evm ([] :: funs)
        (restore
          ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr)
        st' (var (identPhi tag d))
        (.vals [BitVec.ofNat 256 n] st') := by
    rw [hVsw]; exact Step.var (by rw [VEnv.get_cons, if_pos rfl])
  have hassign :
      ExecStmt evm ([] :: funs)
        (restore
          ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr)
        st' (.assign [identV tag d] (var (identPhi tag d)))
        ((identPhi tag d, BitVec.ofNat 256 n) ::
          (identV tag d, BitVec.ofNat 256 n) :: V)
        st' .normal := by
    have h0 := Step.assignVal (D := evm) (vars := [identV tag d]) hePhi rfl
    have hset :
        VEnv.set
          (restore
            ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr)
          (identV tag d) (BitVec.ofNat 256 n) =
        (identPhi tag d, BitVec.ofNat 256 n) ::
          (identV tag d, BitVec.ofNat 256 n) :: V := by
      rw [hVsw, VEnv.set_cons_ne hΦV, VEnv.set_head]
    convert h0
    exact hset.symm
  have hsw := exec_switch (funs := [] :: funs) hcond hsel hhoist hexec
  have hinner :
      ExecStmts evm ([] :: funs)
        ((identV tag d, (0 : U256)) :: V) st
        (seqIfWordInner tag d cond eA eB)
        ((identPhi tag d, BitVec.ofNat 256 n) ::
          (identV tag d, BitVec.ofNat 256 n) :: V)
        st' .normal := by
    rw [seqIfWordInner_eq]
    exact execStmts_append (Step.seqCons hletP Step.seqNil)
      (execStmts_append hsw (Step.seqCons hassign Step.seqNil))
  have hblk :
      ExecStmt evm funs ((identV tag d, (0 : U256)) :: V) st
        (.block (seqIfWordInner tag d cond eA eB))
        ((identV tag d, BitVec.ofNat 256 n) :: V) st' .normal := by
    have hb := Step.block (D := evm) (by
      rw [hoist_seqIfWordInner]; exact hinner)
    rw [restore_call_assign (ok := identPhi tag d) (name := identV tag d)] at hb
    exact hb
  rw [emitSeqIfWord_nil_stmts]
  exact Step.seqCons hletD (Step.seqCons hblk Step.seqNil)

/-- Halt in a `seqIf` word branch: switch restores before the outer block. -/
theorem exec_seqIfWord_halt {funs : FunEnv evm} {V : VEnv evm}
    {st st' : EvmState} {VBr : VEnv evm} {d : Nat}
    {cond : Cond} {eA eB : Emit} {cv : U256} {body : YBlock}
    (hcond : EvalExpr evm ([] :: funs)
      ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
      st (emitCond tag d cond) (.vals [cv] st))
    (hsel : selectSwitch evm cv
      [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: [] :: funs)
      ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
      st body VBr st' Outcome.halt) :
    ExecStmts evm funs V st
      (emitSeqIfWord tag {} d cond eA eB).stmts
      (restore ((identV tag d, (0 : U256)) :: V)
        (restore
          ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr))
      st' Outcome.halt := by
  have hletD := exec_let_zero (funs := funs) (V := V) (st := st) (identV tag d)
  have hletP := exec_let_zero (funs := [] :: funs)
    (V := (identV tag d, (0 : U256)) :: V) (st := st) (identPhi tag d)
  have hinner :
      ExecStmts evm ([] :: funs)
        ((identV tag d, (0 : U256)) :: V) st
        (seqIfWordInner tag d cond eA eB)
        (restore
          ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V) VBr)
        st' .halt := by
    rw [seqIfWordInner_eq]
    exact Step.seqCons hletP (Step.seqStop
      (exec_switch_stmt hcond hsel hhoist hexec) halt_ne_normal)
  have hblk :
      ExecStmt evm funs ((identV tag d, (0 : U256)) :: V) st
        (.block (seqIfWordInner tag d cond eA eB))
        (restore ((identV tag d, (0 : U256)) :: V)
          (restore
            ((identPhi tag d, (0 : U256)) :: (identV tag d, (0 : U256)) :: V)
            VBr))
        st' .halt :=
    Step.block (D := evm) (by rw [hoist_seqIfWordInner]; exact hinner)
  rw [emitSeqIfWord_nil_stmts]
  exact Step.seqCons hletD (Step.seqStop hblk halt_ne_normal)

theorem execStmts_stop_after {funs V st ss V1 st1}
    (h : ExecStmts evm funs V st ss V1 st1 .normal) :
    ExecStmts evm funs V st (ss ++ [stopStmt]) V1
      { st1 with halted := some (.stop, []) } .halt :=
  execStmts_append h (stop_sim funs V1 st1)

/-- Post-state of an optional lock-clear: identity when `clearLock` is false. -/
def stAfterLockClear (clearLock : Bool) (st : EvmState) : EvmState :=
  if clearLock then stTstore st (BitVec.ofNat 256 reentrancyLockSlot) 0 else st

theorem memOnly_stAfterLockClear (clearLock : Bool) (st : EvmState) :
    MemOnly st (stAfterLockClear clearLock st) := by
  cases clearLock with
  | false => simp [stAfterLockClear, MemOnly]
  | true => simpa [stAfterLockClear] using memOnly_tstore st _ _

theorem execStmts_maybe_lockClear {funs V st rest V' st' o}
    (clearLock : Bool) (hstatic : st.env.static = false)
    (h : ExecStmts evm funs V (stAfterLockClear clearLock st) rest V' st' o) :
    ExecStmts evm funs V st
      ((if clearLock then [lockClearStmt] else []) ++ rest) V' st' o := by
  cases clearLock with
  | false => simpa [stAfterLockClear] using h
  | true =>
    simpa [stAfterLockClear] using execStmts_lockClear_cons hstatic h

theorem execStmts_maybeLock {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    (clearLock : Bool) (hstatic : st.env.static = false) :
    ExecStmts evm funs V st (if clearLock then [lockClearStmt] else [])
      V (stAfterLockClear clearLock st) .normal := by
  cases clearLock with
  | false => simpa [stAfterLockClear] using (Step.seqNil : ExecStmts evm funs V st [] V st .normal)
  | true => simpa [stAfterLockClear] using execStmts_lockClear funs V st hstatic

theorem stmt_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {s : Lsc.Stmt}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Stmt s) (hwf : stmtWF c s = true)
    (hn : identsNodup tag env.length = true) :
    match Tx.run (Stmt.denote Γ env s) ctx w with
    | .ok (_, w') =>
        ∃ st', ExecStmts evm funs V st (emitStmt tag c {} env.length s).stmts V st' .normal ∧
          Inv tag Γ c κ ctx w' env V st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st (emitStmt tag c {} env.length s).stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  match s with
  | .store f val =>
    simp [Stmt.denote, Tx.run_store]
    exact stmt_sim_store tag funs hinv hΓ hκ hlen hwf hn
  | .storeMap f k val =>
    simp [Stmt.denote, Tx.run_storeMap]
    exact stmt_sim_storeMap tag funs hinv hΓ hκ hlen hwf hn
  | .storeMap2 f k1 k2 val =>
    simp [Stmt.denote, Tx.run_storeMap2]
    exact stmt_sim_storeMap2 tag funs hinv hΓ hκ hlen hwf hn
  | .emit ev args =>
    rcases (hM1 : args.length = 0 ∨ args.length = 1 ∨ args.length = 3 ∨ args.length = 4)
      with h0 | h1 | h3 | h4
    · match args with
      | [] =>
        simp [Stmt.denote, Tx.run_emit]
        exact stmt_sim_emit0 tag funs hinv hwf
      | _ :: _ => cases h0
    · have ⟨a, hargs⟩ := length_eq_one.mp h1
      subst hargs
      simp [Stmt.denote, Tx.run_emit]
      exact stmt_sim_emit tag funs hinv hwf hn
    · have ⟨a, b, c, hargs⟩ := length_eq_three.mp h3
      subst hargs
      simp [Stmt.denote, Tx.run_emit]
      exact stmt_sim_emit3 tag funs hinv hwf hn
    · have ⟨a, b, c, d, hargs⟩ := length_eq_four.mp h4
      subst hargs
      simp [Stmt.denote, Tx.run_emit]
      exact stmt_sim_emit4 tag funs hinv hwf hn
  | .require cond err args =>
    have ⟨hC, hlen⟩ := (hM1 : M1Cond cond ∧ args.length = 0)
    match args with
    | [] => exact stmt_sim_require tag funs hinv hC hwf hn
    | _ :: _ => cases hlen
  | .revert err args =>
    have hnil : args.length = 0 := hM1
    match args with
    | [] => exact stmt_sim_revert tag funs hinv hwf
    | _ :: _ => cases hnil
  | .call .. =>
    exact (show False from hM1).elim
  | .view .. =>
    exact (show False from hM1).elim

theorem op_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {op : Lsc.Op}
    (funs : FunEnv evm) (hinv : Inv tag Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Op op) (hwf : opWF c op = true)
    (hn : identsNodup tag (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env op) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st ((emitLetOp tag c {} env.length op).getD {}).stmts
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv tag Γ c κ ctx w' (v :: env)
            ((identV tag env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st ((emitLetOp tag c {} env.length op).getD {}).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  match op with
  | .load f =>
    simp [emitLetOp_load, Op.denote, Tx.run_load]
    exact op_sim_load tag funs hinv hwf hn
  | .loadMap f k =>
    simp only [emitLetOp_loadMap]
    simp [Op.denote, Tx.run_loadMap]
    exact op_sim_loadMap tag funs hinv hlen hwf hn
  | .loadMap2 f k1 k2 =>
    simp only [emitLetOp_loadMap2]
    simp [Op.denote, Tx.run_loadMap2]
    exact op_sim_loadMap2 tag funs hinv hlen hwf hn
  | .sender =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_sender]
    exact op_sim_sender tag funs hinv hn
  | .value =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_value]
    exact op_sim_value tag funs hinv hn
  | .timestamp =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_timestamp]
    exact op_sim_timestamp tag funs hinv hn
  | .blockNumber =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_blockNumber]
    exact op_sim_blockNumber tag funs hinv hn
  | .selfAddress =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_selfAddress]
    exact op_sim_selfAddress tag funs hinv hn
  | .addChecked a b =>
    simp only [emitLetOp_addChecked]
    exact op_sim_addChecked tag funs hinv hwf hn
  | .subChecked a b =>
    simp only [emitLetOp_subChecked]
    exact op_sim_subChecked tag funs hinv hwf hn
  | .mulChecked a b =>
    simp only [emitLetOp_mulChecked]
    exact op_sim_mulChecked tag funs hinv hwf hn
  | .divChecked a b =>
    simp only [emitLetOp_divChecked]
    exact op_sim_divChecked tag funs hinv hwf hn
  | .mulDivDown a b d =>
    simp only [emitLetOp_mulDivDown]
    exact op_sim_mulDivDown tag funs hinv hwf hn
  | .mulDivUp a b d =>
    simp only [emitLetOp_mulDivUp]
    exact op_sim_mulDivUp tag funs hinv hwf hn
  | .pow10 d =>
    simp only [emitLetOp_pow10]
    exact op_sim_pow10 tag funs hinv hwf hn
  | .pure a =>
    simp only [emitLetOp_pure]
    exact op_sim_pure tag funs hinv hwf hn
  | .call .. =>
    exact (show False from hM1).elim
  | .view .. =>
    exact (show False from hM1).elim
  | .send .. =>
    exact (show False from hM1).elim
  | .selfBalance =>
    exact (show False from hM1).elim

/-- Structural size for the `core_sim_fall` / `core_toVar_sim` mutual. -/
def coreSize : {t : RetTy} → Core t → Nat
  | _, .ret _ => 1
  | _, .opTail _ => 1
  | _, .opTailAddr _ => 1
  | _, .opTailFlag _ => 1
  | _, .stmtTail _ => 1
  | _, .revertTail .. => 1
  | _, .letOp _ k => coreSize k + 1
  | _, .seq _ k => coreSize k + 1
  | _, .letPure _ _ k => coreSize k + 1
  | _, .ite _ a b => coreSize a + coreSize b + 1
  | _, .seqIf _ th el k => coreSize th + coreSize el + coreSize k + 1
  | _, .letCall _ _ k => coreSize k + 1
  | _, .callTail _ _ => 1

theorem emitReturnUnit_false (e : Emit) : emitReturnUnit e false = e := rfl

/-- Invert word-like `emitCore` of `seqIf` without refining the branch type. -/
theorem emitCore_seqIf_wordLike_prefix {c : ContractDef} {t u : RetTy}
    {cond : Cond} {th el : Core t} {k : Core u} {e' : Emit}
    {d : Nat} {haltUnit clearLock : Bool} (ht : retTyWordLike t)
    (hem : emitCore tag c {} d haltUnit (.seqIf cond th el k) clearLock = some e') :
    ∃ eA eB eK,
      emitCoreToVar tag c {} d (identPhi tag d) th = some eA ∧
      emitCoreToVar tag c {} d (identPhi tag d) el = some eB ∧
      emitCore tag c {} (d + 1) haltUnit k clearLock = some eK ∧
      e'.stmts = (emitSeqIfWord tag {} d cond eA eB).stmts ++ eK.stmts := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t
  all_goals
    obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d
      (identPhi tag d)
    obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d
      (identPhi tag d)
    simp only [emitCore, hA, hB] at hem
    obtain ⟨eK, hKpre, hst⟩ := emitCore_prefix tag hem
    exact ⟨eA, eB, eK, hA, hB, hKpre, hst⟩

/-- Invert word-like `emitCoreToVar` of `seqIf` without refining the branch type. -/
theorem emitCoreToVar_seqIf_wordLike_prefix {c : ContractDef} {t u : RetTy}
    {cond : Cond} {th el : Core t} {k : Core u} {e' : Emit}
    {d : Nat} {dest : YIdent} (ht : retTyWordLike t)
    (hem : emitCoreToVar tag c {} d dest (.seqIf cond th el k) = some e') :
    ∃ eA eB eK,
      emitCoreToVar tag c {} d (identPhi tag d) th = some eA ∧
      emitCoreToVar tag c {} d (identPhi tag d) el = some eB ∧
      emitCoreToVar tag c {} (d + 1) dest k = some eK ∧
      e'.stmts = (emitSeqIfWord tag {} d cond eA eB).stmts ++ eK.stmts := by
  rcases retTyWordLike_cases ht with h | h | h <;> subst t
  all_goals
    obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) d
      (identPhi tag d)
    obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) d
      (identPhi tag d)
    simp only [emitCoreToVar, hA, hB] at hem
    obtain ⟨eK, hKpre, hst⟩ := emitCoreToVar_prefix tag hem
    exact ⟨eA, eB, eK, hA, hB, hKpre, hst⟩


/-- Index of a `Core` (for refined `cases tBr` without capturing `tBr`). -/
abbrev coreRetTy {t : RetTy} (_ : Core t) : RetTy := t

/-- `core_toVar_sim` after `hΓ / hκ / hlen / hM1 / ht`. -/
abbrev CoreToVarSimHyp {S X E ε}
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (ctx : Ctx) {t : RetTy} (core : Core t) : Prop :=
  ∀ (dest : YIdent) (hneDest : ∀ n, dest ≠ identV tag n)
    {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    {old : U256}
    (hget : VEnv.get V dest = some old) (funs : FunEnv evm)
    (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {e' : Emit} (hem : emitCoreToVar tag c {} env.length dest core = some e'),
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
          VEnv.get V' dest = some (BitVec.ofNat 256 (retAsNat v)) ∧
          R c Γ κ w' st' ∧ ctxRel ctx st' ∧
          restore V V' = VEnv.set V dest (BitVec.ofNat 256 (retAsNat v)) ∧
          retAsNat v < wordBound
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes

/-- `core_sim_fall` after `hΓ / hκ / hlen / hM1 / ht`. -/
abbrev CoreFallSimHyp {S X E ε}
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (ctx : Ctx) {t : RetTy} (core : Core t) : Prop :=
  ∀ {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    (funs : FunEnv evm)
    (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {e' : Emit} (hem : emitCore tag c {} env.length false core = some e'),
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (_, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
          R c Γ κ w' st' ∧ ctxRel ctx st' ∧ restore V V' = V
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes

/-- `core_sim` after `hhalt / hΓ / hκ / hlen / hM1`. -/
abbrev CoreHaltSimHyp {S X E ε}
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (ctx : Ctx) (haltUnit : Bool)
    {t : RetTy} (core : Core t) : Prop :=
  ∀ {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    (funs : FunEnv evm)
    (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {clearLock : Bool} {e' : Emit}
    (hem : emitCore tag c {} env.length haltUnit core clearLock = some e'),
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          haltSuccess t v st'.halted ∧ R c Γ κ w' st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes

/-- Word-like `seqIf` fall-through, parameterized by branch `toVar` IHs. -/
theorem seqIf_wordLike_fall {S X E ε} {c : ContractDef}
    {Γ : ContractSchema S X E ε} {κ ctx}
    {t u : RetTy} (htBr : retTyWordLike t) (htU : u = .unit)
    {cond : Cond} {th el : Core t} {k : Core u}
    (hM1 : M1Frag (.seqIf cond th el k))
    (hthToVar : CoreToVarSimHyp (tag := tag) c Γ κ ctx th)
    (helToVar : CoreToVarSimHyp (tag := tag) c Γ κ ctx el)
    (ihk : M1Frag k → u = .unit → CoreFallSimHyp (tag := tag) c Γ κ ctx k)
    {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    (funs : FunEnv evm)
    (hwf : coreWF c (.seqIf cond th el k) = true)
    (hn : identsNodup tag (env.length + coreExtraDepth (.seqIf cond th el k)) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {e' : Emit}
    (hem : emitCore tag c {} env.length false (.seqIf cond th el k) = some e') :
    match Tx.run (Core.denote Γ (.seqIf cond th el k) env) ctx w with
    | .ok (_, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
          R c Γ κ w' st' ∧ ctxRel ctx st' ∧ restore V V' = V
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  have htEq := retTyWordLike_cases htBr
  have ⟨hC, hth, hel, hk⟩ := (m1frag_seqIf_wordLike htBr).mp hM1
  have ⟨hcWF, hthWF, helWF, hkWF⟩ := (coreWF_seqIf_wordLike htBr).mp hwf
  rw [denote_seqIf_wordLike htBr, Tx.run_bind]
  obtain ⟨eA, eB, eK, hA, hB, hKpre, hst⟩ :=
    emitCore_seqIf_wordLike_prefix (tag := tag) htBr hem
  have ⟨hthD, helD, h1D, hkD⟩ := seqIf_wordLike_depth_le htBr cond th el k
  have hn1 : identsNodup tag (env.length + 1) = true :=
    identsNodup_mono tag (Nat.add_le_add_left h1D _) hn
  have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
    identsNodup_mono tag (Nat.add_le_add_left hthD _) hn
  have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
    identsNodup_mono tag (Nat.add_le_add_left helD _) hn
  have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true :=
    identsNodup_mono tag (by
      rw [show (env.length + 1) + coreExtraDepth k =
            env.length + (coreExtraDepth k + 1) by omega]
      exact Nat.add_le_add_left hkD env.length) hn
  have hokΦ : localsOK tag env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) :=
    localsOK_phi_dest (tag := tag) 0 0 hn1 hinv.venv
  have hinvΦ : Inv tag Γ c κ ctx w env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) st :=
    ⟨hokΦ, hinv.wf, hinv.rel, hinv.ctxr⟩
  have hgetΦ : VEnv.get
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V)
      (identPhi tag env.length) = some 0 := by
    rw [VEnv.get_cons, if_pos rfl]
  have hneΦ : ∀ n, identPhi tag env.length ≠ identV tag n :=
    fun n => identPhi_ne_identV tag env.length n
  have hcond1 := eval_cond_ok tag (st := st) ([] :: funs) hokΦ hinv.wf hC hcWF
  rw [hst]
  split_ifs with hc
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eA.stmts :=
      selectSwitch_nonzero (by simp [hc, b2w])
    have hthSim :=
      hthToVar (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        hthWF hnA hinvΦ hA
    cases hrun : Tx.run (Core.denote Γ th env) ctx w with
    | ok q =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, hexecA, hgetA, hRA, hctxA, hrestA, hvA⟩ := hthSim
      rcases q with ⟨v, wA⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA hrestA
      have hinvK : Inv tag Γ c κ ctx wA (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stA :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvA hinv.wf, hRA, hctxA⟩
      have ihK := ihk hk htU (env := retAsNat v :: env) funs hkWF hnK
        hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wA with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hRK, hctxK, hrestK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hRK, hctxK, restore_of_restore_cons hrestK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, bytes, hexecA, hh, herr⟩ := hthSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VA),
        stA, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA)
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eB.stmts := by
      simp [hc, b2w]; exact selectSwitch_zero
    have helSim :=
      helToVar (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        helWF hnB hinvΦ hB
    cases hrun : Tx.run (Core.denote Γ el env) ctx w with
    | ok q =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, hexecB, hgetB, hRB, hctxB, hrestB, hvB⟩ := helSim
      rcases q with ⟨v, wB⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB hrestB
      have hinvK : Inv tag Γ c κ ctx wB (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stB :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvB hinv.wf, hRB, hctxB⟩
      have ihK := ihk hk htU (env := retAsNat v :: env) funs hkWF hnK
        hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wB with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hRK, hctxK, hrestK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hRK, hctxK, restore_of_restore_cons hrestK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, bytes, hexecB, hh, herr⟩ := helSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VB),
        stB, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB)

/-- Word-like `seqIf` assign-to-dest, parameterized by branch `toVar` IHs. -/
theorem seqIf_wordLike_toVar {S X E ε} {c : ContractDef}
    {Γ : ContractSchema S X E ε} {κ ctx}
    {t u : RetTy} (htBr : retTyWordLike t) (htK : retTyWordLike u)
    {cond : Cond} {th el : Core t} {k : Core u}
    (hM1 : M1Frag (.seqIf cond th el k))
    (hthToVar : CoreToVarSimHyp (tag := tag) c Γ κ ctx th)
    (helToVar : CoreToVarSimHyp (tag := tag) c Γ κ ctx el)
    (dest : YIdent) (hneDest : ∀ n, dest ≠ identV tag n)
    (ihk : M1Frag k → retTyWordLike u →
      ∀ {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
        {old : U256}
        (hget : VEnv.get V dest = some old) (funs : FunEnv evm)
        (hwf : coreWF c k = true)
        (hn : identsNodup tag (env.length + coreExtraDepth k) = true)
        (hinv : Inv tag Γ c κ ctx w env V st)
        {e' : Emit} (hem : emitCoreToVar tag c {} env.length dest k = some e'),
        match Tx.run (Core.denote Γ k env) ctx w with
        | .ok (v, w') =>
            ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
              VEnv.get V' dest = some (BitVec.ofNat 256 (retAsNat v)) ∧
              R c Γ κ w' st' ∧ ctxRel ctx st' ∧
              restore V V' = VEnv.set V dest (BitVec.ofNat 256 (retAsNat v)) ∧
              retAsNat v < wordBound
        | .error e =>
            ∃ V' st' bytes,
              ExecStmts evm funs V st e'.stmts V' st' .halt ∧
              st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes)
    {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    {old : U256} (hget : VEnv.get V dest = some old)
    (funs : FunEnv evm)
    (hwf : coreWF c (.seqIf cond th el k) = true)
    (hn : identsNodup tag (env.length + coreExtraDepth (.seqIf cond th el k)) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {e' : Emit}
    (hem : emitCoreToVar tag c {} env.length dest (.seqIf cond th el k) = some e') :
    match Tx.run (Core.denote Γ (.seqIf cond th el k) env) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
          VEnv.get V' dest = some (BitVec.ofNat 256 (retAsNat v)) ∧
          R c Γ κ w' st' ∧ ctxRel ctx st' ∧
          restore V V' = VEnv.set V dest (BitVec.ofNat 256 (retAsNat v)) ∧
          retAsNat v < wordBound
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  have htEq := retTyWordLike_cases htBr
  have ⟨hC, hth, hel, hk⟩ := (m1frag_seqIf_wordLike htBr).mp hM1
  have ⟨hcWF, hthWF, helWF, hkWF⟩ := (coreWF_seqIf_wordLike htBr).mp hwf
  rw [denote_seqIf_wordLike htBr, Tx.run_bind]
  obtain ⟨eA, eB, eK, hA, hB, hKpre, hst⟩ :=
    emitCoreToVar_seqIf_wordLike_prefix (tag := tag) htBr hem
  have ⟨hthD, helD, h1D, hkD⟩ := seqIf_wordLike_depth_le htBr cond th el k
  have hn1 : identsNodup tag (env.length + 1) = true :=
    identsNodup_mono tag (Nat.add_le_add_left h1D _) hn
  have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
    identsNodup_mono tag (Nat.add_le_add_left hthD _) hn
  have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
    identsNodup_mono tag (Nat.add_le_add_left helD _) hn
  have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true :=
    identsNodup_mono tag (by
      rw [show (env.length + 1) + coreExtraDepth k =
            env.length + (coreExtraDepth k + 1) by omega]
      exact Nat.add_le_add_left hkD env.length) hn
  have hokΦ : localsOK tag env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) :=
    localsOK_phi_dest (tag := tag) 0 0 hn1 hinv.venv
  have hinvΦ : Inv tag Γ c κ ctx w env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) st :=
    ⟨hokΦ, hinv.wf, hinv.rel, hinv.ctxr⟩
  have hgetΦ : VEnv.get
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V)
      (identPhi tag env.length) = some 0 := by
    rw [VEnv.get_cons, if_pos rfl]
  have hneΦ : ∀ n, identPhi tag env.length ≠ identV tag n :=
    fun n => identPhi_ne_identV tag env.length n
  have hcond1 := eval_cond_ok tag (st := st) ([] :: funs) hokΦ hinv.wf hC hcWF
  rw [hst]
  split_ifs with hc
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eA.stmts :=
      selectSwitch_nonzero (by simp [hc, b2w])
    have hthSim :=
      hthToVar (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        hthWF hnA hinvΦ hA
    cases hrun : Tx.run (Core.denote Γ th env) ctx w with
    | ok q =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, hexecA, hgetA, hRA, hctxA, hrestA, hvA⟩ := hthSim
      rcases q with ⟨v, wA⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA hrestA
      have hinvK : Inv tag Γ c κ ctx wA (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stA :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvA hinv.wf, hRA, hctxA⟩
      have hgetK : VEnv.get
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V)
          dest = some old := by
        rw [VEnv.get_cons, if_neg (Ne.symm (hneDest env.length)), hget]
      have ihK := ihk hk htK (env := retAsNat v :: env) hgetK
        funs hkWF hnK hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wA with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hgetK', hRK, hctxK, hrestK, hvK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hgetK', hRK, hctxK,
          restore_tail_of_restore_cons_set (Ne.symm (hneDest env.length)) hrestK,
          hvK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, bytes, hexecA, hh, herr⟩ := hthSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VA),
        stA, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA)
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eB.stmts := by
      simp [hc, b2w]; exact selectSwitch_zero
    have helSim :=
      helToVar (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        helWF hnB hinvΦ hB
    cases hrun : Tx.run (Core.denote Γ el env) ctx w with
    | ok q =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, hexecB, hgetB, hRB, hctxB, hrestB, hvB⟩ := helSim
      rcases q with ⟨v, wB⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB hrestB
      have hinvK : Inv tag Γ c κ ctx wB (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stB :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvB hinv.wf, hRB, hctxB⟩
      have hgetK : VEnv.get
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V)
          dest = some old := by
        rw [VEnv.get_cons, if_neg (Ne.symm (hneDest env.length)), hget]
      have ihK := ihk hk htK (env := retAsNat v :: env) hgetK
        funs hkWF hnK hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wB with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hgetK', hRK, hctxK, hrestK, hvK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hgetK', hRK, hctxK,
          restore_tail_of_restore_cons_set (Ne.symm (hneDest env.length)) hrestK,
          hvK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, bytes, hexecB, hh, herr⟩ := helSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VB),
        stB, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB)

/-- Packed fall-through + assign-to-dest simulation (one induction). -/
theorem core_sim_packed {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core) :
    (t = .unit → CoreFallSimHyp (tag := tag) c Γ κ ctx core) ∧
      (retTyWordLike t → CoreToVarSimHyp (tag := tag) c Γ κ ctx core) := by
  revert hM1
  induction core with
  | ret r =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      cases r with
      | unit =>
        simp only [emitCore, emitRet, emitReturnUnit_false, Emit.stmts_nil] at hem
        cases hem
        rw [Core.denote, Tx.run_pure]
        exact ⟨V, st, Step.seqNil, hinv.rel, hinv.ctxr, restore_self V⟩
      | word _ | addr _ | flag _ | pair _ _ => cases ht
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      cases r with
      | word a =>
        simp only [emitCoreToVar, emitAssignRet] at hem; cases hem
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hwfA : atomWF a = true := by
          simp [coreWF, retWF, Bool.and_eq_true] at hwf; exact hwf.1
        have he := eval_atom_ok tag funs (st := st) hinv.venv a
        rw [Core.denote, Tx.run_pure]
        refine ⟨VEnv.set V dest (BitVec.ofNat 256 (a.eval env)), st, ?_, ?_,
          hinv.rel, hinv.ctxr, restore_set V dest _, atom_eval_lt hinv.wf hwfA⟩
        · simp [emitAssign, Emit.stmts_push, Emit.stmts_nil]
          exact Step.seqCons (Step.assignVal he rfl) Step.seqNil
        · simpa [retAsNat, RetExpr.eval, VEnv.setMany_one] using VEnv.get_set_of_some hget
      | addr a =>
        simp only [emitCoreToVar, emitAssignRet] at hem; cases hem
        have he := eval_atom_ok tag funs (st := st) hinv.venv a
        have hwfA : atomWF a = true := by
          simp [coreWF, retWF, Bool.and_eq_true] at hwf; exact hwf.1
        rw [Core.denote, Tx.run_pure]
        refine ⟨VEnv.set V dest (BitVec.ofNat 256 (a.eval env)), st, ?_, ?_,
          hinv.rel, hinv.ctxr, restore_set V dest _, atom_eval_lt hinv.wf hwfA⟩
        · simp [emitAssign, Emit.stmts_push, Emit.stmts_nil]
          exact Step.seqCons (Step.assignVal he rfl) Step.seqNil
        · simpa [retAsNat, RetExpr.eval, VEnv.setMany_one] using VEnv.get_set_of_some hget
      | flag a =>
        simp only [emitCoreToVar, emitAssignRet] at hem; cases hem
        have he := eval_atom_ok tag funs (st := st) hinv.venv a
        have hwfA : atomWF a = true := by
          simp [coreWF, retWF, Bool.and_eq_true] at hwf; exact hwf.1
        rw [Core.denote, Tx.run_pure]
        refine ⟨VEnv.set V dest (BitVec.ofNat 256 (a.eval env)), st, ?_, ?_,
          hinv.rel, hinv.ctxr, restore_set V dest _, atom_eval_lt hinv.wf hwfA⟩
        · simp [emitAssign, Emit.stmts_push, Emit.stmts_nil]
          exact Step.seqCons (Step.assignVal he rfl) Step.seqNil
        · simpa [retAsNat, RetExpr.eval, VEnv.setMany_one] using VEnv.get_set_of_some hget
      | unit | pair _ _ => exact ht.elim
  | opTail op =>
    intro hM1
    constructor
    · intro ht; cases ht
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      simp only [emitCoreToVar] at hem
      cases hE : emitLetOp tag c {} env.length op with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hop : M1Op op := by simpa [M1Frag] using hM1
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop
          (by simpa [coreWF] using hwf) hn1
        simp only [Core.denote] at hsim ⊢
        cases hrun : Tx.run (Op.denote Γ env op) ctx w with
        | ok p =>
          rw [hrun] at hsim
          simp [hE] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          rcases p with ⟨v, w'⟩
          have hget1 : VEnv.get
              ((identV tag env.length, BitVec.ofNat 256 v) :: V) dest ≠ none := by
            rw [VEnv.get_cons, if_neg (Ne.symm (hneDest env.length))]
            simp [hget]
          have heV :
              EvalExpr evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (var (identV tag env.length))
                (.vals [BitVec.ofNat 256 v] st1) :=
            Step.var (by rw [VEnv.get_cons, if_pos rfl])
          have hassign :
              ExecStmt evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (.assign [dest] (var (identV tag env.length)))
                (VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
                  dest (BitVec.ofNat 256 v)) st1 .normal :=
            Step.assignVal heV rfl
          simp only [except_ok_prod]
          refine ⟨VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
              dest (BitVec.ofNat 256 v), st1, ?_, ?_, hinv1.rel, hinv1.ctxr,
              restore_cons_set (Ne.symm (hneDest env.length)),
              by simpa [retAsNat] using hinv1.wf v List.mem_cons_self⟩
          · simp only [emitAssign]
            rw [Emit.stmts_push]
            exact execStmts_append hexec (Step.seqCons hassign Step.seqNil)
          · simpa [retAsNat, VEnv.setMany_one] using
              VEnv.get_set _ dest _ hget1
        | error err =>
          rw [hrun] at hsim
          simp [hE] at hsim
          obtain ⟨V', st', hexec, bytes, hh, herr⟩ := hsim
          simp only [except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          simp only [emitAssign]
          rw [Emit.stmts_push]
          exact execStmts_append_halt hexec
  | opTailAddr op =>
    intro hM1
    constructor
    · intro ht; cases ht
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      simp only [emitCoreToVar] at hem
      cases hE : emitLetOp tag c {} env.length op with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hop : M1Op op := by simpa [M1Frag] using hM1
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop
          (by simpa [coreWF] using hwf) hn1
        simp only [Core.denote] at hsim
        cases hrun : Tx.run (Core.denote Γ (.opTailAddr op) env) ctx w with
        | ok p =>
          have hrun' : Tx.run (Op.denote Γ env op) ctx w = .ok p := hrun
          rw [hrun'] at hsim
          simp [hE] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          rcases p with ⟨v, w'⟩
          have hget1 : VEnv.get
              ((identV tag env.length, BitVec.ofNat 256 v) :: V) dest ≠ none := by
            rw [VEnv.get_cons, if_neg (Ne.symm (hneDest env.length))]
            simp [hget]
          have heV :
              EvalExpr evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (var (identV tag env.length))
                (.vals [BitVec.ofNat 256 v] st1) :=
            Step.var (by rw [VEnv.get_cons, if_pos rfl])
          have hassign :
              ExecStmt evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (.assign [dest] (var (identV tag env.length)))
                (VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
                  dest (BitVec.ofNat 256 v)) st1 .normal :=
            Step.assignVal heV rfl
          simp only [except_ok_prod]
          refine ⟨VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
              dest (BitVec.ofNat 256 v), st1, ?_, ?_, hinv1.rel, hinv1.ctxr,
              restore_cons_set (Ne.symm (hneDest env.length)),
              by simpa [retAsNat] using hinv1.wf v List.mem_cons_self⟩
          · simp only [emitAssign]
            rw [Emit.stmts_push]
            exact execStmts_append hexec (Step.seqCons hassign Step.seqNil)
          · simpa [retAsNat, VEnv.setMany_one] using
              VEnv.get_set _ dest _ hget1
        | error err =>
          have hrun' : Tx.run (Op.denote Γ env op) ctx w = .error err := hrun
          rw [hrun'] at hsim
          simp [hE] at hsim
          obtain ⟨V', st', hexec, bytes, hh, herr⟩ := hsim
          simp only [except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          simp only [emitAssign]
          rw [Emit.stmts_push]
          exact execStmts_append_halt hexec
  | opTailFlag op =>
    intro hM1
    constructor
    · intro ht; cases ht
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      simp only [emitCoreToVar] at hem
      cases hE : emitLetOp tag c {} env.length op with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hop : M1Op op := by simpa [M1Frag] using hM1
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop
          (by simpa [coreWF] using hwf) hn1
        simp only [Core.denote] at hsim
        cases hrun : Tx.run (Core.denote Γ (.opTailFlag op) env) ctx w with
        | ok p =>
          have hrun' : Tx.run (Op.denote Γ env op) ctx w = .ok p := hrun
          rw [hrun'] at hsim
          simp [hE] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          rcases p with ⟨v, w'⟩
          have hget1 : VEnv.get
              ((identV tag env.length, BitVec.ofNat 256 v) :: V) dest ≠ none := by
            rw [VEnv.get_cons, if_neg (Ne.symm (hneDest env.length))]
            simp [hget]
          have heV :
              EvalExpr evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (var (identV tag env.length))
                (.vals [BitVec.ofNat 256 v] st1) :=
            Step.var (by rw [VEnv.get_cons, if_pos rfl])
          have hassign :
              ExecStmt evm funs
                ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
                (.assign [dest] (var (identV tag env.length)))
                (VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
                  dest (BitVec.ofNat 256 v)) st1 .normal :=
            Step.assignVal heV rfl
          simp only [except_ok_prod]
          refine ⟨VEnv.set ((identV tag env.length, BitVec.ofNat 256 v) :: V)
              dest (BitVec.ofNat 256 v), st1, ?_, ?_, hinv1.rel, hinv1.ctxr,
              restore_cons_set (Ne.symm (hneDest env.length)),
              by simpa [retAsNat] using hinv1.wf v List.mem_cons_self⟩
          · simp only [emitAssign]
            rw [Emit.stmts_push]
            exact execStmts_append hexec (Step.seqCons hassign Step.seqNil)
          · simpa [retAsNat, VEnv.setMany_one] using
              VEnv.get_set _ dest _ hget1
        | error err =>
          have hrun' : Tx.run (Op.denote Γ env op) ctx w = .error err := hrun
          rw [hrun'] at hsim
          simp [hE] at hsim
          obtain ⟨V', st', hexec, bytes, hh, herr⟩ := hsim
          simp only [except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          simp only [emitAssign]
          rw [Emit.stmts_push]
          exact execStmts_append_halt hexec
  | stmtTail s =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      simp only [emitCore, emitReturnUnit_false] at hem
      cases hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hsim := stmt_sim tag funs hinv hΓ hκ hlen (show M1Stmt s by simpa [M1Frag] using hM1)
        (show stmtWF c s = true by simpa [coreWF] using hwf) hn0
      cases hrun : Tx.run (Core.denote Γ (.stmtTail s) env) ctx w with
      | ok p =>
        simp only [RetTy.denote, Core.denote] at hrun
        rw [hrun] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        simp only [except_ok_prod]
        exact ⟨V, st1, hexec, hinv1.rel, hinv1.ctxr, restore_self V⟩
      | error err =>
        simp only [RetTy.denote, Core.denote] at hrun
        rw [hrun] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        exact ⟨V', st', bytes, hexec, hh, herr⟩
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      cases ht
  | letOp op k ih =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
      have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
      simp only [Core.denote, Tx.run_bind]
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length op with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
          simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
        cases hopr : Tx.run (Op.denote Γ env op) ctx w with
        | ok p =>
          have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
          rw [hopr] at hsim
          simp only [hE] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          have ih' := (ih hk).1 ht funs hkWF (by simpa using hnK) hinv1 h0
          cases hK : Tx.run (Core.denote Γ k (p.1 :: env)) ctx p.2 with
          | ok q =>
            rw [hK] at ih'
            obtain ⟨V', st', hexeck, hR, hctx, hrest⟩ := ih'
            rcases p with ⟨v, w'⟩
            rcases q with ⟨r, w''⟩
            simp only [except_ok_prod, hK]
            refine ⟨V', st', ?_, hR, hctx, restore_of_restore_cons hrest⟩
            rw [hst]
            exact execStmts_append hexec hexeck
          | error err =>
            rw [hK] at ih'
            obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
            rcases p with ⟨v, w'⟩
            simp only [except_ok_prod, hK, except_error_prod]
            refine ⟨V', st', bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append hexec hexeck
        | error err =>
          have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
          rw [hopr] at hsim
          simp only [hE] at hsim
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
          simp only [except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append_halt hexec
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
      have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
      simp only [Core.denote, Tx.run_bind]
      simp only [emitCoreToVar] at hem
      cases hE : emitLetOp tag c {} env.length op with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        obtain ⟨e0, h0, hst⟩ := emitCoreToVar_prefix tag hem
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
          simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        cases hrun : Tx.run (Op.denote Γ env op) ctx w with
        | ok p =>
          rw [hrun] at hsim
          simp [hE] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          rcases p with ⟨v, w1⟩
          have hne : identV tag env.length ≠ dest := (Ne.symm (hneDest env.length))
          have hget1 : VEnv.get
              ((identV tag env.length, BitVec.ofNat 256 v) :: V) dest = some old := by
            rw [VEnv.get_cons, if_neg hne, hget]
          have ih' := (ih hk).2 ht dest hneDest (env := v :: env) hget1 funs hkWF hnK hinv1 h0
          cases hK : Tx.run (Core.denote Γ k (v :: env)) ctx w1 with
          | ok q =>
            rw [hK] at ih'
            obtain ⟨VK, stK, hexeck, hgetK, hRK, hctxK, hrestK, hvK⟩ := ih'
            rcases q with ⟨_, wK⟩
            simp only [except_ok_prod, hK]
            refine ⟨VK, stK, ?_, hgetK, hRK, hctxK,
              restore_tail_of_restore_cons_set (Ne.symm (hneDest env.length)) hrestK, hvK⟩
            rw [hst]
            exact execStmts_append hexec hexeck
          | error err =>
            rw [hK] at ih'
            obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ih'
            simp only [except_ok_prod, hK, except_error_prod]
            refine ⟨VK, stK, bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append hexec hexeck
        | error err =>
          rw [hrun] at hsim
          simp [hE] at hsim
          obtain ⟨V', st', hexec, bytes, hh, herr⟩ := hsim
          simp only [except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append_halt hexec
  | seq s k ih =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      have ⟨hs, hk⟩ := m1frag_seq.mp hM1
      have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
      simp only [Core.denote, Tx.run_bind]
      simp only [emitCore] at hem
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
        simpa [coreExtraDepth] using hn
      cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
      | ok p =>
        have hsim := stmt_sim tag funs hinv hΓ hκ hlen hs hsWF hn0
        rw [hrun] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        have ih' := (ih hk).1 ht funs hkWF hnK hinv1 h0
        cases hK : Tx.run (Core.denote Γ k env) ctx p.2 with
        | ok q =>
          rw [hK] at ih'
          obtain ⟨V', st', hexeck, hR, hctx, hrest⟩ := ih'
          rcases p with ⟨u, w'⟩
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod, hK]
          refine ⟨V', st', ?_, hR, hctx, hrest⟩
          rw [hst]
          exact execStmts_append hexec hexeck
        | error err =>
          rw [hK] at ih'
          obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
          rcases p with ⟨u, w'⟩
          simp only [except_ok_prod, hK, except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append hexec hexeck
      | error err =>
        have hsim := stmt_sim tag funs hinv hΓ hκ hlen hs hsWF hn0
        rw [hrun] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append_halt hexec
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      have ⟨hs, hk⟩ := m1frag_seq.mp hM1
      have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
      simp only [Core.denote, Tx.run_bind]
      simp only [emitCoreToVar] at hem
      obtain ⟨e0, h0, hst⟩ := emitCoreToVar_prefix tag hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (Nat.le_add_right _ _) hn
      have hnK : identsNodup tag (env.length + coreExtraDepth k) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hsim := stmt_sim tag funs hinv hΓ hκ hlen hs hsWF hn0
      cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
      | ok p =>
        rw [hrun] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨_, w1⟩
        have ih' := (ih hk).2 ht dest hneDest hget funs hkWF hnK hinv1 h0
        cases hK : Tx.run (Core.denote Γ k env) ctx w1 with
        | ok q =>
          rw [hK] at ih'
          obtain ⟨VK, stK, hexeck, hgetK, hRK, hctxK, hrestK, hvK⟩ := ih'
          rcases q with ⟨_, wK⟩
          simp only [except_ok_prod, hK]
          refine ⟨VK, stK, ?_, hgetK, hRK, hctxK, hrestK, hvK⟩
          rw [hst]
          exact execStmts_append hexec hexeck
        | error err =>
          rw [hK] at ih'
          obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ih'
          simp only [except_ok_prod, hK, except_error_prod]
          refine ⟨VK, stK, bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append hexec hexeck
      | error err =>
        rw [hrun] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append_halt hexec
  | letPure p args k ih =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      have ⟨hp, hargs, hk⟩ := m1frag_letPure.mp hM1
      subst hp
      have ⟨a, hargs'⟩ := length_eq_one.mp hargs
      subst hargs'
      have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
        simpa [coreWF, Bool.and_eq_true] using hwf
      simp only [Core.denote]
      have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
      rw [hpe]
      simp only [emitCore, emitPrim] at hem
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      have he := eval_atom_ok tag funs (st := st) hinv.venv a
      have hv := atom_eval_lt hinv.wf hwfA
      have hlet :
          ExecStmt evm funs V st
            (.letDecl [identV tag env.length] (some (atomE tag env.length a)))
            ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
        Step.letVal he rfl
      have hinv1 : Inv tag Γ c κ ctx w (a.eval env :: env)
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
        ⟨localsOK_cons (tag := tag) _ hn1 hinv.venv, envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
      have ih' := (ih hk).1 ht funs hkWF (by simpa using hnK) hinv1 h0
      cases hK : Tx.run (Core.denote Γ k (a.eval env :: env)) ctx w with
      | ok q =>
        rw [hK] at ih'
        obtain ⟨V', st', hexeck, hR, hctx, hrest⟩ := ih'
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod]
        refine ⟨V', st', ?_, hR, hctx, restore_of_restore_cons hrest⟩
        rw [hst]
        simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
        exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
      | error err =>
        rw [hK] at ih'
        obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
        exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      have ⟨hp, hargs, hk⟩ := m1frag_letPure.mp hM1
      subst hp
      have ⟨a, hargs'⟩ := length_eq_one.mp hargs
      subst hargs'
      have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
        simpa [coreWF, Bool.and_eq_true] using hwf
      simp only [Core.denote]
      have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
      rw [hpe]
      simp only [emitCoreToVar, emitPrim] at hem
      obtain ⟨e0, h0, hst⟩ := emitCoreToVar_prefix tag hem
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      have he := eval_atom_ok tag funs (st := st) hinv.venv a
      have hv := atom_eval_lt hinv.wf hwfA
      have hlet :
          ExecStmt evm funs V st
            (.letDecl [identV tag env.length] (some (atomE tag env.length a)))
            ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
        Step.letVal he rfl
      have hne : identV tag env.length ≠ dest := (Ne.symm (hneDest env.length))
      have hget1 : VEnv.get
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) dest = some old := by
        rw [VEnv.get_cons, if_neg hne, hget]
      have hinv1 : Inv tag Γ c κ ctx w (a.eval env :: env)
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
        ⟨localsOK_cons (tag := tag) _ hn1 hinv.venv, envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
      have ih' := (ih hk).2 ht dest hneDest (env := a.eval env :: env) hget1 funs hkWF hnK hinv1 h0
      cases hK : Tx.run (Core.denote Γ k (a.eval env :: env)) ctx w with
      | ok q =>
        rw [hK] at ih'
        obtain ⟨VK, stK, hexeck, hgetK, hRK, hctxK, hrestK, hvK⟩ := ih'
        rcases q with ⟨_, wK⟩
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hgetK, hRK, hctxK,
          restore_tail_of_restore_cons_set (Ne.symm (hneDest env.length)) hrestK, hvK⟩
        rw [hst]
        simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
        exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
      | error err =>
        rw [hK] at ih'
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ih'
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        rw [hst]
        simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
        exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
  | ite cond a b iha ihb =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      have ⟨hC, ha, hb⟩ := m1frag_ite.mp hM1
      have hwf' := hwf
      simp [coreWF, Bool.and_eq_true] at hwf'
      obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
      simp only [Core.denote]
      simp only [emitCore] at hem
      obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        a ({} : Emit) env.length
      obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        b ({} : Emit) env.length
      simp [hA, hB] at hem
      cases hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (Nat.le_add_right _ _) hn
      have hnA : identsNodup tag (env.length + coreExtraDepth a) = true :=
        identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_left _ _) _) hn
      have hnB : identsNodup tag (env.length + coreExtraDepth b) = true :=
        identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_right _ _) _) hn
      have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
      have hpush :
          (Emit.push ({} : Emit) (.switch (emitCond tag env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
            [.switch (emitCond tag env.length cond)
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
        simp [Emit.stmts_push, Emit.stmts_nil]
      rw [hpush]
      split_ifs with hc
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
          selectSwitch_nonzero (by simp [hc, b2w])
        have ihA := (iha ha).1 ht ([] :: funs) haWF hnA hinv hA
        cases hrun : Tx.run (Core.denote Γ a env) ctx w with
        | ok q =>
          rw [hrun] at ihA
          obtain ⟨V', st', hexec, hR, hctx, hrest⟩ := ihA
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod]
          refine ⟨V, st', ?_, hR, hctx, restore_self V⟩
          have hsw := exec_switch hcond hsel (hoist_emitCore tag hA) hexec
          rwa [hrest] at hsw
        | error err =>
          rw [hrun] at ihA
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          exact exec_switch hcond hsel (hoist_emitCore tag hA) hexec
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
          simp [hc, b2w]
          exact selectSwitch_zero
        have ihB := (ihb hb).1 ht ([] :: funs) hbWF hnB hinv hB
        cases hrun : Tx.run (Core.denote Γ b env) ctx w with
        | ok q =>
          rw [hrun] at ihB
          obtain ⟨V', st', hexec, hR, hctx, hrest⟩ := ihB
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod]
          refine ⟨V, st', ?_, hR, hctx, restore_self V⟩
          have hsw := exec_switch hcond hsel (hoist_emitCore tag hB) hexec
          rwa [hrest] at hsw
        | error err =>
          rw [hrun] at ihB
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          exact exec_switch hcond hsel (hoist_emitCore tag hB) hexec
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      have ⟨hC, ha, hb⟩ := m1frag_ite.mp hM1
      have hwf' := hwf
      simp [coreWF, Bool.and_eq_true] at hwf'
      obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
      simp only [Core.denote]
      simp only [emitCoreToVar] at hem
      obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) a ({} : Emit) env.length dest
      obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) b ({} : Emit) env.length dest
      simp [hA, hB] at hem
      cases hem
      have hnA : identsNodup tag (env.length + coreExtraDepth a) = true :=
        identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_left _ _) _) hn
      have hnB : identsNodup tag (env.length + coreExtraDepth b) = true :=
        identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_right _ _) _) hn
      have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
      have hpush :
          (Emit.push ({} : Emit) (.switch (emitCond tag env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
            [.switch (emitCond tag env.length cond)
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
        simp [Emit.stmts_push, Emit.stmts_nil]
      rw [hpush]
      split_ifs with hc
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
          selectSwitch_nonzero (by simp [hc, b2w])
        have ihA := (iha ha).2 ht dest hneDest hget ([] :: funs) haWF hnA hinv hA
        cases hrun : Tx.run (Core.denote Γ a env) ctx w with
        | ok q =>
          rw [hrun] at ihA
          obtain ⟨V', st', hexec, hget', hR, hctx', hrest', hv'⟩ := ihA
          rcases q with ⟨_, w''⟩
          simp only [except_ok_prod]
          refine ⟨restore V V', st', ?_, ?_, hR, hctx', ?_, hv'⟩
          · exact exec_switch hcond hsel (hoist_emitCoreToVar tag hA) hexec
          · rw [hrest']; exact VEnv.get_set_of_some hget
          · rw [hrest']; exact restore_set V dest _
        | error err =>
          rw [hrun] at ihA
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          exact exec_switch hcond hsel (hoist_emitCoreToVar tag hA) hexec
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
          simp [hc, b2w]
          exact selectSwitch_zero
        have ihB := (ihb hb).2 ht dest hneDest hget ([] :: funs) hbWF hnB hinv hB
        cases hrun : Tx.run (Core.denote Γ b env) ctx w with
        | ok q =>
          rw [hrun] at ihB
          obtain ⟨V', st', hexec, hget', hR, hctx', hrest', hv'⟩ := ihB
          rcases q with ⟨_, w''⟩
          simp only [except_ok_prod]
          refine ⟨restore V V', st', ?_, ?_, hR, hctx', ?_, hv'⟩
          · exact exec_switch hcond hsel (hoist_emitCoreToVar tag hB) hexec
          · rw [hrest']; exact VEnv.get_set_of_some hget
          · rw [hrest']; exact restore_set V dest _
        | error err =>
          rw [hrun] at ihB
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          exact exec_switch hcond hsel (hoist_emitCoreToVar tag hB) hexec
  | @seqIf tBr _ cond th el k ihth ihel ihk =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      cases tBr with
      | pair _ _ => simp [M1Frag] at hM1
      | unit =>
        have ⟨hC, hth, hel, hk⟩ := m1frag_seqIf.mp hM1
        have ⟨hcWF, hthWF, helWF, hkWF, _⟩ := coreWF_seqIf.mp hwf
        simp only [Core.denote, Tx.run_bind]
        simp only [emitCore] at hem
        obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
          th ({} : Emit) env.length
        obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
          el ({} : Emit) env.length
        simp [hA, hB] at hem
        obtain ⟨eK, hKpre, hst⟩ := emitCore_prefix tag hem
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (Nat.le_add_right _ _) hn
        have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnK : identsNodup tag (env.length + coreExtraDepth k) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
        split_ifs with hc
        · have hsel :
              selectSwitch evm (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
            selectSwitch_nonzero (by simp [hc, b2w])
          have ihA := (ihth hth).1 rfl ([] :: funs) hthWF hnA hinv hA
          cases hrun : Tx.run (Core.denote Γ th env) ctx w with
          | ok q =>
            rw [hrun] at ihA
            obtain ⟨VA, stA, hexecA, hRA, hctxA, hrestA⟩ := ihA
            rcases q with ⟨_, wA⟩
            have hinvK : Inv tag Γ c κ ctx wA env V stA :=
              ⟨hinv.venv, hinv.wf, hRA, hctxA⟩
            have ihK := (ihk hk).1 ht funs hkWF hnK hinvK hKpre
            cases hKrun : Tx.run (Core.denote Γ k env) ctx wA with
            | ok qk =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, hexeck, hRK, hctxK, hrestK⟩ := ihK
              rcases qk with ⟨_, wK⟩
              simp only [except_ok_prod, hKrun]
              refine ⟨VK, stK, ?_, hRK, hctxK, hrestK⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hA) hexecA
              rw [hrestA] at hsw
              exact execStmts_append hsw hexeck
            | error err =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
              simp only [except_ok_prod, hKrun, except_error_prod]
              refine ⟨VK, stK, bytes, ?_, hh, herr⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hA) hexecA
              rw [hrestA] at hsw
              exact execStmts_append hsw hexeck
          | error err =>
            rw [hrun] at ihA
            obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
            simp only [except_error_prod]
            refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append_halt
              (exec_switch hcond hsel (hoist_emitCore tag hA) hexec)
        · have hsel :
              selectSwitch evm (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
            simp [hc, b2w]
            exact selectSwitch_zero
          have ihB := (ihel hel).1 rfl ([] :: funs) helWF hnB hinv hB
          cases hrun : Tx.run (Core.denote Γ el env) ctx w with
          | ok q =>
            rw [hrun] at ihB
            obtain ⟨VB, stB, hexecB, hRB, hctxB, hrestB⟩ := ihB
            rcases q with ⟨_, wB⟩
            have hinvK : Inv tag Γ c κ ctx wB env V stB :=
              ⟨hinv.venv, hinv.wf, hRB, hctxB⟩
            have ihK := (ihk hk).1 ht funs hkWF hnK hinvK hKpre
            cases hKrun : Tx.run (Core.denote Γ k env) ctx wB with
            | ok qk =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, hexeck, hRK, hctxK, hrestK⟩ := ihK
              rcases qk with ⟨_, wK⟩
              simp only [except_ok_prod, hKrun]
              refine ⟨VK, stK, ?_, hRK, hctxK, hrestK⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hB) hexecB
              rw [hrestB] at hsw
              exact execStmts_append hsw hexeck
            | error err =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
              simp only [except_ok_prod, hKrun, except_error_prod]
              refine ⟨VK, stK, bytes, ?_, hh, herr⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hB) hexecB
              rw [hrestB] at hsw
              exact execStmts_append hsw hexeck
          | error err =>
            rw [hrun] at ihB
            obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
            simp only [except_error_prod]
            refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append_halt
              (exec_switch hcond hsel (hoist_emitCore tag hB) hexec)
      | word | addr | flag =>
        have htWL : retTyWordLike (coreRetTy th) := trivial
        have ⟨_, hth, hel, _⟩ := m1frag_seqIf.mp hM1
        exact seqIf_wordLike_fall (tag := tag) htWL ht hM1
          ((ihth hth).2 htWL)
          ((ihel hel).2 htWL)
          (fun hMk htU => (ihk hMk).1 htU) funs hwf hn hinv hem
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      cases tBr with
      | pair _ _ => simp [M1Frag] at hM1
      | unit =>
        have ⟨hC, hth, hel, hk⟩ := m1frag_seqIf.mp hM1
        have ⟨hcWF, hthWF, helWF, hkWF, _⟩ := coreWF_seqIf.mp hwf
        simp only [Core.denote, Tx.run_bind]
        simp only [emitCoreToVar] at hem
        obtain ⟨eA, hA⟩ := emitCoreToVar_some tag (c := c) th ({} : Emit) env.length dest
        obtain ⟨eB, hB⟩ := emitCoreToVar_some tag (c := c) el ({} : Emit) env.length dest
        simp [hA, hB] at hem
        obtain ⟨eK, hKpre, hst⟩ := emitCoreToVar_prefix tag hem
        have hA' : emitCore tag c {} env.length false th false = some eA := by
          simpa [emitCoreToVar_eq_emitCore_unit tag th {} env.length dest] using hA
        have hB' : emitCore tag c {} env.length false el false = some eB := by
          simpa [emitCoreToVar_eq_emitCore_unit tag el {} env.length dest] using hB
        have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnK : identsNodup tag (env.length + coreExtraDepth k) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
        split_ifs with hc
        · have hsel :
              selectSwitch evm (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
            selectSwitch_nonzero (by simp [hc, b2w])
          have ihA := (ihth hth).1 rfl
            ([] :: funs) hthWF hnA hinv hA'
          cases hrun : Tx.run (Core.denote Γ th env) ctx w with
          | ok q =>
            rw [hrun] at ihA
            obtain ⟨VA, stA, hexecA, hRA, hctxA, hrestA⟩ := ihA
            rcases q with ⟨_, wA⟩
            have hinvK : Inv tag Γ c κ ctx wA env V stA :=
              ⟨hinv.venv, hinv.wf, hRA, hctxA⟩
            have ihK := (ihk hk).2 ht dest hneDest hget funs hkWF hnK hinvK hKpre
            cases hKrun : Tx.run (Core.denote Γ k env) ctx wA with
            | ok qk =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, hexeck, hgetK, hRK, hctxK, hrestK, hvK⟩ := ihK
              rcases qk with ⟨_, wK⟩
              simp only [except_ok_prod, hKrun]
              refine ⟨VK, stK, ?_, hgetK, hRK, hctxK, hrestK, hvK⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hA') hexecA
              rw [hrestA] at hsw
              exact execStmts_append hsw hexeck
            | error err =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
              simp only [except_ok_prod, hKrun, except_error_prod]
              refine ⟨VK, stK, bytes, ?_, hh, herr⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hA') hexecA
              rw [hrestA] at hsw
              exact execStmts_append hsw hexeck
          | error err =>
            rw [hrun] at ihA
            obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
            simp only [except_error_prod]
            refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append_halt
              (exec_switch hcond hsel (hoist_emitCore tag hA') hexec)
        · have hsel :
              selectSwitch evm (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
            simp [hc, b2w]
            exact selectSwitch_zero
          have ihB := (ihel hel).1 rfl
            ([] :: funs) helWF hnB hinv hB'
          cases hrun : Tx.run (Core.denote Γ el env) ctx w with
          | ok q =>
            rw [hrun] at ihB
            obtain ⟨VB, stB, hexecB, hRB, hctxB, hrestB⟩ := ihB
            rcases q with ⟨_, wB⟩
            have hinvK : Inv tag Γ c κ ctx wB env V stB :=
              ⟨hinv.venv, hinv.wf, hRB, hctxB⟩
            have ihK := (ihk hk).2 ht dest hneDest hget funs hkWF hnK hinvK hKpre
            cases hKrun : Tx.run (Core.denote Γ k env) ctx wB with
            | ok qk =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, hexeck, hgetK, hRK, hctxK, hrestK, hvK⟩ := ihK
              rcases qk with ⟨_, wK⟩
              simp only [except_ok_prod, hKrun]
              refine ⟨VK, stK, ?_, hgetK, hRK, hctxK, hrestK, hvK⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hB') hexecB
              rw [hrestB] at hsw
              exact execStmts_append hsw hexeck
            | error err =>
              rw [hKrun] at ihK
              obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
              simp only [except_ok_prod, hKrun, except_error_prod]
              refine ⟨VK, stK, bytes, ?_, hh, herr⟩
              rw [hst]
              have hsw := exec_switch hcond hsel (hoist_emitCore tag hB') hexecB
              rw [hrestB] at hsw
              exact execStmts_append hsw hexeck
          | error err =>
            rw [hrun] at ihB
            obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
            simp only [except_error_prod]
            refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
            rw [hst]
            exact execStmts_append_halt
              (exec_switch hcond hsel (hoist_emitCore tag hB') hexec)
      | word | addr | flag =>
        have htWL : retTyWordLike (coreRetTy th) := trivial
        have ⟨_, hth, hel, _⟩ := m1frag_seqIf.mp hM1
        exact seqIf_wordLike_toVar (tag := tag) htWL ht hM1
          ((ihth hth).2 htWL)
          ((ihel hel).2 htWL)
          dest hneDest (fun hMk htK => (ihk hMk).2 htK dest hneDest) hget funs hwf hn hinv hem
  | revertTail err args =>
    intro hM1
    constructor
    · intro ht w env V st funs hwf hn hinv e' hem
      have hnil : args.length = 0 := by simpa [M1Frag] using hM1
      match args with
      | _ :: _ => cases hnil
      | [] =>
        simp only [emitCore] at hem
        cases hem
        simp only [Core.denote, Tx.run_revert]
        exact revertTail_sim tag funs hinv hwf
    · intro ht dest hneDest w env V st old hget funs hwf hn hinv e' hem
      have hnil : args.length = 0 := by simpa [M1Frag] using hM1
      match args with
      | _ :: _ => cases hnil
      | [] =>
        simp only [emitCoreToVar] at hem; cases hem
        simp only [Core.denote, Tx.run_revert]
        exact revertTail_sim tag funs hinv hwf
  | letCall _ _ _ | callTail _ _ =>
    intro hM1
    exact False.elim (by simpa [M1Frag] using hM1)

theorem core_sim_fall {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core) (ht : t = .unit) :
    CoreFallSimHyp (tag := tag) c Γ κ ctx core :=
  (core_sim_packed (tag := tag) hΓ hκ hlen core hM1).1 ht

/-- Assign `dest` and fall through. Word-like cores only (`ht`). -/
theorem core_toVar_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core)
    (ht : retTyWordLike t) (dest : YIdent)
    (hneDest : ∀ n, dest ≠ identV tag n) :
    ∀ {w : World S X E} {env V st} {old : U256}
      (hget : VEnv.get V dest = some old) (funs : FunEnv evm)
      (hwf : coreWF c core = true)
      (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
      (hinv : Inv tag Γ c κ ctx w env V st)
      {e' : Emit} (hem : emitCoreToVar tag c {} env.length dest core = some e'),
      match Tx.run (Core.denote Γ core env) ctx w with
      | .ok (v, w') =>
          ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
            VEnv.get V' dest = some (BitVec.ofNat 256 (retAsNat v)) ∧
            R c Γ κ w' st' ∧ ctxRel ctx st' ∧
            restore V V' = VEnv.set V dest (BitVec.ofNat 256 (retAsNat v)) ∧
            retAsNat v < wordBound
      | .error e =>
          ∃ V' st' bytes,
            ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes :=
  (core_sim_packed (tag := tag) hΓ hκ hlen core hM1).2 ht dest hneDest



/-- Word-like `seqIf` halt simulation, using closed `core_toVar_sim`. -/
theorem seqIf_wordLike_sim {S X E ε} {c : ContractDef}
    {Γ : ContractSchema S X E ε} {κ ctx haltUnit}
    (hhalt : haltUnit = true)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t u : RetTy} (htBr : retTyWordLike t)
    {cond : Cond} {th el : Core t} {k : Core u}
    (hM1 : M1Frag (.seqIf cond th el k))
    (ihk : M1Frag k → CoreHaltSimHyp (tag := tag) c Γ κ ctx haltUnit k)
    {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    (funs : FunEnv evm)
    (hwf : coreWF c (.seqIf cond th el k) = true)
    (hn : identsNodup tag (env.length + coreExtraDepth (.seqIf cond th el k)) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {clearLock : Bool} {e' : Emit}
    (hem : emitCore tag c {} env.length haltUnit (.seqIf cond th el k) clearLock = some e') :
    match Tx.run (Core.denote Γ (.seqIf cond th el k) env) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          haltSuccess u v st'.halted ∧ R c Γ κ w' st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st e'.stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  have htEq := retTyWordLike_cases htBr
  have ⟨hC, hth, hel, hk⟩ := (m1frag_seqIf_wordLike htBr).mp hM1
  have ⟨hcWF, hthWF, helWF, hkWF⟩ := (coreWF_seqIf_wordLike htBr).mp hwf
  rw [denote_seqIf_wordLike htBr, Tx.run_bind]
  obtain ⟨eA, eB, eK, hA, hB, hKpre, hst⟩ :=
    emitCore_seqIf_wordLike_prefix (tag := tag) htBr hem
  have ⟨hthD, helD, h1D, hkD⟩ := seqIf_wordLike_depth_le htBr cond th el k
  have hn1 : identsNodup tag (env.length + 1) = true :=
    identsNodup_mono tag (Nat.add_le_add_left h1D _) hn
  have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
    identsNodup_mono tag (Nat.add_le_add_left hthD _) hn
  have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
    identsNodup_mono tag (Nat.add_le_add_left helD _) hn
  have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true :=
    identsNodup_mono tag (by
      rw [show (env.length + 1) + coreExtraDepth k =
            env.length + (coreExtraDepth k + 1) by omega]
      exact Nat.add_le_add_left hkD env.length) hn
  have hokΦ : localsOK tag env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) :=
    localsOK_phi_dest (tag := tag) 0 0 hn1 hinv.venv
  have hinvΦ : Inv tag Γ c κ ctx w env
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V) st :=
    ⟨hokΦ, hinv.wf, hinv.rel, hinv.ctxr⟩
  have hgetΦ : VEnv.get
      ((identPhi tag env.length, (0 : U256)) ::
        (identV tag env.length, (0 : U256)) :: V)
      (identPhi tag env.length) = some 0 := by
    rw [VEnv.get_cons, if_pos rfl]
  have hneΦ : ∀ n, identPhi tag env.length ≠ identV tag n :=
    fun n => identPhi_ne_identV tag env.length n
  have hcond1 := eval_cond_ok tag (st := st) ([] :: funs) hokΦ hinv.wf hC hcWF
  rw [hst]
  split_ifs with hc
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eA.stmts :=
      selectSwitch_nonzero (by simp [hc, b2w])
    have hthSim :=
      core_toVar_sim (tag := tag) hΓ hκ hlen th hth htBr
        (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        hthWF hnA hinvΦ hA
    cases hrun : Tx.run (Core.denote Γ th env) ctx w with
    | ok q =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, hexecA, hgetA, hRA, hctxA, hrestA, hvA⟩ := hthSim
      rcases q with ⟨v, wA⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA hrestA
      have hinvK : Inv tag Γ c κ ctx wA (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stA :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvA hinv.wf, hRA, hctxA⟩
      have ihK := ihk hk (env := retAsNat v :: env) funs hkWF hnK hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wA with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hsucc, hRK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hsucc, hRK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at hthSim
      obtain ⟨VA, stA, bytes, hexecA, hh, herr⟩ := hthSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VA),
        stA, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hA) hexecA)
  · have hsel :
        selectSwitch evm (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) =
            eB.stmts := by
      simp [hc, b2w]; exact selectSwitch_zero
    have helSim :=
      core_toVar_sim (tag := tag) hΓ hκ hlen el hel htBr
        (identPhi tag env.length) hneΦ hgetΦ ([] :: [] :: funs)
        helWF hnB hinvΦ hB
    cases hrun : Tx.run (Core.denote Γ el env) ctx w with
    | ok q =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, hexecB, hgetB, hRB, hctxB, hrestB, hvB⟩ := helSim
      rcases q with ⟨v, wB⟩
      have hpre :=
        exec_seqIfWord_ok (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB hrestB
      have hinvK : Inv tag Γ c κ ctx wB (retAsNat v :: env)
          ((identV tag env.length, BitVec.ofNat 256 (retAsNat v)) :: V) stB :=
        ⟨localsOK_cons (tag := tag) (retAsNat v) hn1 hinv.venv,
          envWF_cons hvB hinv.wf, hRB, hctxB⟩
      have ihK := ihk hk (env := retAsNat v :: env) funs hkWF hnK hinvK hKpre
      cases hKrun : Tx.run (Core.denote Γ k (retAsNat v :: env)) ctx wB with
      | ok qk =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, hexeck, hsucc, hRK⟩ := ihK
        rcases qk with ⟨_, wK⟩
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_ok_prod]
        refine ⟨VK, stK, ?_, hsucc, hRK⟩
        exact execStmts_append hpre hexeck
      | error err =>
        rw [hKrun] at ihK
        obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
        simp only [except_ok_prod]
        rw [seqIfCont_retAsNat (Γ := Γ) v k env htEq, hKrun]
        simp only [except_error_prod]
        refine ⟨VK, stK, bytes, ?_, hh, herr⟩
        exact execStmts_append hpre hexeck
    | error err =>
      rw [hrun] at helSim
      obtain ⟨VB, stB, bytes, hexecB, hh, herr⟩ := helSim
      simp only [except_error_prod]
      refine ⟨
        restore ((identV tag env.length, (0 : U256)) :: V)
          (restore
            ((identPhi tag env.length, (0 : U256)) ::
              (identV tag env.length, (0 : U256)) :: V) VB),
        stB, bytes, ?_, hh, herr⟩
      exact execStmts_append_halt
        (exec_seqIfWord_halt (tag := tag) hcond1 hsel
          (hoist_emitCoreToVar tag hB) hexecB)

theorem core_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx haltUnit} (hhalt : haltUnit = true)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv evm)
      (hwf : coreWF c core = true)
      (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
      (hinv : Inv tag Γ c κ ctx w env V st)
      {clearLock : Bool} {e' : Emit}
      (hem : emitCore tag c {} env.length haltUnit core clearLock = some e'),
      match Tx.run (Core.denote Γ core env) ctx w with
      | .ok (v, w') =>
          ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            haltSuccess t v st'.halted ∧ R c Γ κ w' st'
      | .error e =>
          ∃ V' st' bytes,
            ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  revert hM1
  induction core with

  | ret r =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    cases r with
    | unit =>
      simp only [emitCore] at hem
      cases hem
      have hstatic := ctxRel_static hinv.ctxr
      have hs : (emitRet tag {} env.length haltUnit RetExpr.unit clearLock).stmts =
          (if clearLock then [lockClearStmt] else []) ++ [stopStmt] := by
        cases clearLock with
        | false =>
          simp [emitRet, hhalt, emitReturnUnit_true, Emit.stmts_nil]
        | true =>
          simp [emitRet_lock_eq, emitLockClear_stmts, Emit.stmts_nil, emitRet, hhalt,
            emitReturnUnit_true]
      rw [Core.denote, Tx.run_pure]
      refine ⟨V,
        { stAfterLockClear clearLock st with halted := some (.stop, []) }, ?_, rfl, ?_⟩
      · rw [hs]
        exact execStmts_maybe_lockClear clearLock hstatic
          (stop_sim funs V (stAfterLockClear clearLock st))
      · exact R_halted_update (R_memOnly hinv.rel (memOnly_stAfterLockClear clearLock st)) _
    | word a =>
      simp only [emitCore] at hem
      cases hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by
        simp [coreWF, retWF, Bool.and_eq_true] at hwf
        exact hwf.1
      have hv := atom_eval_lt hinv.wf hwfA
      have hstatic := ctxRel_static hinv.ctxr
      have hMO := memOnly_stAfterLockClear clearLock st
      have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st)
            (Inv_memOnly tag hinv hMO).venv a
      obtain ⟨st', hexec, hh, hR'⟩ :=
        return_word_sim funs V hv he (R_memOnly hinv.rel hMO)
      rw [Core.denote, Tx.run_pure]
      refine ⟨V, st', ?_, haltSuccess_word hh, hR'⟩
      rw [emitRet_word_stmts_if tag {} env.length haltUnit a clearLock, Emit.stmts_nil]
      exact execStmts_maybe_lockClear clearLock hstatic hexec
    | addr a =>
      simp only [emitCore] at hem
      cases hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by
        simp [coreWF, retWF, Bool.and_eq_true] at hwf
        exact hwf.1
      have hv := atom_eval_lt hinv.wf hwfA
      have hstatic := ctxRel_static hinv.ctxr
      have hMO := memOnly_stAfterLockClear clearLock st
      have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st)
            (Inv_memOnly tag hinv hMO).venv a
      obtain ⟨st', hexec, hh, hR'⟩ :=
        return_word_sim funs V hv he (R_memOnly hinv.rel hMO)
      rw [Core.denote, Tx.run_pure]
      refine ⟨V, st', ?_, haltSuccess_addr hh, hR'⟩
      rw [emitRet_addr_stmts_if tag {} env.length haltUnit a clearLock, Emit.stmts_nil]
      exact execStmts_maybe_lockClear clearLock hstatic hexec
    | flag a =>
      simp only [emitCore] at hem
      cases hem
      have hn0 : identsNodup tag env.length = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by
        simp [coreWF, retWF, Bool.and_eq_true] at hwf
        exact hwf.1
      have hv := atom_eval_lt hinv.wf hwfA
      have hstatic := ctxRel_static hinv.ctxr
      have hMO := memOnly_stAfterLockClear clearLock st
      have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st)
            (Inv_memOnly tag hinv hMO).venv a
      obtain ⟨st', hexec, hh, hR'⟩ :=
        return_word_sim funs V hv he (R_memOnly hinv.rel hMO)
      rw [Core.denote, Tx.run_pure]
      refine ⟨V, st', ?_, haltSuccess_flag hh, hR'⟩
      rw [emitRet_flag_stmts_if tag {} env.length haltUnit a clearLock, Emit.stmts_nil]
      exact execStmts_maybe_lockClear clearLock hstatic hexec
    | pair x y =>
      cases x with
      | word a =>
        cases y with
        | word b =>
          simp only [emitCore] at hem
          cases hem
          have hn0 : identsNodup tag env.length = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have ⟨hwfA, hwfB⟩ : atomWF a = true ∧ atomWF b = true := by
            simp [coreWF, retWF, Bool.and_eq_true] at hwf
            exact hwf.1
          have hv0 := atom_eval_lt hinv.wf hwfA
          have hv1 := atom_eval_lt hinv.wf hwfB
          have hstatic := ctxRel_static hinv.ctxr
          have hMO := memOnly_stAfterLockClear clearLock st
          have he0 := eval_atom_ok tag funs (st := stAfterLockClear clearLock st)
            (Inv_memOnly tag hinv hMO).venv a
          obtain ⟨st', hexec, hh, hR'⟩ :=
            return_pair_sim funs V hv0 hv1 he0
              (fun st' => eval_atom_ok tag funs (st := st')
                (Inv_memOnly tag hinv hMO).venv b) (R_memOnly hinv.rel hMO)
          rw [Core.denote, Tx.run_pure]
          refine ⟨V, st', ?_, haltSuccess_pair_ww hh, hR'⟩
          rw [emitRet_pair_ww_stmts_if tag {} env.length haltUnit a b clearLock, Emit.stmts_nil]
          exact execStmts_maybe_lockClear clearLock hstatic hexec
        | _ => simp [M1Frag] at hM1
      | _ => simp [M1Frag] at hM1
  | stmtTail s =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    simp only [emitCore] at hem
    rw [hhalt] at hem
    cases hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (by simp [coreExtraDepth]) hn
    have hs :
        (emitReturnUnit
          (if clearLock then emitLockClear (emitStmt tag c {} env.length s)
            else emitStmt tag c {} env.length s) true).stmts =
          (emitStmt tag c {} env.length s).stmts ++
            ((if clearLock then [lockClearStmt] else []) ++ [stopStmt]) :=
      emitReturnUnit_lock_if (emitStmt tag c {} env.length s) clearLock
    have hsim := stmt_sim tag funs hinv hΓ hκ hlen (show M1Stmt s by simpa [M1Frag] using hM1)
      (show stmtWF c s = true by simpa [coreWF] using hwf) hn0
    cases hrun : Tx.run (Core.denote Γ (.stmtTail s) env) ctx w with
    | ok p =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      have hstatic := ctxRel_static hinv1.ctxr
      simp only [except_ok_prod]
      refine ⟨V, { stAfterLockClear clearLock st1 with halted := some (.stop, []) }, ?_,
        rfl, R_halted_update (R_memOnly hinv1.rel (memOnly_stAfterLockClear clearLock st1)) _⟩
      rw [hs]
      exact execStmts_append hexec
        (execStmts_maybe_lockClear clearLock hstatic
          (stop_sim funs V (stAfterLockClear clearLock st1)))
    | error err =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hs]
      exact execStmts_append_halt hexec
  | letOp op k ih =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    cases hE : emitLetOp tag c {} env.length op with
    | none =>
      simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        have ih' := ih hk funs hkWF (by simpa using hnK) hinv1 h0
        cases hK : Tx.run (Core.denote Γ k (p.1 :: env)) ctx p.2 with
        | ok q =>
          rw [hK] at ih'
          obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
          rcases p with ⟨v, w'⟩
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod, hK]
          refine ⟨V', st', ?_, hhaltS, hR⟩
          rw [hst]
          exact execStmts_append hexec hexeck
        | error err =>
          rw [hK] at ih'
          obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
          rcases p with ⟨v, w'⟩
          simp only [except_ok_prod, hK, except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append hexec hexeck
      | error err =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append_halt hexec
  | seq s k ih =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (by simp [coreExtraDepth]) hn
    have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
    | ok p =>
      have hsim := stmt_sim tag funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      have ih' := ih hk funs hkWF hnK hinv1 h0
      cases hK : Tx.run (Core.denote Γ k env) ctx p.2 with
      | ok q =>
        rw [hK] at ih'
        obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
        rcases p with ⟨u, w'⟩
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod, hK]
        refine ⟨V', st', ?_, hhaltS, hR⟩
        rw [hst]
        exact execStmts_append hexec hexeck
      | error err =>
        rw [hK] at ih'
        obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
        rcases p with ⟨u, w'⟩
        simp only [except_ok_prod, hK, except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append hexec hexeck
    | error err =>
      have hsim := stmt_sim tag funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      exact execStmts_append_halt hexec
  | opTail op =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    simp only [Core.denote, RetTy.denote]
    simp only [emitCore] at hem
    cases hE : emitLetOp tag c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet tag e1 (env.length + 1) haltUnit (.word (.var 0)) clearLock).stmts =
            e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
              (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts) :=
        emitRet_word_stmts_if tag _ _ _ _ _
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        simp only [except_ok_prod]
        have hn0 : identsNodup tag (v :: env).length = true := by
          simpa using hn1
        have hstatic := ctxRel_static hinv1.ctxr
        have hMO := memOnly_stAfterLockClear clearLock st1
        have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st1)
          (Inv_memOnly tag hinv1 hMO).venv (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV tag env.length, BitVec.ofNat 256 v) :: V) hv he
            (R_memOnly hinv1.rel hMO)
        refine ⟨(identV tag env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_word hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec (execStmts_maybe_lockClear clearLock hstatic hret)
      | error err =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | letPure p args k ih =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    have ⟨hp, hargs, hk⟩ := m1frag_letPure.mp hM1
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
    have hn1 : identsNodup tag (env.length + 1) = true :=
      identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom_ok tag funs (st := st) hinv.venv a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt evm funs V st
          (.letDecl [identV tag env.length] (some (atomE tag env.length a)))
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal he rfl
    have hinv1 : Inv tag Γ c κ ctx w (a.eval env :: env)
        ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨localsOK_cons (tag := tag) _ hn1 hinv.venv, envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have ih' := ih hk funs hkWF (by simpa using hnK) hinv1 h0
    cases hK : Tx.run (Core.denote Γ k (a.eval env :: env)) ctx w with
    | ok q =>
      rw [hK] at ih'
      obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
      rcases q with ⟨r, w''⟩
      simp only [except_ok_prod]
      refine ⟨V', st', ?_, hhaltS, hR⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
    | error err =>
      rw [hK] at ih'
      obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
  | ite cond a b iha ihb =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    have ⟨hC, ha, hb⟩ := m1frag_ite.mp hM1
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
    simp only [Core.denote]
    simp only [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := haltUnit) (clearLock := clearLock)
      a ({} : Emit) env.length
    obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := haltUnit) (clearLock := clearLock)
      b ({} : Emit) env.length
    simp [hA, hB] at hem
    cases hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (Nat.le_add_right _ _) hn
    have hnA : identsNodup tag (env.length + coreExtraDepth a) = true :=
      identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_left _ _) _) hn
    have hnB : identsNodup tag (env.length + coreExtraDepth b) = true :=
      identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_right _ _) _) hn
    have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond tag env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond tag env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush]
    split_ifs with hc
    · have hsel :
          selectSwitch evm (b2w (decide (cond.denote env)))
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
        selectSwitch_nonzero (by simp [hc, b2w])
      have ihA := iha ha ([] :: funs) haWF hnA hinv hA
      cases hrun : Tx.run (Core.denote Γ a env) ctx w with
      | ok q =>
        rw [hrun] at ihA
        obtain ⟨V', st', hexec, hhaltS, hR⟩ := ihA
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod]
        refine ⟨restore V V', st', ?_, hhaltS, hR⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore tag hA) hexec
      | error err =>
        rw [hrun] at ihA
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
        simp only [except_error_prod]
        refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore tag hA) hexec
    · have hsel :
          selectSwitch evm (b2w (decide (cond.denote env)))
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
        simp [hc, b2w]
        exact selectSwitch_zero
      have ihB := ihb hb ([] :: funs) hbWF hnB hinv hB
      cases hrun : Tx.run (Core.denote Γ b env) ctx w with
      | ok q =>
        rw [hrun] at ihB
        obtain ⟨V', st', hexec, hhaltS, hR⟩ := ihB
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod]
        refine ⟨restore V V', st', ?_, hhaltS, hR⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore tag hB) hexec
      | error err =>
        rw [hrun] at ihB
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
        simp only [except_error_prod]
        refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore tag hB) hexec
  | letCall _ _ _ | callTail _ _ =>
    intro hM1
    exact False.elim (by simpa [M1Frag] using hM1)
  | @seqIf tBr _ cond th el k ihth ihel ihk =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    cases tBr with
    | pair _ _ => simp [M1Frag] at hM1
    | unit =>
      have ⟨hC, hth, hel, hk⟩ := m1frag_seqIf.mp hM1
      have ⟨hcWF, hthWF, helWF, hkWF, _⟩ := coreWF_seqIf.mp hwf
      simp only [Core.denote, Tx.run_bind]
      simp only [emitCore] at hem
      obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        th ({} : Emit) env.length
      obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := false) (clearLock := false)
        el ({} : Emit) env.length
      simp [hA, hB] at hem
      obtain ⟨eK, hKpre, hst⟩ := emitCore_prefix tag hem
      have hnA : identsNodup tag (env.length + coreExtraDepth th) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hnB : identsNodup tag (env.length + coreExtraDepth el) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup tag (env.length + coreExtraDepth k) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
      have hcond := eval_cond_ok tag (st := st) funs hinv.venv hinv.wf hC hcWF
      split_ifs with hc
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
          selectSwitch_nonzero (by simp [hc, b2w])
        have ihA := core_sim_fall tag hΓ hκ hlen th hth rfl
          ([] :: funs) hthWF hnA hinv hA
        cases hrun : Tx.run (Core.denote Γ th env) ctx w with
        | ok q =>
          rw [hrun] at ihA
          obtain ⟨VA, stA, hexecA, hRA, hctxA, hrestA⟩ := ihA
          rcases q with ⟨_, wA⟩
          have hinvK : Inv tag Γ c κ ctx wA env V stA :=
            ⟨hinv.venv, hinv.wf, hRA, hctxA⟩
          have ihK := ihk hk funs hkWF hnK hinvK hKpre
          cases hKrun : Tx.run (Core.denote Γ k env) ctx wA with
          | ok qk =>
            rw [hKrun] at ihK
            obtain ⟨VK, stK, hexeck, hsucc, hRK⟩ := ihK
            rcases qk with ⟨_, wK⟩
            simp only [except_ok_prod, hKrun]
            refine ⟨VK, stK, ?_, hsucc, hRK⟩
            rw [hst]
            have hsw := exec_switch hcond hsel (hoist_emitCore tag hA) hexecA
            rw [hrestA] at hsw
            exact execStmts_append hsw hexeck
          | error err =>
            rw [hKrun] at ihK
            obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
            simp only [except_ok_prod, hKrun, except_error_prod]
            refine ⟨VK, stK, bytes, ?_, hh, herr⟩
            rw [hst]
            have hsw := exec_switch hcond hsel (hoist_emitCore tag hA) hexecA
            rw [hrestA] at hsw
            exact execStmts_append hsw hexeck
        | error err =>
          rw [hrun] at ihA
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append_halt
            (exec_switch hcond hsel (hoist_emitCore tag hA) hexec)
      · have hsel :
            selectSwitch evm (b2w (decide (cond.denote env)))
              [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
          simp [hc, b2w]
          exact selectSwitch_zero
        have ihB := core_sim_fall tag hΓ hκ hlen el hel rfl
          ([] :: funs) helWF hnB hinv hB
        cases hrun : Tx.run (Core.denote Γ el env) ctx w with
        | ok q =>
          rw [hrun] at ihB
          obtain ⟨VB, stB, hexecB, hRB, hctxB, hrestB⟩ := ihB
          rcases q with ⟨_, wB⟩
          have hinvK : Inv tag Γ c κ ctx wB env V stB :=
            ⟨hinv.venv, hinv.wf, hRB, hctxB⟩
          have ihK := ihk hk funs hkWF hnK hinvK hKpre
          cases hKrun : Tx.run (Core.denote Γ k env) ctx wB with
          | ok qk =>
            rw [hKrun] at ihK
            obtain ⟨VK, stK, hexeck, hsucc, hRK⟩ := ihK
            rcases qk with ⟨_, wK⟩
            simp only [except_ok_prod, hKrun]
            refine ⟨VK, stK, ?_, hsucc, hRK⟩
            rw [hst]
            have hsw := exec_switch hcond hsel (hoist_emitCore tag hB) hexecB
            rw [hrestB] at hsw
            exact execStmts_append hsw hexeck
          | error err =>
            rw [hKrun] at ihK
            obtain ⟨VK, stK, bytes, hexeck, hh, herr⟩ := ihK
            simp only [except_ok_prod, hKrun, except_error_prod]
            refine ⟨VK, stK, bytes, ?_, hh, herr⟩
            rw [hst]
            have hsw := exec_switch hcond hsel (hoist_emitCore tag hB) hexecB
            rw [hrestB] at hsw
            exact execStmts_append hsw hexeck
        | error err =>
          rw [hrun] at ihB
          obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
          simp only [except_error_prod]
          refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append_halt
            (exec_switch hcond hsel (hoist_emitCore tag hB) hexec)
    | word | addr | flag =>
      have htWL : retTyWordLike (coreRetTy th) := trivial
      exact seqIf_wordLike_sim (tag := tag) hhalt hΓ hκ hlen htWL hM1
        ihk funs hwf hn hinv hem
  | opTailAddr op =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    simp only [emitCore] at hem
    cases hE : emitLetOp tag c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet tag e1 (env.length + 1) haltUnit (.addr (.var 0)) clearLock).stmts =
            e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
              (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts) :=
        emitRet_addr_stmts_if tag _ _ _ _ _
      have hden : Tx.run (Core.denote Γ (.opTailAddr op) env) ctx w =
          Tx.run (Op.denote Γ env op) ctx w := rfl
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        rw [hden, hopr]
        simp only [except_ok_prod]
        have hn0 : identsNodup tag (v :: env).length = true := by
          simpa using hn1
        have hstatic := ctxRel_static hinv1.ctxr
        have hMO := memOnly_stAfterLockClear clearLock st1
        have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st1)
          (Inv_memOnly tag hinv1 hMO).venv (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV tag env.length, BitVec.ofNat 256 v) :: V) hv he
            (R_memOnly hinv1.rel hMO)
        refine ⟨(identV tag env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_addr hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec (execStmts_maybe_lockClear clearLock hstatic hret)
      | error err =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        rw [hden, hopr]
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | opTailFlag op =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    simp only [emitCore] at hem
    cases hE : emitLetOp tag c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup tag (env.length + 1) = true :=
        identsNodup_mono tag (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet tag e1 (env.length + 1) haltUnit (.flag (.var 0)) clearLock).stmts =
            e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
              (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts) :=
        emitRet_flag_stmts_if tag _ _ _ _ _
      have hden : Tx.run (Core.denote Γ (.opTailFlag op) env) ctx w =
          Tx.run (Op.denote Γ env op) ctx w := rfl
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        rw [hden, hopr]
        simp only [except_ok_prod]
        have hn0 : identsNodup tag (v :: env).length = true := by
          simpa using hn1
        have hstatic := ctxRel_static hinv1.ctxr
        have hMO := memOnly_stAfterLockClear clearLock st1
        have he := eval_atom_ok tag funs (st := stAfterLockClear clearLock st1)
          (Inv_memOnly tag hinv1 hMO).venv (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV tag env.length, BitVec.ofNat 256 v) :: V) hv he
            (R_memOnly hinv1.rel hMO)
        refine ⟨(identV tag env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_flag hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec (execStmts_maybe_lockClear clearLock hstatic hret)
      | error err =>
        have hsim := op_sim tag funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        rw [hden, hopr]
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | revertTail err args =>
    intro hM1 w env V st funs hwf hn hinv clearLock e' hem
    have hnil : args.length = 0 := by simpa [M1Frag] using hM1
    match args with
    | _ :: _ => cases hnil
    | [] =>
      simp only [emitCore] at hem
      cases hem
      simp only [Core.denote, Tx.run_revert]
      exact revertTail_sim tag funs hinv hwf

theorem params_sim_zero (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (off : Nat) :
    ExecStmts evm funs V st (emitParams tag {} off 0).stmts V st .normal := by
  simp [emitParams_zero, Emit.stmts_nil]
  exact Step.seqNil

theorem toYulFn_inv {c f yul} (h : toYulFn c f = some yul) (hk : f.kind ≠ .constructor) :
    coreWF c f.core = true ∧
    identsNodup f.name (maxDepth f) = true ∧
    ∃ e, emitCore f.name c (emitParams f.name {} 4 f.params.length)
        f.params.length true f.core (locks f) = some e ∧
      yul = e.stmts := by
  unfold toYulFn at h
  have hwfB : coreWF c f.core = true := by
    by_contra hne
    have : (!coreWF c f.core) = true := by
      cases hcore : coreWF c f.core
      · rfl
      · exact (hne hcore).elim
    simp [this] at h
  have hnodB : identsNodup f.name (maxDepth f) = true := by
    by_contra hne
    have : (!identsNodup f.name (maxDepth f)) = true := by
      cases hnd : identsNodup f.name (maxDepth f)
      · rfl
      · exact (hne hnd).elim
    simp [hwfB, this] at h
  have hoffset : (if f.kind = FnKind.constructor then 0 else 4) = 4 := by
    simp [hk]
  have hhalt : decide (f.kind ≠ FnKind.constructor) = true := by simp [hk]
  simp [hwfB, hnodB, hoffset, hhalt] at h
  obtain ⟨e, hem⟩ := emitCore_some (tag := f.name) (c := c) (halt := true)
    (clearLock := locks f) f.core
    (emitParams f.name {} 4 f.params.length) f.params.length
  simp [hem] at h
  exact ⟨hwfB, hnodB, e, hem, by cases h; rfl⟩

theorem toYulFn_execStmts_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) (funs : FunEnv evm) :
    match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs [] st0 yul V' st' .halt ∧
          haltSuccess f.ret v st'.halted ∧ R c Γ κ w' st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs [] st0 yul V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  have hlocks : locks f = false := locks_eq_false_of_callFree hM1
  rw [hlocks] at hem
  subst hy
  set args := decodeArgs f st0.env.calldata
  have hargs : args = decodeArgs f st0.env.calldata := rfl
  simp only [← hargs]
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (tag := f.name) (funs := funs) st0 4 f.params.length hbound
  have hn : identsNodup f.name (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup f.name (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have hnEnv : identsNodup f.name args.reverse.length = true :=
    identsNodup_mono f.name (Nat.le_add_right _ _) hn'
  have hinv : Inv f.name Γ c κ ctx w args.reverse (toVEnv f.name args.reverse) st0 :=
    Inv.of_eq (tag := f.name) rfl hnEnv henv hR hctx
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix (tag := f.name) hem
  have h0' : emitCore f.name c {} args.reverse.length true f.core = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have hsim := core_sim (tag := f.name) (c := c) (Γ := Γ) (κ := κ) (ctx := ctx)
    (haltUnit := true) rfl hΓ hκ hlen f.core hM1 (funs := funs) hwf hn' hinv h0'
  cases hrun : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hsim ⊢
    obtain ⟨V', st', hexec, hsucc, hR'⟩ := hsim
    rcases p with ⟨v, w'⟩
    refine ⟨V', st', ?_, hsucc, hR'⟩
    rw [hst]
    have hpar' : ExecStmts evm funs [] st0 (emitParams f.name {} 4 f.params.length).stmts
        (toVEnv f.name args.reverse) st0 .normal := by
      convert hpar
      try simp [args, hdec]
    exact execStmts_append hpar' hexec
  | error err =>
    simp only [hrun, except_error_prod] at hsim ⊢
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    refine ⟨V', st', bytes, ?_, hh, herr⟩
    rw [hst]
    have hpar' : ExecStmts evm funs [] st0 (emitParams f.name {} 4 f.params.length).stmts
        (toVEnv f.name args.reverse) st0 .normal := by
      convert hpar
      try simp [args, hdec]
    exact execStmts_append hpar' hexec

theorem toYulFn_hoist {c f yul} (h : toYulFn c f = some yul)
    (hk : f.kind ≠ .constructor) : hoist evm yul = [] := by
  have ⟨_, _, e, hem, hy⟩ := toYulFn_inv h hk
  subst hy
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix (tag := f.name) hem
  rw [hst, hoist_append, hoist_params, hoist_emitCore (tag := f.name) h0]
  simp

end Lsc.Compiler

namespace Lsc.Compiler.Proof

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc
open Lsc.Compiler

theorem toYulFn_correct_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    ToYulFnCorrect c Γ κ f yul ctx w st0 := by
  have hsim := toYulFn_execStmts_callFree (c := c) (Γ := Γ) hΓ κ hκ f hf hM1 hlen
    hbound yul hyul ctx w st0 hctx hR [[]]
  have hhoist := toYulFn_hoist hyul hf
  set args := decodeArgs f st0.env.calldata
  have hargs : args = decodeArgs f st0.env.calldata := rfl
  simp only [← hargs] at hsim
  change match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
    | .ok (v, w') =>
        ∃ stObs, RunCommitted yul st0 [] stObs .halt ∧
          haltSuccess f.ret v stObs.halted ∧ R c Γ κ w' stObs
    | .error e =>
        ∃ stObs bytes,
          RunCommitted yul st0 [] stObs .halt ∧
            stObs.halted = some (.revert, bytes) ∧
            haltError c Γ e bytes ∧ R c Γ κ w stObs
  cases hrun : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hsim ⊢
    obtain ⟨V', st', hexec, hsucc, hR'⟩ := hsim
    have hRun : Run evm yul st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    refine ⟨st', ⟨st', hRun, ?_⟩, hsucc, hR'⟩
    obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
    exact (committedState_commit hh hk).symm
  | error err =>
    simp only [hrun, except_error_prod] at hsim ⊢
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    have hRun : Run evm yul st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    refine ⟨committedState st0 st', bytes, ⟨st', hRun, rfl⟩, ?_, herr,
      R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler.Proof
