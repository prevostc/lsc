import Lsc.Compiler.Proof.DispatchProof
import Lsc.Compiler.CoreExtSimTheorems
import Lsc.Compiler.Proof.CallState
import Lsc.Compiler.DispatchExtDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
S2 backward dispatcher: `runtimeBlock_correct_ext`. The guard / selector /
`switch` wrapper is call-free (`step_descend` + `execStmts_det_evm`). The
selected `toYulFn` body may contain `call`; extra empty `FunEnv` scopes from
nested `block`s are dropped so `toYulFn_correct_ext` applies.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-! ### Empty `FunEnv` scopes are irrelevant to `Step` -/

def dropEmpty {D : Dialect} : FunEnv D → FunEnv D
  | [] => []
  | scope :: rest =>
      if scope.isEmpty then dropEmpty rest else scope :: dropEmpty rest

theorem dropEmpty_nil {D : Dialect} : dropEmpty ([] : FunEnv D) = [] := rfl

theorem dropEmpty_cons_nil {D : Dialect} (rest : FunEnv D) :
    dropEmpty ([] :: rest) = dropEmpty rest := by
  simp [dropEmpty]

theorem dropEmpty_cons_cons {D : Dialect} (x : Ident × FDecl D) (xs : FScope D)
    (rest : FunEnv D) :
    dropEmpty ((x :: xs) :: rest) = (x :: xs) :: dropEmpty rest := by
  simp [dropEmpty]

theorem dropEmpty_idem {D : Dialect} (funs : FunEnv D) :
    dropEmpty (dropEmpty funs) = dropEmpty funs := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    cases scope with
    | nil => simp [dropEmpty]; exact ih
    | cons x xs =>
      rw [dropEmpty_cons_cons, dropEmpty_cons_cons, ih]

theorem dropEmpty_cons_eq {D : Dialect} (s : FScope D) {funs1 funs2 : FunEnv D}
    (h : dropEmpty funs1 = dropEmpty funs2) :
    dropEmpty (s :: funs1) = dropEmpty (s :: funs2) := by
  cases s with
  | nil => simpa [dropEmpty] using h
  | cons x xs => simpa [dropEmpty] using congrArg (fun r => (x :: xs) :: r) h

theorem lookupFun_drop_of_some {D : Dialect} {funs : FunEnv D} {fn : Ident}
    {d : FDecl D} {cenv : FunEnv D}
    (h : lookupFun funs fn = some (d, cenv)) :
    ∃ cenv', lookupFun (dropEmpty funs) fn = some (d, cenv') ∧
      dropEmpty cenv = dropEmpty cenv' := by
  induction funs generalizing cenv with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
    cases scope with
    | nil =>
      simp [lookupFun, dropEmpty] at h ⊢
      exact ih h
    | cons x xs =>
      simp [lookupFun, dropEmpty] at h ⊢
      cases hfind : List.find? (fun p => p.1 = fn) (x :: xs) with
      | none =>
        simp [hfind] at h
        exact ih h
      | some p =>
        simp [hfind] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨(x :: xs) :: dropEmpty rest, rfl, ?_⟩
        simp [dropEmpty, dropEmpty_idem]

theorem lookupFun_some_of_drop {D : Dialect} {funs : FunEnv D} {fn : Ident}
    {d : FDecl D} {cenv' : FunEnv D}
    (h : lookupFun (dropEmpty funs) fn = some (d, cenv')) :
    ∃ cenv, lookupFun funs fn = some (d, cenv) ∧ dropEmpty cenv = dropEmpty cenv' := by
  induction funs generalizing cenv' with
  | nil => simp [dropEmpty, lookupFun] at h
  | cons scope rest ih =>
    cases scope with
    | nil =>
      simp [lookupFun, dropEmpty] at h ⊢
      exact ih h
    | cons x xs =>
      simp [lookupFun, dropEmpty] at h ⊢
      cases hfind : List.find? (fun p => p.1 = fn) (x :: xs) with
      | none =>
        simp [hfind] at h
        exact ih h
      | some p =>
        simp [hfind] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨(x :: xs) :: rest, rfl, ?_⟩
        simp [dropEmpty, dropEmpty_idem]

theorem lookupFun_congr {D : Dialect} {funs1 funs2 : FunEnv D}
    (hd : dropEmpty funs1 = dropEmpty funs2) {fn : Ident} {d : FDecl D}
    {c1 : FunEnv D} (h1 : lookupFun funs1 fn = some (d, c1)) :
    ∃ c2, lookupFun funs2 fn = some (d, c2) ∧ dropEmpty c1 = dropEmpty c2 := by
  obtain ⟨cD, hD, heq⟩ := lookupFun_drop_of_some h1
  rw [hd] at hD
  obtain ⟨c2, h2, heq2⟩ := lookupFun_some_of_drop hD
  exact ⟨c2, h2, heq.trans heq2.symm⟩

theorem step_of_dropEmpty {D : Dialect} [DecidableEq D.Value]
    {funs funs' : FunEnv D} {V : VEnv D} {st : D.State} {code : Code D.Op}
    {r : Res D} (hd : dropEmpty funs = dropEmpty funs')
    (h : Step D funs V st code r) : Step D funs' V st code r := by
  induction h generalizing funs' with
  | lit => exact Step.lit
  | var hv => exact Step.var hv
  | builtinOk hargs hop ih => exact Step.builtinOk (ih hd) hop
  | builtinHalt hargs hop ih => exact Step.builtinHalt (ih hd) hop
  | builtinArgsHalt hargs ih => exact Step.builtinArgsHalt (ih hd)
  | callOk hargs hlook hlen hbody ho ihargs ihbody =>
    obtain ⟨c2, hlook2, hceq⟩ := lookupFun_congr hd hlook
    exact Step.callOk (ihargs hd) hlook2 hlen (ihbody hceq) ho
  | callHalt hargs hlook hlen hbody ihargs ihbody =>
    obtain ⟨c2, hlook2, hceq⟩ := lookupFun_congr hd hlook
    exact Step.callHalt (ihargs hd) hlook2 hlen (ihbody hceq)
  | callArgsHalt hargs ih => exact Step.callArgsHalt (ih hd)
  | argsNil => exact Step.argsNil
  | argsCons hr he ihr ihe => exact Step.argsCons (ihr hd) (ihe hd)
  | argsRestHalt hr ih => exact Step.argsRestHalt (ih hd)
  | argsHeadHalt hr he ihr ihe => exact Step.argsHeadHalt (ihr hd) (ihe hd)
  | funDef => exact Step.funDef
  | block hbody ih => exact Step.block (ih (dropEmpty_cons_eq _ hd))
  | letZero => exact Step.letZero
  | letVal he hlen ih => exact Step.letVal (ih hd) hlen
  | letHalt he ih => exact Step.letHalt (ih hd)
  | assignVal he hlen ih => exact Step.assignVal (ih hd) hlen
  | assignHalt he ih => exact Step.assignHalt (ih hd)
  | exprStmt he ih => exact Step.exprStmt (ih hd)
  | exprStmtHalt he ih => exact Step.exprStmtHalt (ih hd)
  | ifTrue he hne hb ihe ihb => exact Step.ifTrue (ihe hd) hne (ihb hd)
  | ifFalse he hz ihe => exact Step.ifFalse (ihe hd) hz
  | ifHalt he ih => exact Step.ifHalt (ih hd)
  | switchExec he hb ihe ihb => exact Step.switchExec (ihe hd) (ihb hd)
  | switchHalt he ih => exact Step.switchHalt (ih hd)
  | forLoop hi hl ihi ihl =>
    exact Step.forLoop (ihi (dropEmpty_cons_eq _ hd)) (ihl (dropEmpty_cons_eq _ hd))
  | forInitHalt hi ih => exact Step.forInitHalt (ih (dropEmpty_cons_eq _ hd))
  | «break» => exact Step.«break»
  | «continue» => exact Step.«continue»
  | «leave» => exact Step.leave
  | seqNil => exact Step.seqNil
  | seqCons h1 h2 ih1 ih2 => exact Step.seqCons (ih1 hd) (ih2 hd)
  | seqStop hs hne ih => exact Step.seqStop (ih hd) hne
  | loopDone he hz ih => exact Step.loopDone (ih hd) hz
  | loopCondHalt he ih => exact Step.loopCondHalt (ih hd)
  | loopStep he hne hb ho hp hl ihe ihb ihp ihl =>
    exact Step.loopStep (ihe hd) hne (ihb hd) ho (ihp hd) (ihl hd)
  | loopPostHalt he hne hb ho hp ihe ihb ihp =>
    exact Step.loopPostHalt (ihe hd) hne (ihb hd) ho (ihp hd)
  | loopBreak he hne hb ihe ihb => exact Step.loopBreak (ihe hd) hne (ihb hd)
  | loopLeave he hne hb ihe ihb => exact Step.loopLeave (ihe hd) hne (ihb hd)
  | loopBodyHalt he hne hb ihe ihb => exact Step.loopBodyHalt (ihe hd) hne (ihb hd)

theorem dropEmpty_replicate_nil {D : Dialect} (n : Nat) :
    dropEmpty (List.replicate n ([] : FScope D)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dropEmpty, ih]

theorem restore_nil_any {D : Dialect} (Vb : VEnv D) :
    restore ([] : VEnv D) Vb = [] := by
  simp [restore]

theorem execStmts_of_dropEmpty {D : Dialect} [DecidableEq D.Value]
    {funs funs' : FunEnv D} {V : VEnv D} {st : D.State} {ss : Block D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (hd : dropEmpty funs = dropEmpty funs')
    (h : ExecStmts D funs V st ss V' st' o) :
    ExecStmts D funs' V st ss V' st' o :=
  step_of_dropEmpty hd h

theorem run_of_execStmts_open {calls : ExternalCalls} {yul : YBlock}
    {st0 : EvmState} {Vb : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hh : hoist (yulD calls) yul = [])
    (h : ExecStmts (yulD calls) [[]] [] st0 yul Vb st' o) :
    Run (yulD calls) yul st0 [] st' o := by
  have hb : ExecStmt (yulD calls) [] [] st0 (.block yul) (restore [] Vb) st' o :=
    Step.block (by rwa [hh])
  rw [restore_nil_any] at hb
  exact hb

/-! ### Call-free dispatcher prefix on `yulD` -/

theorem noExt_selector :
    noExtExpr (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) = true :=
  rfl

theorem noExt_guardLt (n : Nat) :
    noExtBlock (emitGuardLt {} n).stmts = true := by
  simp [emitGuardLt_stmts, noExtBlock, noExtStmts, noExtStmt, noExtExpr, noExtExprs,
    noExtOp, noExt_revert00]
  rfl

theorem noExtFuns_nils {calls : ExternalCalls} :
    ∀ n, noExtFuns (List.replicate n ([] : FScope (yulD calls))) = true
  | 0 => rfl
  | n + 1 => by
    simpa [List.replicate_succ] using
      noExtFuns_cons_nil (noExtFuns_nils (calls := calls) n)

theorem execStmts_singleton_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {s : YulSemantics.Stmt D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmts D funs V st [s] V' st' o) :
    ExecStmt D funs V st s V' st' o := by
  cases h with
  | seqCons h1 h2 =>
    cases h2
    exact h1
  | seqStop hs _ => exact hs

theorem exec_guardLt_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hcd : st.env.calldata.length < wordBound)
    (hn : n < wordBound)
    (h : ExecStmts (yulD calls) funs V st (emitGuardLt {} n).stmts V' st' o) :
    (st.env.calldata.length < n →
      o = .halt ∧ V' = V ∧
        st' = { touchMemory st 0 0 with halted := some (.revert, []) }) ∧
    (n ≤ st.env.calldata.length →
      o = .normal ∧ V' = V ∧ st' = st) := by
  have hno : noExtBlock (emitGuardLt {} n).stmts = true := noExt_guardLt n
  have hdesc := execStmts_descend hfuns hno h
  constructor
  · intro hshort
    have hfwd := guardLt_halt (funs := funEnvUncast calls funs) (V := V) (st := st)
      (n := n) hcd hn hshort
    have ⟨hV, hst, ho⟩ := execStmts_det_evm hfwd hdesc
    exact ⟨ho.symm, hV.symm, hst.symm⟩
  · intro hge
    have hfwd := guardLt_ok (funs := funEnvUncast calls funs) (V := V) (st := st)
      (n := n) hcd hn hge
    have ⟨hV, hst, ho⟩ := execStmts_det_evm hfwd hdesc
    exact ⟨ho.symm, hV.symm, hst.symm⟩

theorem exec_guardLt_block_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hcd : st.env.calldata.length < wordBound)
    (hn : n < wordBound)
    (h : ExecStmt (yulD calls) funs V st
      (.block (emitGuardLt {} n).stmts) V' st' o) :
    (st.env.calldata.length < n →
      o = .halt ∧ V' = V ∧
        st' = { touchMemory st 0 0 with halted := some (.revert, []) }) ∧
    (n ≤ st.env.calldata.length →
      o = .normal ∧ V' = V ∧ st' = st) := by
  obtain ⟨Vb, hss, hVeq⟩ := exec_block_inv h
  have hh : hoist (yulD calls) (emitGuardLt {} n).stmts = [] :=
    hoist_yulD_of_evm (calls := calls) (hoist_guardLt n)
  rw [hh] at hss
  have hinner := exec_guardLt_inv (noExtFuns_cons_nil hfuns) hcd hn hss
  constructor
  · intro hshort
    rcases hinner.1 hshort with ⟨rfl, ⟨hVb, rfl⟩⟩
    exact ⟨rfl, hVeq.trans (hVb ▸ restore_self_open V), rfl⟩
  · intro hge
    rcases hinner.2 hge with ⟨rfl, ⟨hVb, rfl⟩⟩
    exact ⟨rfl, hVeq.trans (hVb ▸ restore_self_open V), rfl⟩

theorem eval_selector_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {r : EResult (yulD calls)}
    (hfuns : noExtFuns funs = true)
    (h : EvalExpr (yulD calls) funs V st
      (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) r) :
    r = .vals [BitVec.ofNat 256 (calldataSelector st.env.calldata)] st := by
  have hdesc := evalExpr_descend hfuns noExt_selector h
  have hfwd := eval_selector (funs := funEnvUncast calls funs) V st
  have heq := evalExpr_det_evm hfwd hdesc
  cases r
  · simp [eresUncast] at heq
    obtain ⟨h1, h2⟩ := heq
    rw [← h1, h2]
  · simp [eresUncast] at heq

theorem exec_revert00_block_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st (.block [revert00]) V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } :=
  exec_revert00_block_inv h

theorem noExt_memoryGuardErased : noExtStmt memoryGuardErased = true := by
  unfold memoryGuardErased
  rfl

theorem ExtAgree_stAfterGuard {self : Address} {x : Lsc.ExtState} {st : EvmState}
    (h : ExtAgree self x st) : ExtAgree self x (stAfterGuard st) := by
  simpa [stAfterGuard] using h

theorem ExtAgree_committed_guard {self : Address} {x : Lsc.ExtState}
    {st0 st' : EvmState}
    (h : ExtAgree self x (committedState (stAfterGuard st0) st')) :
    ExtAgree self x (committedState st0 st') := by
  simpa [stAfterGuard] using h

theorem R_committed_guard {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st0 st' : EvmState}
    (hMO : MemOnly st0 (stAfterGuard st0))
    (hR : R c Γ κ w (committedState (stAfterGuard st0) st')) :
    R c Γ κ w (committedState st0 st') := by
  cases hhalt : st'.halted with
  | none =>
    have h1 : committedState (stAfterGuard st0) st' = st' := by simp [committedState, hhalt]
    have h2 : committedState st0 st' = st' := by simp [committedState, hhalt]
    rw [h2]; rwa [h1] at hR
  | some p =>
    rcases p with ⟨k, bytes⟩
    by_cases hc : k.commits = true
    · have h1 : committedState (stAfterGuard st0) st' = st' := by
        simp [committedState, hhalt, hc]
      have h2 : committedState st0 st' = st' := by simp [committedState, hhalt, hc]
      rw [h2]; rwa [h1] at hR
    · have h1 : committedState (stAfterGuard st0) st' =
          { stAfterGuard st0 with halted := st'.halted, returndata := st'.returndata } := by
        simp [committedState, hhalt, hc]
      have h2 : committedState st0 st' =
          { st0 with halted := st'.halted, returndata := st'.returndata } := by
        simp [committedState, hhalt, hc]
      rw [h2]
      apply R_memOnly (st := committedState (stAfterGuard st0) st') hR
      rw [h1]
      rcases hMO with ⟨hs, hl, hcaller, hv, ht, hn, ha, hst, hk, hcd, _⟩
      exact ⟨hs.symm, hl.symm, hcaller.symm, hv.symm, ht.symm, hn.symm, ha.symm,
        hst.symm, hk.symm, hcd.symm, rfl⟩

/-- `committedState` along a `MemOnly` start-state: storage-relevant `R` is
preserved because rollback restores the start state and success ignores it. -/
theorem R_committed_of_memOnly {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st0 st1 st' : EvmState}
    (hMO : MemOnly st0 st1)
    (hR : R c Γ κ w (committedState st1 st')) :
    R c Γ κ w (committedState st0 st') := by
  cases hhalt : st'.halted with
  | none =>
    have h1 : committedState st1 st' = st' := by simp [committedState, hhalt]
    have h2 : committedState st0 st' = st' := by simp [committedState, hhalt]
    rw [h2]; rwa [h1] at hR
  | some p =>
    rcases p with ⟨k, bytes⟩
    by_cases hc : k.commits = true
    · have h1 : committedState st1 st' = st' := by
        simp [committedState, hhalt, hc]
      have h2 : committedState st0 st' = st' := by simp [committedState, hhalt, hc]
      rw [h2]; rwa [h1] at hR
    · have h1 : committedState st1 st' =
          { st1 with halted := st'.halted, returndata := st'.returndata } := by
        simp [committedState, hhalt, hc]
      have h2 : committedState st0 st' =
          { st0 with halted := st'.halted, returndata := st'.returndata } := by
        simp [committedState, hhalt, hc]
      rw [h2]
      apply R_memOnly (st := committedState st1 st') hR
      rw [h1]
      rcases hMO with ⟨hs, hl, hcaller, hv, ht, hn, ha, hst, hk, hcd, _⟩
      exact ⟨hs.symm, hl.symm, hcaller.symm, hv.symm, ht.symm, hn.symm, ha.symm,
        hst.symm, hk.symm, hcd.symm, rfl⟩

theorem committedState_halted_eq (st0 st' : EvmState) :
    (committedState st0 st').halted = st'.halted := by
  unfold committedState
  split <;> [rfl; split <;> rfl]

theorem haltSuccess_committed_guard {t : RetTy} {v : t.denote} {st0 st' : EvmState}
    (h : haltSuccess t v (committedState (stAfterGuard st0) st').halted) :
    haltSuccess t v (committedState st0 st').halted := by
  simpa [committedState_halted_eq] using h

theorem exec_memoryGuardErased_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (h : ExecStmt (yulD calls) funs V st memoryGuardErased V' st' o) :
    o = .normal ∧ V' = V ∧ st' = stAfterGuard st := by
  have hdesc := execStmt_descend hfuns noExt_memoryGuardErased h
  have hfwd := exec_memoryGuardErased (funEnvUncast calls funs) V st
  have heq := step_det_evm hfwd hdesc
  injection heq with hV hst ho
  exact ⟨ho.symm, hV.symm, hst.symm⟩

theorem exec_lockCheck_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hLock : LockFree st)
    (h : ExecStmt (yulD calls) funs V st lockCheckStmt V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  have hdesc := execStmt_descend hfuns noExt_lockCheckStmt h
  have hfwd := exec_lockCheck_ok (funEnvUncast calls funs) V st hLock
  have heq := step_det_evm hfwd hdesc
  injection heq with hV hst ho
  exact ⟨ho.symm, hV.symm, hst.symm⟩

theorem exec_lockSet_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hstatic : st.env.static = false)
    (h : ExecStmt (yulD calls) funs V st lockSetStmt V' st' o) :
    o = .normal ∧ V' = V ∧
      st' = stTstore st (BitVec.ofNat 256 reentrancyLockSlot) 1 := by
  have hdesc := execStmt_descend hfuns noExt_lockSetStmt h
  have hfwd := exec_lockSetStmt (funEnvUncast calls funs) V st hstatic
  have heq := step_det_evm hfwd hdesc
  injection heq with hV hst ho
  exact ⟨ho.symm, hV.symm, hst.symm⟩

theorem exec_valueCheckPrefix_ok_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {f : FnDef} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (hok : f.payable = true ∨ st.env.callvalue = 0)
    (h : ExecStmts (yulD calls) funs V st (valueCheckPrefix f) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  have hdesc := execStmts_descend hfuns
    (by simpa [noExtBlock] using noExt_valueCheckPrefix f) h
  have hfwd :=
    exec_valueCheckPrefix_ok (funs := funEnvUncast calls funs) (V := V) hok
  have heq := execStmts_det_evm hfwd hdesc
  exact ⟨heq.2.2.symm, heq.1.symm, heq.2.1.symm⟩

theorem exec_valueCheckPrefix_halt_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {f : FnDef} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (hp : f.payable = false) (hv : st.env.callvalue ≠ 0)
    (h : ExecStmts (yulD calls) funs V st (valueCheckPrefix f) V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  have hdesc := execStmts_descend hfuns
    (by simpa [noExtBlock] using noExt_valueCheckPrefix f) h
  have hfwd :=
    exec_valueCheckPrefix_halt (funs := funEnvUncast calls funs) (V := V) hp hv
  have heq := execStmts_det_evm hfwd hdesc
  exact ⟨heq.2.2.symm, heq.1.symm, heq.2.1.symm⟩

theorem exec_valueGuardPrefix_ok_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {f : FnDef} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (hok : f.payable = true ∨ st.env.callvalue = 0)
    (hnw : f.payable = false ∨ st.env.selfBalance.ult st.env.callvalue = false)
    (h : ExecStmts (yulD calls) funs V st (valueGuardPrefix f) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  have hdesc := execStmts_descend hfuns
    (by simpa [noExtBlock] using noExt_valueGuardPrefix f) h
  have hfwd :=
    exec_valueGuardPrefix_ok (funs := funEnvUncast calls funs) (V := V) hok hnw
  have heq := execStmts_det_evm hfwd hdesc
  exact ⟨heq.2.2.symm, heq.1.symm, heq.2.1.symm⟩

theorem exec_valueGuardPrefix_valueHalt_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {f : FnDef} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (hp : f.payable = false) (hv : st.env.callvalue ≠ 0)
    (h : ExecStmts (yulD calls) funs V st (valueGuardPrefix f) V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  have hdesc := execStmts_descend hfuns
    (by simpa [noExtBlock] using noExt_valueGuardPrefix f) h
  have hfwd :=
    exec_valueGuardPrefix_valueHalt (funs := funEnvUncast calls funs) (V := V) hp hv
  have heq := execStmts_det_evm hfwd hdesc
  exact ⟨heq.2.2.symm, heq.1.symm, heq.2.1.symm⟩

theorem exec_valueGuardPrefix_wrapHalt_inv {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {f : FnDef} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true)
    (hp : f.payable = true)
    (hw : st.env.selfBalance.ult st.env.callvalue = true)
    (h : ExecStmts (yulD calls) funs V st (valueGuardPrefix f) V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  have hdesc := execStmts_descend hfuns
    (by simpa [noExtBlock] using noExt_valueGuardPrefix f) h
  have hfwd :=
    exec_valueGuardPrefix_wrapHalt (funs := funEnvUncast calls funs) (V := V) hp hw
  have heq := execStmts_det_evm hfwd hdesc
  exact ⟨heq.2.2.symm, heq.1.symm, heq.2.1.symm⟩

/-! ### `selectedFn` inversion -/

theorem selectedFn_none_of_find_none {c : ContractDef} {cd : List UInt8}
    (h4 : ¬ cd.length < 4)
    (h : c.functions.find? (fun f => f.selector = calldataSelector cd) = none) :
    selectedFn c cd = none := by
  simp [selectedFn, h4, h]

theorem selectedFn_none_of_short_params {c : ContractDef} {cd : List UInt8} {f : FnDef}
    (h4 : ¬ cd.length < 4)
    (hf : c.functions.find? (fun g => g.selector = calldataSelector cd) = some f)
    (hs : cd.length < 4 + 32 * f.params.length) :
    selectedFn c cd = none := by
  simp [selectedFn, h4, hf, hs]

theorem selectedFn_some_of {c : ContractDef} {cd : List UInt8} {f : FnDef}
    (h4 : ¬ cd.length < 4)
    (hf : c.functions.find? (fun g => g.selector = calldataSelector cd) = some f)
    (hs : ¬ cd.length < 4 + 32 * f.params.length) :
    selectedFn c cd = some f := by
  simp [selectedFn, h4, hf, hs]

theorem revert_obs {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st0 st' : EvmState}
    (hR : R c Γ κ w st0) (hh : st'.halted = some (.revert, [])) :
    (committedState st0 st').halted = some (.revert, []) ∧
      R c Γ κ w (committedState st0 st') :=
  ⟨by simp [committedState_rollback hh HaltKind.revert_commits, hh],
    R_rollback_obs hR hh HaltKind.revert_commits⟩

/-! ### Main theorem (`RuntimeBlockCorrectExt` is in `DispatchExtDefs.lean`) -/

namespace Proof
theorem runtimeBlock_correct_ext {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hAgr : ExtAgree ctx.self w.ext st0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hLock : LockFree st0) :
    RuntimeBlockCorrectExt c Γ κ o yul ctx w st0 := by
  intro st' out hrun
  obtain ⟨_, cases, hmap, hy⟩ := runtimeBlock_inv hyul
  obtain ⟨casesE, hmapE, hE⟩ := erase_runtimeBlock hyul
  rw [show casesE = cases from Option.some.inj (hmapE.symm.trans hmap)] at hE
  subst hy
  rw [hE] at hrun
  obtain ⟨Vb, hbody, _⟩ := run_block_inv hrun
  have hhoist := hoist_yulD_of_evm (calls := toCalls o)
    (hoist_erased_runtime (emitGuardLt {} 4).stmts
      (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) cases)
  rw [hhoist] at hbody
  have hfuns0 : noExtFuns ([] :: [] : FunEnv (yulD (toCalls o))) = true :=
    noExtFuns_nilScope
  cases execStmts_cons_inv hbody with
  | inr hstopG =>
    obtain ⟨hneG, hGhalt⟩ := hstopG
    exact (hneG (exec_memoryGuardErased_inv hfuns0 hGhalt).1).elim
  | inl hokG =>
    obtain ⟨VG, stA, hG, hrest⟩ := hokG
    have hGinv := exec_memoryGuardErased_inv hfuns0 hG
    obtain ⟨_, hVG, hstA⟩ := hGinv
    subst hVG
    have hstA0 : stA = st0 := by simpa [stAfterGuard] using hstA
    rw [hstA0] at hrest
    set cd := st0.env.calldata
    have hcd := ctxRel_calldata_lt hctx
    have hMO := memOnly_stAfterGuard st0
    have hctxA := ctxRel_memOnly hctx hMO
    have hRA := R_memOnly hR hMO
    have hAgrA := ExtAgree_stAfterGuard hAgr
    have hLockA : LockFree stA := hstA0.symm ▸ hLock
    have hcdA : (stAfterGuard st0).env.calldata = cd := by
      rcases hMO with ⟨_, _, _, _, _, _, _, _, _, hcd', _⟩
      exact hcd'
    have hlenA : (stAfterGuard st0).env.calldata.length = cd.length := by simp [hcdA]
    have hselA : calldataSelector (stAfterGuard st0).env.calldata =
        calldataSelector cd := by
      simp [hcdA]
    cases execStmts_cons_inv hrest with
    | inr hstopL =>
      obtain ⟨hneL, hLhalt⟩ := hstopL
      exact (hneL (exec_lockCheck_inv hfuns0 (by simpa [hstA0] using hLockA) hLhalt).1).elim
    | inl hokL =>
    obtain ⟨VL, stL0, hchk, hrest⟩ := hokL
    have hLinv := exec_lockCheck_inv hfuns0 (by simpa [hstA0] using hLockA) hchk
    obtain ⟨_, hVL, hstL⟩ := hLinv
    subst hVL
    rw [show stL0 = st0 from hstA0 ▸ hstL] at hrest
    cases execStmts_cons_inv hrest with
    | inr hstop =>
      obtain ⟨hne, hguard⟩ := hstop
      have hinv := exec_guardLt_block_inv hfuns0 (ctxRel_calldata_lt hctxA)
        four_lt_wordBound hguard
      by_cases hshort : cd.length < 4
      · rcases hinv.1 (by simpa [hlenA] using hshort) with ⟨ho, ⟨_, hst⟩⟩
        have hnone : selectedFn c cd = none := selectedFn_none_of_short hshort
        have hhalted : st'.halted = some (.revert, []) := by rw [hst]
        obtain ⟨hh, hR'⟩ := revert_obs hR hhalted
        simp [dispatchedFn, hnone]
        exact ⟨ho, hh, hR'⟩
      · rcases hinv.2 (Nat.not_lt.mp (by simpa [hlenA] using hshort)) with ⟨ho, _⟩
        exact (hne ho).elim
    | inl hok =>
    obtain ⟨V1, st1, hguard, htail⟩ := hok
    have hinv := exec_guardLt_block_inv hfuns0 (ctxRel_calldata_lt hctxA)
      four_lt_wordBound hguard
    by_cases hshort : cd.length < 4
    · rcases hinv.1 (by simpa [hlenA] using hshort) with ⟨ho, _⟩
      cases ho
    · rcases hinv.2 (Nat.not_lt.mp (by simpa [hlenA] using hshort)) with
        ⟨_, ⟨hVeq, hst⟩⟩
      subst hVeq
      rw [hst] at htail
      have hsw := execStmts_singleton_inv htail
      cases hsw with
      | switchHalt he =>
        have hr := eval_selector_open hfuns0 he
        cases hr
      | switchExec he hb =>
        have hr := eval_selector_open hfuns0 he
        injection hr with hvs hstSel
        rw [hstSel] at hb
        injection hvs with hcv _
        subst hcv
        rw [hselA] at hb
        rw [selectSwitch_uncast] at hb
        have hswM := selectSwitch_mapM (c := c) (sel := calldataSelector cd)
          (calldataSelector_lt_word cd) hmap
        cases hfind : c.functions.find? (fun f => f.selector = calldataSelector cd) with
        | none =>
          have hswEq : selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
              cases (some [revert00]) = [revert00] := by
            simpa [hfind] using hswM
          rw [hswEq] at hb
          rcases exec_revert00_block_open hb with ⟨ho, ⟨_, hst⟩⟩
          have hnone : selectedFn c cd = none :=
            selectedFn_none_of_find_none hshort hfind
          have hhalted : st'.halted = some (.revert, []) := by rw [hst]
          obtain ⟨hh, hR'⟩ := revert_obs hR hhalted
          simp [dispatchedFn, hnone]
          exact ⟨ho, hh, hR'⟩
        | some f =>
          obtain ⟨body, hyF, hswEq⟩ : ∃ body, toYulFn c f = some body ∧
              selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
                cases (some [revert00]) =
                YulSemantics.Stmt.block
                  (emitGuardLt {} (4 + 32 * f.params.length)).stmts ::
                  (valueGuardPrefix f ++ (lockSetPrefix f ++
                    [YulSemantics.Stmt.block body])) := by
            simpa [hfind] using hswM
          rw [hswEq] at hb
          have hfmem : f ∈ c.functions := mem_of_find? hfind
          obtain ⟨Vb2, hcase, hV2⟩ := exec_block_inv hb
          have hhcase : hoist (yulD (toCalls o))
              (YulSemantics.Stmt.block
                (emitGuardLt {} (4 + 32 * f.params.length)).stmts ::
                (valueGuardPrefix f ++ (lockSetPrefix f ++
                  [YulSemantics.Stmt.block body]))) = [] :=
            hoist_yulD_of_evm (calls := toCalls o) (hoist_entryCaseBody f _ _)
          rw [hhcase] at hcase
          have hfuns1 : noExtFuns
              ([] :: ([] :: []) : FunEnv (yulD (toCalls o))) = true :=
            noExtFuns_cons_nil hfuns0
          cases execStmts_cons_inv hcase with
          | inr hstopF =>
            obtain ⟨hneF, hgf⟩ := hstopF
            have hgi := exec_guardLt_block_inv hfuns1 (ctxRel_calldata_lt hctxA)
              (hbound f hfmem) hgf
            by_cases hshortF : cd.length < 4 + 32 * f.params.length
            · rcases hgi.1 (by simpa [hlenA] using hshortF) with ⟨ho, ⟨_, hst⟩⟩
              have hnone : selectedFn c cd = none :=
                selectedFn_none_of_short_params hshort hfind hshortF
              have hhalted : st'.halted = some (.revert, []) := by rw [hst]
              obtain ⟨hh, hR'⟩ := revert_obs hR hhalted
              simp [dispatchedFn, hnone]
              exact ⟨ho, hh, hR'⟩
            · rcases hgi.2 (Nat.not_lt.mp (by simpa [hlenA] using hshortF))
                with ⟨ho, _⟩
              exact (hneF ho).elim
          | inl hokF =>
            obtain ⟨V2, st2, hgf, hrestF⟩ := hokF
            have hgi := exec_guardLt_block_inv hfuns1 (ctxRel_calldata_lt hctxA)
              (hbound f hfmem) hgf
            by_cases hshortF : cd.length < 4 + 32 * f.params.length
            · rcases hgi.1 (by simpa [hlenA] using hshortF) with ⟨ho, _⟩
              cases ho
            · rcases hgi.2 (Nat.not_lt.mp (by simpa [hlenA] using hshortF)) with
                ⟨_, ⟨hVeqF, hstF⟩⟩
              subst hVeqF
              rw [hstF] at hrestF
              have hselF : selectedFn c cd = some f :=
                selectedFn_some_of hshort hfind hshortF
              cases execStmts_append_inv hrestF with
              | inr hstopV =>
                obtain ⟨hneV, hval⟩ := hstopV
                by_cases hwrap : f.payable && st0.env.selfBalance.ult st0.env.callvalue
                · have hp : f.payable = true := by
                    cases hpay : f.payable
                    · simp [hpay] at hwrap
                    · rfl
                  have hw :
                      (stAfterGuard st0).env.selfBalance.ult
                        (stAfterGuard st0).env.callvalue = true := by
                    simp [stAfterGuard, hp] at hwrap
                    exact hwrap
                  have hinv := exec_valueGuardPrefix_wrapHalt_inv hfuns1 hp hw hval
                  have hvo : valueOk f ctx.value = true := by
                    simp [valueOk, hp]
                  have hsome : dispatchedFn c cd ctx.value = some f := by
                    simp [dispatchedFn, hselF, hvo]
                  have hhalted : st'.halted = some (.revert, []) := by rw [hinv.2.2]
                  obtain ⟨hh, hR'⟩ := revert_obs hR hhalted
                  simp only [hsome, hwrap]
                  exact ⟨hinv.1, hh, hR'⟩
                · by_cases hvo : valueOk f ctx.value = true
                  · have hnw : f.payable = false ∨
                        (stAfterGuard st0).env.selfBalance.ult
                          (stAfterGuard st0).env.callvalue = false := by
                      cases hpay : f.payable
                      · exact Or.inl rfl
                      · refine Or.inr ?_
                        simpa [stAfterGuard, hpay] using hwrap
                    have hinv := exec_valueGuardPrefix_ok_inv hfuns1
                      (valueOk_to_callvalue hctxA hvo) hnw hval
                    exact (hneV hinv.1).elim
                  · have hp : f.payable = false := by
                      simp [valueOk] at hvo
                      cases hpay : f.payable
                      · rfl
                      · simp [hpay] at hvo
                    have hvnz : ctx.value ≠ 0 := by
                      simp [valueOk, hp] at hvo
                      exact hvo
                    have hcv : (stAfterGuard st0).env.callvalue ≠ 0 := by
                      intro heq
                      exact hvnz ((callvalue_eq_zero_iff hctxA).mp heq)
                    have hinv := exec_valueGuardPrefix_valueHalt_inv hfuns1 hp hcv hval
                    have hnone : dispatchedFn c cd ctx.value = none := by
                      simp [dispatchedFn, hselF, hvo]
                    have hhalted : st'.halted = some (.revert, []) := by rw [hinv.2.2]
                    obtain ⟨hh, hR'⟩ := revert_obs hR hhalted
                    simp [hnone]
                    exact ⟨hinv.1, hh, hR'⟩
              | inl hokV =>
                obtain ⟨VV, stV, hval, hrestL⟩ := hokV
                by_cases hwrap : f.payable && st0.env.selfBalance.ult st0.env.callvalue
                · have hp : f.payable = true := by
                    cases hpay : f.payable
                    · simp [hpay] at hwrap
                    · rfl
                  have hw :
                      (stAfterGuard st0).env.selfBalance.ult
                        (stAfterGuard st0).env.callvalue = true := by
                    simp [stAfterGuard, hp] at hwrap
                    exact hwrap
                  have hinv := exec_valueGuardPrefix_wrapHalt_inv hfuns1 hp hw hval
                  cases hinv.1
                · by_cases hvo : valueOk f ctx.value = true
                  · have hnw : f.payable = false ∨
                        (stAfterGuard st0).env.selfBalance.ult
                          (stAfterGuard st0).env.callvalue = false := by
                      cases hpay : f.payable
                      · exact Or.inl rfl
                      · refine Or.inr ?_
                        simpa [stAfterGuard, hpay] using hwrap
                    have hinv := exec_valueGuardPrefix_ok_inv hfuns1
                      (valueOk_to_callvalue hctxA hvo) hnw hval
                    obtain ⟨_, hVV, hstV⟩ := hinv
                    subst hVV
                    rw [hstV] at hrestL
                    have hsome : dispatchedFn c cd ctx.value = some f := by
                      simp [dispatchedFn, hselF, hvo]
                    by_cases hlocks : locks f
                    · have hpre : lockSetPrefix f = [lockSetStmt] := by
                        simp [lockSetPrefix, hlocks]
                      simp [hpre] at hrestL
                      cases execStmts_cons_inv hrestL with
                      | inr hstopS =>
                        obtain ⟨hneS, hset⟩ := hstopS
                        exact (hneS (exec_lockSet_inv hfuns1
                          (ctxRel_static hctxA) hset).1).elim
                      | inl hokS =>
                        obtain ⟨VS, stS, hset, hrestB⟩ := hokS
                        have hsetI := exec_lockSet_inv hfuns1 (ctxRel_static hctxA) hset
                        obtain ⟨_, hVS, hstS⟩ := hsetI
                        subst hVS
                        rw [hstS] at hrestB
                        have hbodyStmt := execStmts_singleton_inv hrestB
                        obtain ⟨Vb3, hss, _⟩ := exec_block_inv hbodyStmt
                        have hhf := hoist_yulD_of_evm (calls := toCalls o)
                          (toYulFn_hoist hyF (hctor f hfmem))
                        rw [hhf] at hss
                        set stL := stTstore (stAfterGuard st0)
                          (BitVec.ofNat 256 reentrancyLockSlot) 1
                        have hss' :
                            ExecStmts (yulD (toCalls o)) [[]] [] stL
                              body Vb3 st' out :=
                          execStmts_of_dropEmpty (by simp [dropEmpty]) hss
                        have hRun :
                            Run (yulD (toCalls o)) body stL [] st' out :=
                          run_of_execStmts_open hhf hss'
                        have hMOL := memOnly_tstore (stAfterGuard st0)
                          (BitVec.ofNat 256 reentrancyLockSlot) 1
                        have hctxL := ctxRel_memOnly hctxA hMOL
                        have hRL := R_memOnly hRA hMOL
                        have hAgrL := ExtAgree_tstore
                          (slot := BitVec.ofNat 256 reentrancyLockSlot)
                          (val := 1) hAgrA (ctxRel_address hctxA)
                        have hfn := toYulFn_correct_ext (c := c) (Γ := Γ) hΓ κ hκ o f
                          (hctor f hfmem) (hS2 f hfmem) hlen (hbound f hfmem) body hyF
                          ctx w stL hctxL hRL (by simpa [stL, stTstore] using hAgrL)
                          hOr hNR
                        have hMO_L : MemOnly st0 stL := by
                          simpa [stL, stAfterGuard] using
                            memOnly_tstore st0 (BitVec.ofNat 256 reentrancyLockSlot) 1
                        have hconcl := hfn st' out hRun
                        simp only [hsome, hwrap]
                        have hcdL : stL.env.calldata = cd := by
                          simp [stL, stTstore, hcdA]
                        rw [hcdL] at hconcl
                        cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f cd).reverse)
                            ctx w with
                        | ok p =>
                          rcases p with ⟨v, w'⟩
                          simp only [htx] at hconcl ⊢
                          obtain ⟨ho, hsucc, hR', hAgr'⟩ := hconcl
                          obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
                          have hh' : st'.halted = some (k, bs) := by
                            simpa [committedState_halted_eq] using hh
                          rw [committedState_commit (st0 := st0) hh' hk]
                          rw [committedState_commit (st0 := stL) hh' hk] at hR' hAgr'
                          exact ⟨ho, by simpa [committedState_halted_eq] using hsucc,
                            hR', hAgr'⟩
                        | error err =>
                          simp only [htx] at hconcl ⊢
                          obtain ⟨bytes, ho, hh, herr, hR'⟩ := hconcl
                          exact ⟨bytes, ho, by simpa [committedState_halted_eq] using hh,
                            herr, R_committed_of_memOnly hMO_L hR'⟩
                    · have hpre : lockSetPrefix f = [] := by
                        simp [lockSetPrefix, hlocks]
                      simp [hpre] at hrestL
                      have hbodyStmt := execStmts_singleton_inv hrestL
                      obtain ⟨Vb3, hss, _⟩ := exec_block_inv hbodyStmt
                      have hhf := hoist_yulD_of_evm (calls := toCalls o)
                        (toYulFn_hoist hyF (hctor f hfmem))
                      rw [hhf] at hss
                      have hss' :
                          ExecStmts (yulD (toCalls o)) [[]] [] (stAfterGuard st0)
                            body Vb3 st' out :=
                        execStmts_of_dropEmpty (by simp [dropEmpty]) hss
                      have hRun :
                          Run (yulD (toCalls o)) body (stAfterGuard st0) [] st' out :=
                        run_of_execStmts_open hhf hss'
                      have hfn := toYulFn_correct_ext (c := c) (Γ := Γ) hΓ κ hκ o f
                        (hctor f hfmem) (hS2 f hfmem) hlen (hbound f hfmem) body hyF
                        ctx w (stAfterGuard st0) hctxA hRA hAgrA hOr hNR
                      have hconcl := hfn st' out hRun
                      simp only [hsome, hwrap]
                      rw [hcdA] at hconcl
                      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f cd).reverse)
                          ctx w with
                      | ok p =>
                        rcases p with ⟨v, w'⟩
                        simp only [htx] at hconcl ⊢
                        obtain ⟨ho, hsucc, hR', hAgr'⟩ := hconcl
                        exact ⟨ho, haltSuccess_committed_guard hsucc,
                          R_committed_guard hMO hR', ExtAgree_committed_guard hAgr'⟩
                      | error err =>
                        simp only [htx] at hconcl ⊢
                        obtain ⟨bytes, ho, hh, herr, hR'⟩ := hconcl
                        exact ⟨bytes, ho, by simpa [committedState_halted_eq] using hh,
                          herr, R_committed_guard hMO hR'⟩
                  · have hp : f.payable = false := by
                      simp [valueOk] at hvo
                      cases hpay : f.payable
                      · rfl
                      · simp [hpay] at hvo
                    have hvnz : ctx.value ≠ 0 := by
                      simp [valueOk, hp] at hvo
                      exact hvo
                    have hcv : (stAfterGuard st0).env.callvalue ≠ 0 := by
                      intro heq
                      exact hvnz ((callvalue_eq_zero_iff hctxA).mp heq)
                    have hinv := exec_valueGuardPrefix_valueHalt_inv hfuns1 hp hcv hval
                    cases hinv.1

end Proof

end Lsc.Compiler

