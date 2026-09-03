import Lsc.Compile.IR.WordEvalLemmas
import Lsc.Compile.IR.Opt.FoldConsts
import Lsc.Compile.IR.Opt.ElimUnusedLocals
import Lsc.Compile.IR.Opt.Pipeline

namespace Lsc.Compile.IR

open Opt

private theorem IRState.setLocal_comm_of_ne (st : IRState) (first second : Lsc.Ident)
    (firstValue secondValue : Nat) (hne : first ≠ second) :
    (st.setLocal first firstValue).setLocal second secondValue =
      (st.setLocal second secondValue).setLocal first firstValue := by
  cases st
  simp only [IRState.setLocal]
  congr 1
  funext name
  by_cases hfirst : name = first
  · subst name
    simp [hne]
  · by_cases hsecond : name = second
    · subst name
      simp [hfirst]
    · simp [hfirst, hsecond]

/-- Setting a local which a statement does not mention commutes through the return-observing
evaluator.  The final states differ only by that same local update. -/
theorem evalStmtNatView_setLocal_unused (st : NatViewState) (name : Lsc.Ident) (value : Nat)
    (stmt : Stmt) (hunused : name ∉ freeVarsStmt stmt) :
    evalStmtNatView { st with state := st.state.setLocal name value } stmt =
      Option.map (fun result => { result with state := result.state.setLocal name value })
        (evalStmtNatView st stmt) := by
  induction stmt generalizing st with
  | skip => rfl
  | seq first rest ihFirst ihRest =>
      simp only [freeVarsStmt, List.mem_append] at hunused
      have hfirst : name ∉ freeVarsStmt first := fun h => hunused (Or.inl h)
      have hrest : name ∉ freeVarsStmt rest := fun h => hunused (Or.inr h)
      simp only [evalStmtNatView]
      rw [ihFirst st hfirst]
      cases heval : evalStmtNatView st first with
      | none => rfl
      | some next =>
          cases hhalt : next.halt with
          | running =>
              simpa [heval, hhalt] using ihRest next hrest
          | returned result => simp [hhalt]
          | reverted selector => simp [hhalt]
  | letBind other expr =>
      simp only [freeVarsStmt, List.mem_cons] at hunused
      have hne : name ≠ other := fun h => hunused (Or.inl h)
      have hexpr : name ∉ freeVarsExpr expr := fun h => hunused (Or.inr h)
      simp only [evalStmtNatView, Option.map]
      rw [evalExpr_setLocal_unused st.state name value expr hexpr]
      congr 1
      exact congrArg (fun state : IRState => ({ state := state, halt := st.halt } : NatViewState))
        (IRState.setLocal_comm_of_ne st.state name other value
          (evalExpr st.state expr) hne)
  | sstore => rfl
  | sstoreDyn => rfl
  | ifRevertSelector cond selector =>
      simp only [freeVarsStmt] at hunused
      simp only [evalStmtNatView, Option.map]
      rw [evalExpr_setLocal_unused st.state name value cond hunused]
      split <;> rfl
  | log => rfl
  | revertSelector => rfl
  | ret expr =>
      simp only [freeVarsStmt] at hunused
      simp only [evalStmtNatView, Option.map]
      rw [evalExpr_setLocal_unused st.state name value expr hunused]
  | checkReentrancyLock => rfl
  | setReentrancyLock => rfl
  | externalCall => rfl
  | externalCallBind => rfl
  | staticCall => rfl
  | staticCallBind => rfl

/-- An unused local update cannot change whether evaluation fails, returns, or reverts, nor the
returned value or revert selector. -/
theorem evalStmtNatView_setLocal_unused_halt (st : NatViewState) (name : Lsc.Ident)
    (value : Nat) (stmt : Stmt) (hunused : name ∉ freeVarsStmt stmt) :
    Option.map NatViewState.halt
        (evalStmtNatView { st with state := st.state.setLocal name value } stmt) =
      Option.map NatViewState.halt (evalStmtNatView st stmt) := by
  rw [evalStmtNatView_setLocal_unused st name value stmt hunused]
  cases evalStmtNatView st stmt <;> rfl

private theorem evalStmtNatView_seq_halt_congr (st : NatViewState) (first before after : Stmt)
    (hrest : ∀ next : NatViewState, next.halt = .running →
      Option.map NatViewState.halt (evalStmtNatView next before) =
        Option.map NatViewState.halt (evalStmtNatView next after)) :
    Option.map NatViewState.halt (evalStmtNatView st (.seq first before)) =
      Option.map NatViewState.halt (evalStmtNatView st (.seq first after)) := by
  simp only [evalStmtNatView]
  cases heval : evalStmtNatView st first with
  | none => rfl
  | some next =>
      cases hhalt : next.halt with
      | running => simpa [hhalt] using hrest next hhalt
      | returned value => simp [hhalt]
      | reverted selector => simp [hhalt]

/-- Eliminating unused locals preserves the complete return/revert observation of a running
return-observing Nat evaluation. -/
theorem evalStmtNatView_elimUnusedLocals (st : NatViewState) (stmt : Stmt)
    (hrunning : st.halt = .running) :
    Option.map NatViewState.halt (evalStmtNatView st (elimUnusedLocals stmt)) =
      Option.map NatViewState.halt (evalStmtNatView st stmt) := by
  induction stmt generalizing st with
  | seq first rest ihFirst ihRest =>
      cases first with
      | letBind name expr =>
          by_cases hused : name ∈ freeVarsStmt (elimUnusedLocals rest)
          · simp only [elimUnusedLocals, if_pos hused]
            exact evalStmtNatView_seq_halt_congr st (.letBind name expr)
              (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
          · simp only [elimUnusedLocals, if_neg hused]
            let bound : NatViewState :=
              { state := st.state.setLocal name (evalExpr st.state expr), halt := st.halt }
            have hbound : bound.halt = .running := by simp [bound, hrunning]
            have hseq :
                evalStmtNatView st (.seq (.letBind name expr) rest) =
                  evalStmtNatView bound rest := by
              simp [evalStmtNatView, bound, hrunning]
            calc
              Option.map NatViewState.halt (evalStmtNatView st (elimUnusedLocals rest)) =
                  Option.map NatViewState.halt
                    (evalStmtNatView
                      { st with state := st.state.setLocal name (evalExpr st.state expr) }
                      (elimUnusedLocals rest)) := by
                    symm
                    exact evalStmtNatView_setLocal_unused_halt st name
                      (evalExpr st.state expr) (elimUnusedLocals rest) hused
              _ = Option.map NatViewState.halt (evalStmtNatView bound rest) := by
                    simpa [bound] using ihRest bound hbound
              _ = Option.map NatViewState.halt
                    (evalStmtNatView st (.seq (.letBind name expr) rest)) := by rw [hseq]
      | skip =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st .skip
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | seq left right =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.seq left right)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | sstore slot expr =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.sstore slot expr)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | sstoreDyn slot value =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.sstoreDyn slot value)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | ifRevertSelector cond selector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.ifRevertSelector cond selector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | log topic data =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.log topic data)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | revertSelector selector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.revertSelector selector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | ret value =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.ret value)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | checkReentrancyLock selector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.checkReentrancyLock selector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | setReentrancyLock held =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st (.setReentrancyLock held)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | externalCall addr selector args checkBoolReturn failSelector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st
            (.externalCall addr selector args checkBoolReturn failSelector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | externalCallBind addr selector args bindName failSelector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st
            (.externalCallBind addr selector args bindName failSelector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | staticCall addr selector args retWords failSelector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st
            (.staticCall addr selector args retWords failSelector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
      | staticCallBind addr selector args bindName failSelector =>
          simp only [elimUnusedLocals]
          exact evalStmtNatView_seq_halt_congr st
            (.staticCallBind addr selector args bindName failSelector)
            (elimUnusedLocals rest) rest (fun next hnext => ihRest next hnext)
  | skip => rfl
  | letBind => rfl
  | sstore => rfl
  | sstoreDyn => rfl
  | ifRevertSelector => rfl
  | log => rfl
  | revertSelector => rfl
  | ret => rfl
  | checkReentrancyLock => rfl
  | setReentrancyLock => rfl
  | externalCall => rfl
  | externalCallBind => rfl
  | staticCall => rfl
  | staticCallBind => rfl

/-- Constant folding preserves the return-observing Nat view semantics, not merely the older
state-only observable semantics. -/
theorem evalStmtNatView_foldConstsStmt (st : NatViewState) (stmt : Stmt) :
    evalStmtNatView st (foldConstsStmt stmt) = evalStmtNatView st stmt := by
  induction stmt generalizing st with
  | skip => rfl
  | seq first rest ihFirst ihRest =>
      simp only [foldConstsStmt, evalStmtNatView]
      rw [ihFirst]
      cases hfirst : evalStmtNatView st first with
      | none => rfl
      | some next =>
          cases next.halt <;> simp [ihRest]
  | letBind name value =>
      simp [foldConstsStmt, evalStmtNatView, Opt.FoldConsts.foldConsts_correct]
  | sstore => rfl
  | sstoreDyn => rfl
  | ifRevertSelector cond selector =>
      simp [foldConstsStmt, evalStmtNatView, Opt.FoldConsts.foldConsts_correct]
  | log => rfl
  | revertSelector => rfl
  | ret value =>
      simp [foldConstsStmt, evalStmtNatView, Opt.FoldConsts.foldConsts_correct]
  | checkReentrancyLock => rfl
  | setReentrancyLock => rfl
  | externalCall => rfl
  | externalCallBind => rfl
  | staticCall => rfl
  | staticCallBind => rfl

/-- The complete optimizer pipeline preserves return/revert observations in the Nat view. -/
theorem evalStmtNatView_optimizeStmt (st : NatViewState) (stmt : Stmt)
    (hrunning : st.halt = .running) :
    Option.map NatViewState.halt (evalStmtNatView st (optimizeStmt stmt)) =
      Option.map NatViewState.halt (evalStmtNatView st stmt) := by
  unfold optimizeStmt
  calc
    Option.map NatViewState.halt
        (evalStmtNatView st (elimUnusedLocals (foldConstsStmt stmt))) =
      Option.map NatViewState.halt (evalStmtNatView st (foldConstsStmt stmt)) :=
        evalStmtNatView_elimUnusedLocals st (foldConstsStmt stmt) hrunning
    _ = Option.map NatViewState.halt (evalStmtNatView st stmt) := by
      rw [evalStmtNatView_foldConstsStmt]

/-- Under explicit no-wrap hypotheses on both forms, constant folding preserves an expression's
word value.  The second hypothesis is stated explicitly because Nat constant folding of an
underflowing subtraction is not EVM-word sound. -/
theorem evalExprWord_foldConsts (nat : IRState) (word : WordState) (e : Expr)
    (hst : word.Agrees nat)
    (hnw : ExprNoWrap nat e) (hnwFolded : ExprNoWrap nat (foldConsts e)) :
    evalExprWord word (foldConsts e) = evalExprWord word e := by
  obtain ⟨source, hsource, hsourceNat⟩ := evalExprWord_agrees nat word e hst hnw
  obtain ⟨folded, hfolded, hfoldedNat⟩ :=
    evalExprWord_agrees nat word (foldConsts e) hst hnwFolded
  rw [hsource, hfolded]
  congr 1
  apply (Word.eq_iff_toNat_eq folded source).mpr
  rw [hfoldedNat, hsourceNat, Opt.FoldConsts.foldConsts_correct]

/-- Constant folding preserves an observed returned word (up to equal `toNat`) for the supported
pure view fragment. -/
theorem foldConstsStmt_preserves_return (nat : NatViewState) (word : WordState) (stmt : Stmt)
    (hst : nat.Agrees word)
    (hnw : StmtNoWrap nat stmt)
    (hnwFolded : StmtNoWrap nat (foldConstsStmt stmt))
    {sourceResult : WordState} {sourceValue : Word}
    (hsource : evalStmtWord word stmt = some sourceResult)
    (hreturned : sourceResult.halt = .returned sourceValue) :
    ∃ foldedResult foldedValue,
      evalStmtWord word (foldConstsStmt stmt) = some foldedResult ∧
      foldedResult.halt = .returned foldedValue ∧
      foldedValue.toNat = sourceValue.toNat := by
  obtain ⟨natSource, wordSource, hnatSource, hwordSource, hagreeSource⟩ :=
    evalStmtWord_agrees nat word stmt hst hnw
  have hwordEq : wordSource = sourceResult := Option.some.inj (hwordSource.symm.trans hsource)
  subst wordSource
  cases hnatHalt : natSource.halt with
  | running =>
      simp [NatViewState.Agrees, hnatHalt, hreturned] at hagreeSource
  | returned natValue =>
      have hsourceValue : sourceValue.toNat = natValue := by
        simpa [NatViewState.Agrees, hnatHalt, hreturned] using hagreeSource.2
      obtain ⟨natFolded, wordFolded, hnatFolded, hwordFolded, hagreeFolded⟩ :=
        evalStmtWord_agrees nat word (foldConstsStmt stmt) hst hnwFolded
      have hnatFoldedEq : natFolded = natSource := by
        rw [evalStmtNatView_foldConstsStmt] at hnatFolded
        exact Option.some.inj (hnatFolded.symm.trans hnatSource)
      subst natFolded
      cases hfoldedHalt : wordFolded.halt with
      | running =>
          simp [NatViewState.Agrees, hnatHalt, hfoldedHalt] at hagreeFolded
      | returned foldedValue =>
          refine ⟨wordFolded, foldedValue, hwordFolded, hfoldedHalt, ?_⟩
          have hfoldedValue : foldedValue.toNat = natValue := by
            simpa [NatViewState.Agrees, hnatHalt, hfoldedHalt] using hagreeFolded.2
          exact hfoldedValue.trans hsourceValue.symm
      | reverted selector =>
          simp [NatViewState.Agrees, hnatHalt, hfoldedHalt] at hagreeFolded
  | reverted selector =>
      simp [NatViewState.Agrees, hnatHalt, hreturned] at hagreeSource

/-- A reusable bridge from Nat return/revert preservation to returned UInt256 preservation.
Both statement forms carry explicit dynamic no-wrap hypotheses. -/
theorem evalStmtWord_preserves_return_of_natHalt
    (nat : NatViewState) (word : WordState) (source optimized : Stmt)
    (hst : nat.Agrees word)
    (hnwSource : StmtNoWrap nat source)
    (hnwOptimized : StmtNoWrap nat optimized)
    (hNat :
      Option.map NatViewState.halt (evalStmtNatView nat optimized) =
        Option.map NatViewState.halt (evalStmtNatView nat source))
    {sourceResult : WordState} {sourceValue : Word}
    (hsource : evalStmtWord word source = some sourceResult)
    (hreturned : sourceResult.halt = .returned sourceValue) :
    ∃ optimizedResult optimizedValue,
      evalStmtWord word optimized = some optimizedResult ∧
      optimizedResult.halt = .returned optimizedValue ∧
      optimizedValue.toNat = sourceValue.toNat := by
  obtain ⟨natSource, wordSource, hnatSource, hwordSource, hagreeSource⟩ :=
    evalStmtWord_agrees nat word source hst hnwSource
  have hwordEq : wordSource = sourceResult := Option.some.inj (hwordSource.symm.trans hsource)
  subst wordSource
  obtain ⟨natOptimized, wordOptimized, hnatOptimized, hwordOptimized, hagreeOptimized⟩ :=
    evalStmtWord_agrees nat word optimized hst hnwOptimized
  have hnatHalt : natOptimized.halt = natSource.halt := by
    have hsome : some natOptimized.halt = some natSource.halt := by
      simpa [hnatOptimized, hnatSource] using hNat
    exact Option.some.inj hsome
  cases hsourceHalt : natSource.halt with
  | running =>
      simp [NatViewState.Agrees, hsourceHalt, hreturned] at hagreeSource
  | returned natValue =>
      have hsourceValue : sourceValue.toNat = natValue := by
        simpa [NatViewState.Agrees, hsourceHalt, hreturned] using hagreeSource.2
      have hoptimizedHalt : natOptimized.halt = .returned natValue :=
        hnatHalt.trans hsourceHalt
      cases hwordHalt : wordOptimized.halt with
      | running =>
          simp [NatViewState.Agrees, hoptimizedHalt, hwordHalt] at hagreeOptimized
      | returned optimizedValue =>
          refine ⟨wordOptimized, optimizedValue, hwordOptimized, hwordHalt, ?_⟩
          have hoptimizedValue : optimizedValue.toNat = natValue := by
            simpa [NatViewState.Agrees, hoptimizedHalt, hwordHalt] using hagreeOptimized.2
          exact hoptimizedValue.trans hsourceValue.symm
      | reverted selector =>
          simp [NatViewState.Agrees, hoptimizedHalt, hwordHalt] at hagreeOptimized
  | reverted selector =>
      simp [NatViewState.Agrees, hsourceHalt, hreturned] at hagreeSource

/-- Unused-local elimination preserves an observed returned word under explicit no-wrap
hypotheses for both executions. -/
theorem elimUnusedLocals_preserves_return
    (nat : NatViewState) (word : WordState) (stmt : Stmt)
    (hrunning : nat.halt = .running)
    (hst : nat.Agrees word)
    (hnw : StmtNoWrap nat stmt)
    (hnwEliminated : StmtNoWrap nat (elimUnusedLocals stmt))
    {sourceResult : WordState} {sourceValue : Word}
    (hsource : evalStmtWord word stmt = some sourceResult)
    (hreturned : sourceResult.halt = .returned sourceValue) :
    ∃ eliminatedResult eliminatedValue,
      evalStmtWord word (elimUnusedLocals stmt) = some eliminatedResult ∧
      eliminatedResult.halt = .returned eliminatedValue ∧
      eliminatedValue.toNat = sourceValue.toNat :=
  evalStmtWord_preserves_return_of_natHalt nat word stmt (elimUnusedLocals stmt)
    hst hnw hnwEliminated (evalStmtNatView_elimUnusedLocals nat stmt hrunning)
    hsource hreturned

/-- The complete optimizer pipeline preserves an observed returned UInt256 under explicit
no-wrap hypotheses for the source and optimized statements. -/
theorem optimizeStmt_preserves_return
    (nat : NatViewState) (word : WordState) (stmt : Stmt)
    (hrunning : nat.halt = .running)
    (hst : nat.Agrees word)
    (hnw : StmtNoWrap nat stmt)
    (hnwOptimized : StmtNoWrap nat (optimizeStmt stmt))
    {sourceResult : WordState} {sourceValue : Word}
    (hsource : evalStmtWord word stmt = some sourceResult)
    (hreturned : sourceResult.halt = .returned sourceValue) :
    ∃ optimizedResult optimizedValue,
      evalStmtWord word (optimizeStmt stmt) = some optimizedResult ∧
      optimizedResult.halt = .returned optimizedValue ∧
      optimizedValue.toNat = sourceValue.toNat :=
  evalStmtWord_preserves_return_of_natHalt nat word stmt (optimizeStmt stmt)
    hst hnw hnwOptimized (evalStmtNatView_optimizeStmt nat stmt hrunning)
    hsource hreturned

end Lsc.Compile.IR
