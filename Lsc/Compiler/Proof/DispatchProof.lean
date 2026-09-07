import Lsc.Compiler.Proof.CoreProof
import Lsc.Compiler.Proof.Erase
import Lsc.Compiler.DispatchDefs
import YulSemantics.Observation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of S1 dispatcher correctness. Statements live in `DispatchTheorems`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem four_lt_wordBound : 4 < wordBound := lt_256_wordBound (by decide)

theorem selector_lt_word (f : FnDef) : f.selector < wordBound :=
  Nat.lt_trans (selectorOf_lt f.name f.params) (by
    unfold wordBound
    exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2)
      (by decide : (32 : Nat) < 256))

theorem calldataSelector_lt (cd : List UInt8) : calldataSelector cd < 2 ^ 32 := by
  unfold calldataSelector
  have h : (wordFrom cd 0).toNat < 2 ^ 256 := (wordFrom cd 0).isLt
  have hdiv : (wordFrom cd 0).toNat / 2 ^ 224 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (by
      have hmul : (2 : Nat) ^ 224 * 2 ^ 32 = 2 ^ 256 := (Nat.pow_add 2 224 32).symm
      rw [hmul]; exact h)
  simpa [Nat.shiftRight_eq_div_pow] using hdiv

theorem calldataSelector_lt_word (cd : List UInt8) :
    calldataSelector cd < wordBound :=
  Nat.lt_trans (calldataSelector_lt cd) (by
    unfold wordBound
    exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2)
      (by decide : (32 : Nat) < 256))

theorem ushiftRight_eq_ofNat (x : U256) (n : Nat) :
    x >>> n = BitVec.ofNat 256 (x.toNat >>> n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt

theorem step_calldatasize (st : EvmState) :
    stepOp Op.calldatasize [] st =
      some (.ok [BitVec.ofNat 256 st.env.calldata.length] st) := rfl

theorem step_shr (st : EvmState) (shift val : U256) :
    stepOp Op.shr [shift, val] st = some (.ok [val >>> shift.toNat] st) := rfl

theorem readBytes_zero (mem : Nat → UInt8) (p : Nat) : readBytes mem p 0 = [] := by
  simp [readBytes]

theorem litToNat (n : Nat) (hn : n < wordBound) :
    (YulSemantics.EVM.litValue (.number n)).toNat = n := by
  rw [litValue_number, toNat_ofNat_of_lt hn]

theorem emitGuardLt_stmts (n : Nat) :
    (emitGuardLt {} n).stmts =
      [.cond (bop Op.lt [bop Op.calldatasize [], lit n]) [revert00]] := by
  simp [emitGuardLt, Emit.stmts_push, Emit.stmts_nil]

theorem hoist_revert00 : hoist evm [revert00] = [] := by simp [hoist, revert00]

theorem hoist_guardLt (n : Nat) : hoist evm (emitGuardLt {} n).stmts = [] := by
  simp [emitGuardLt_stmts, hoist]

theorem hoist_two_blocks (a b : YBlock) :
    hoist evm [.block a, .block b] = [] := by simp [hoist]

theorem hoist_runtime (guard : YBlock) (sel : YExpr)
    (cases : List (YulSemantics.Literal × YBlock)) :
    hoist evm [.block guard, .switch sel cases (some [revert00])] = [] := by
  simp [hoist]

theorem memoryGuardK_lt_wordBound : memoryGuardK < wordBound := by
  unfold memoryGuardK wordBound
  exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : (8 : Nat) < 256)

theorem toNat_memoryGuardK :
    (BitVec.ofNat 256 memoryGuardK).toNat = memoryGuardK :=
  toNat_ofNat_of_lt memoryGuardK_lt_wordBound

/-- The discarded-guard marker does not touch memory. -/
def stAfterGuard (st : EvmState) : EvmState := st

theorem memOnly_stAfterGuard (st : EvmState) : MemOnly st (stAfterGuard st) := by
  simp [MemOnly, stAfterGuard]

theorem memoryGuardK_ne_zero :
    evm.litValue (.number memoryGuardK) ≠ Dialect.zero evm := by
  simp [Dialect.zero, litValue, memoryGuardK]

theorem exec_empty_block (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmt evm funs V st (.block []) V st .normal := by
  have h : ExecStmt evm funs V st (.block []) (restore V V) st .normal :=
    Step.block (D := evm) (by
      change ExecStmts evm (hoist evm [] :: funs) V st [] V st .normal
      exact Step.seqNil)
  simpa [restore_self] using h

theorem exec_memoryGuardErased (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmt evm funs V st memoryGuardErased V (stAfterGuard st) .normal := by
  simpa [memoryGuardErased, stAfterGuard, lit] using
    Step.ifTrue (D := evm) (Step.lit (D := evm)) memoryGuardK_ne_zero
      (exec_empty_block funs V st)

theorem hoist_erased_runtime (guard : YBlock) (sel : YExpr)
    (cases : List (YulSemantics.Literal × YBlock)) :
    hoist evm (memoryGuardErased ::
      [.block guard, .switch sel cases (some [revert00])]) = [] := by
  simp [hoist, memoryGuardErased]

theorem exec_cons_normal {funs V st s V1 st1 rest V' st' o}
    (h1 : ExecStmt evm funs V st s V1 st1 .normal)
    (h2 : ExecStmts evm funs V1 st1 rest V' st' o) :
    ExecStmts evm funs V st (s :: rest) V' st' o :=
  Step.seqCons h1 h2

def erasedRuntime (cases : List (YulSemantics.Literal × YBlock)) : YBlock :=
  memoryGuardErased ::
    [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
      YulSemantics.Stmt.switch
        (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
        cases (some [revert00])]

theorem eval_calldatasize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st (bop Op.calldatasize [])
      (.vals [BitVec.ofNat 256 st.env.calldata.length] st) :=
  Step.builtinOk Step.argsNil (step_calldatasize _)

theorem eval_selector (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st
      (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
      (.vals [BitVec.ofNat 256 (calldataSelector st.env.calldata)] st) := by
  have hload :
      EvalExpr evm funs V st (bop Op.calldataload [lit 0])
        (.vals [wordFrom st.env.calldata 0] st) := by
    refine Step.builtinOk (Step.argsCons Step.argsNil Step.lit) ?_
    simp only [step_calldataload, litToNat 0 zero_lt_wordBound]
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hload) Step.lit) ?_
  simp only [evm_litValue_number, step_shr, toNat_224, ushiftRight_eq_ofNat]
  rfl

theorem revert00_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    ExecStmts evm funs V st [revert00] V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.seqStop (Step.exprStmtHalt (Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) ?_))
    halt_ne_normal
  simp only [step_revert, litToNat 0 zero_lt_wordBound, readBytes_zero]

theorem exec_block_halt {funs V st body V' st'}
    (hh : hoist evm body = [])
    (h : ExecStmts evm ([] :: funs) V st body V' st' .halt) :
    ExecStmt evm funs V st (.block body) (restore V V') st' .halt := by
  refine Step.block (D := evm) ?_
  rwa [hh]

theorem exec_block_ok {funs V st body V' st'}
    (hh : hoist evm body = [])
    (h : ExecStmts evm ([] :: funs) V st body V' st' .normal) :
    ExecStmt evm funs V st (.block body) (restore V V') st' .normal := by
  refine Step.block (D := evm) ?_
  rwa [hh]

theorem eval_lt_calldatasize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (n : Nat) (hcd : st.env.calldata.length < wordBound) (hn : n < wordBound) :
    EvalExpr evm funs V st
      (bop Op.lt [bop Op.calldatasize [], lit n])
      (.vals [b2w (decide (st.env.calldata.length < n))] st) := by
  have hsz := eval_calldatasize funs V st
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hsz) ?_
  simp only [step_lt, litValue_number, ult_ofNat hcd hn]

theorem guardLt_halt {funs V st n}
    (hcd : st.env.calldata.length < wordBound) (hn : n < wordBound)
    (hlt : st.env.calldata.length < n) :
    ExecStmts evm funs V st (emitGuardLt {} n).stmts V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have he := eval_lt_calldatasize funs V st n hcd hn
  have htrue : decide (st.env.calldata.length < n) = true := decide_eq_true hlt
  have inner :
      ExecStmts evm (hoist evm [revert00] :: funs) V st [revert00] V
        { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
    rw [hoist_revert00]
    exact revert00_exec _ _ _
  have hif :
      ExecStmt evm funs V st
        (.cond (bop Op.lt [bop Op.calldatasize [], lit n]) [revert00]) V
        { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
    refine Step.ifTrue (D := evm) he ?_ ?_
    · simp [htrue, b2w, Dialect.zero, litValue]
    · simpa [restore_self] using Step.block (D := evm) inner
  simpa [emitGuardLt_stmts] using Step.seqStop hif halt_ne_normal

theorem guardLt_ok {funs V st n}
    (hcd : st.env.calldata.length < wordBound) (hn : n < wordBound)
    (hge : n ≤ st.env.calldata.length) :
    ExecStmts evm funs V st (emitGuardLt {} n).stmts V st .normal := by
  have he := eval_lt_calldatasize funs V st n hcd hn
  have hfalse : decide (st.env.calldata.length < n) = false :=
    decide_eq_false (Nat.not_lt.mpr hge)
  have hif :
      ExecStmt evm funs V st
        (.cond (bop Op.lt [bop Op.calldatasize [], lit n]) [revert00]) V st .normal := by
    refine Step.ifFalse he ?_
    simp [hfalse, b2w, Dialect.zero, litValue]
  simpa [emitGuardLt_stmts] using Step.seqCons hif Step.seqNil

theorem entryCase_inv {c f p} (h : entryCase c f = some p) :
    ∃ body, toYulFn c f = some body ∧
      p = (YulSemantics.Literal.number f.selector,
        [YulSemantics.Stmt.block (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
          YulSemantics.Stmt.block body]) := by
  simp [entryCase, Bind.bind, Option.bind] at h
  cases hb : toYulFn c f <;> simp [hb] at h
  exact ⟨_, rfl, by cases h; rfl⟩

theorem mem_of_find? {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons x xs ih =>
    simp [List.find?] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem find?_pred {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons x xs ih =>
    simp [List.find?] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem selectSwitch_mapM {c : ContractDef} {sel : Nat} (hsel : sel < wordBound) :
    ∀ {fs : List FnDef} {cases : List (YulSemantics.Literal × YBlock)},
      fs.mapM (entryCase c) = some cases →
      match fs.find? (fun f => f.selector = sel) with
      | none =>
          selectSwitch evm (BitVec.ofNat 256 sel) cases (some [revert00]) = [revert00]
      | some f =>
          ∃ body, toYulFn c f = some body ∧
            selectSwitch evm (BitVec.ofNat 256 sel) cases (some [revert00]) =
              [YulSemantics.Stmt.block
                (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
                YulSemantics.Stmt.block body]
  | [], cases, hmap => by
    simp [List.mapM_nil] at hmap
    subst cases
    simp [selectSwitch, List.find?]
  | f :: rest, cases, hmap => by
    rw [List.mapM_cons] at hmap
    simp [Bind.bind, Option.bind, Pure.pure] at hmap
    cases hf : entryCase c f with
    | none => simp [hf] at hmap
    | some p =>
      simp [hf] at hmap
      cases hr : rest.mapM (entryCase c) with
      | none => simp [hr] at hmap
      | some cs =>
        simp [hr] at hmap
        subst cases
        obtain ⟨body, hb, hp⟩ := entryCase_inv hf
        subst p
        have ih := selectSwitch_mapM (fs := rest) (sel := sel) hsel hr
        cases hdec : decide (f.selector = sel) with
        | true =>
          have hpeq : f.selector = sel := of_decide_eq_true hdec
          have heq : BitVec.ofNat 256 sel = BitVec.ofNat 256 f.selector := by
            rw [ofNat_eq_iff hsel (selector_lt_word f), hpeq]
          simp [List.find?, hdec]
          refine ⟨body, hb, ?_⟩
          simp [selectSwitch, litValue_number, heq]
        | false =>
          have hpeq : ¬ f.selector = sel := of_decide_eq_false hdec
          have hne : BitVec.ofNat 256 sel ≠ BitVec.ofNat 256 f.selector := by
            intro h
            exact hpeq ((ofNat_eq_iff hsel (selector_lt_word f)).mp h).symm
          have hdec' :
              decide (BitVec.ofNat 256 sel =
                YulSemantics.EVM.litValue (.number f.selector)) = false := by
            rw [litValue_number]
            exact decide_eq_false hne
          simp [List.find?, hdec, selectSwitch, hdec']
          exact ih

theorem selectedFn_none_of_short {c cd} (h : cd.length < 4) :
    selectedFn c cd = none := by
  simp [selectedFn, h]

theorem run_of_exec {prog st0 st'}
    (hh : hoist evm prog = [])
    (h : ExecStmts evm [[]] [] st0 prog [] st' .halt) :
    Run evm prog st0 [] st' .halt := by
  have hb := Step.block (D := evm) (by rwa [hh])
  rw [restore_nil] at hb
  exact hb

theorem exec_head_halt {funs V st s rest st'}
    (h : ExecStmt evm funs V st s V st' .halt) :
    ExecStmts evm funs V st (s :: rest) V st' .halt :=
  Step.seqStop (rest := rest) h halt_ne_normal

theorem exec_pair_halt {funs V st s1 s2 st'}
    (h1 : ExecStmt evm funs V st s1 V st .normal)
    (h2 : ExecStmt evm funs V st s2 V st' .halt) :
    ExecStmts evm funs V st [s1, s2] V st' .halt :=
  Step.seqCons h1 (Step.seqStop (rest := []) h2 halt_ne_normal)

theorem switch_halt_nil {funs st cnd cv cases dflt body st'}
    (he : EvalExpr evm funs [] st cnd (.vals [cv] st))
    (hsel : selectSwitch evm cv cases dflt = body)
    (hh : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: funs) [] st body [] st' .halt) :
    ExecStmt evm funs [] st (.switch cnd cases dflt) [] st' .halt := by
  refine Step.switchExec he ?_
  rw [hsel]
  have hb := Step.block (D := evm) (by rwa [hh])
  rw [restore_nil] at hb
  exact hb

theorem obs_revert {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ yul st0 st'} {w : World S X E}
    (hR : R c Γ κ w st0)
    (hRun : Run evm yul st0 [] st' .halt)
    (hh : st'.halted = some (.revert, [])) :
    RunCommitted yul st0 [] (committedState st0 st') .halt ∧
      (committedState st0 st').halted = some (.revert, []) ∧
      R c Γ κ w (committedState st0 st') :=
  ⟨⟨st', hRun, rfl⟩,
    by simp [committedState_rollback hh HaltKind.revert_commits, hh],
    R_rollback_obs hR hh HaltKind.revert_commits⟩

end Lsc.Compiler

namespace Lsc.Compiler.Proof

open YulSemantics
open YulSemantics.EVM
open Lsc
open Lsc.Compiler

theorem runtimeBlock_correct_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    RuntimeBlockCorrectCallFree c Γ κ yul ctx w st0 := by
  simp only [RuntimeBlockCorrectCallFree]
  obtain ⟨_, cases, hmap, hy⟩ := runtimeBlock_inv hyul
  obtain ⟨casesE, hmapE, hE⟩ := erase_runtimeBlock hyul
  rw [show casesE = cases from Option.some.inj (hmapE.symm.trans hmap)] at hE
  subst hy
  rw [hE]
  set cd := st0.env.calldata
  have hcd := ctxRel_calldata_lt hctx
  set stA : EvmState := stAfterGuard st0
  have hG : ExecStmt evm [[]] [] st0 memoryGuardErased [] stA .normal :=
    exec_memoryGuardErased [[]] [] st0
  have hMO := memOnly_stAfterGuard st0
  have hctxA := ctxRel_memOnly hctx hMO
  have hRA := R_memOnly hR hMO
  have hcdA : stA.env.calldata = cd := by
    rcases hMO with ⟨_, _, _, _, _, _, _, _, _, hcd', _⟩
    exact hcd'
  have hhoist := hoist_erased_runtime (emitGuardLt {} 4).stmts
    (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) cases
  set stRev : EvmState :=
    { touchMemory stA 0 0 with halted := some (.revert, []) }
  have hhRev : stRev.halted = some (.revert, []) := rfl
  have hselE := eval_selector (funs := [[]]) [] stA
  rw [hcdA] at hselE
  by_cases hshort : cd.length < 4
  · have hnone : selectedFn c cd = none := selectedFn_none_of_short hshort
    have hguard := guardLt_halt (funs := [[], []]) (V := []) (st := stA)
      (n := 4) (by simpa [hcdA] using hcd) four_lt_wordBound (by simpa [hcdA] using hshort)
    have hblk := exec_block_halt (funs := [[]]) (V := []) (hoist_guardLt 4) hguard
    rw [restore_self] at hblk
    have hexec :
        ExecStmts evm [[]] [] st0 (erasedRuntime cases) [] stRev .halt :=
      exec_cons_normal hG (exec_head_halt hblk)
    have hRC := obs_revert (yul := erasedRuntime cases) hR
      (run_of_exec hhoist hexec) hhRev
    refine ⟨committedState st0 stRev, hRC.1, ?_⟩
    simp only [hnone]
    exact ⟨hRC.2.1, hRC.2.2⟩
  · have hge4 : 4 ≤ cd.length := Nat.le_of_not_gt hshort
    have hguard := guardLt_ok (funs := [[], []]) (V := []) (st := stA)
      (n := 4) (by simpa [hcdA] using hcd) four_lt_wordBound (by simpa [hcdA] using hge4)
    have hblk4 := exec_block_ok (funs := [[]]) (V := []) (hoist_guardLt 4) hguard
    rw [restore_self] at hblk4
    have hswM := selectSwitch_mapM (c := c) (sel := calldataSelector cd)
      (calldataSelector_lt_word cd) hmap
    cases hfind : c.functions.find? (fun f => f.selector = calldataSelector cd) with
    | none =>
      have hnone : selectedFn c cd = none := by
        simp [selectedFn, hshort, hfind]
      have hswEq : selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
          cases (some [revert00]) = [revert00] := by
        simpa [hfind] using hswM
      have hswStmt := switch_halt_nil hselE hswEq hoist_revert00
        (revert00_exec [[], []] [] stA)
      have hexec := exec_cons_normal hG (exec_pair_halt hblk4 hswStmt)
      have hRC := obs_revert (yul := erasedRuntime cases) hR
        (run_of_exec hhoist hexec) hhRev
      refine ⟨committedState st0 stRev, hRC.1, ?_⟩
      simp only [hnone]
      exact ⟨hRC.2.1, hRC.2.2⟩
    | some f =>
      have hfmem : f ∈ c.functions := mem_of_find? hfind
      have hfb := hbound f hfmem
      have ⟨body, hbody, hswEq⟩ :
          ∃ body, toYulFn c f = some body ∧
            selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
              cases (some [revert00]) =
                [YulSemantics.Stmt.block
                  (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
                  YulSemantics.Stmt.block body] := by
        simpa [hfind] using hswM
      set caseBody : YBlock :=
        [YulSemantics.Stmt.block (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
          YulSemantics.Stmt.block body]
      have hcaseH : hoist evm caseBody = [] := hoist_two_blocks _ _
      by_cases hshortF : cd.length < 4 + 32 * f.params.length
      · have hnone : selectedFn c cd = none := by
          simp [selectedFn, hshort, hfind, hshortF]
        have hgF := guardLt_halt (funs := [[], [], []]) (V := []) (st := stA)
          (n := 4 + 32 * f.params.length) (by simpa [hcdA] using hcd) hfb
          (by simpa [hcdA] using hshortF)
        have hblkF := exec_block_halt (funs := [[], []]) (V := [])
          (hoist_guardLt (4 + 32 * f.params.length)) hgF
        rw [restore_self] at hblkF
        have hcase : ExecStmts evm [[], []] [] stA caseBody [] stRev .halt :=
          exec_head_halt hblkF
        have hswStmt := switch_halt_nil hselE hswEq hcaseH hcase
        have hexec := exec_cons_normal hG (exec_pair_halt hblk4 hswStmt)
        have hRC := obs_revert (yul := erasedRuntime cases) hR
          (run_of_exec hhoist hexec) hhRev
        refine ⟨committedState st0 stRev, hRC.1, ?_⟩
        simp only [hnone]
        exact ⟨hRC.2.1, hRC.2.2⟩
      · have hsome : selectedFn c cd = some f := by
          simp [selectedFn, hshort, hfind, hshortF]
        have hgeF : 4 + 32 * f.params.length ≤ cd.length := Nat.le_of_not_gt hshortF
        have hgF := guardLt_ok (funs := [[], [], []]) (V := []) (st := stA)
          (n := 4 + 32 * f.params.length) (by simpa [hcdA] using hcd) hfb
          (by simpa [hcdA] using hgeF)
        have hblkF := exec_block_ok (funs := [[], []]) (V := [])
          (hoist_guardLt (4 + 32 * f.params.length)) hgF
        rw [restore_self] at hblkF
        have hsim := toYulFn_execStmts_callFree (c := c) (Γ := Γ) hΓ κ hκ f
          (hctor f hfmem) (hcf f hfmem) hlen (hbound f hfmem) body hbody
          ctx w stA hctxA hRA [[], [], []]
        have hfH := toYulFn_hoist hbody (hctor f hfmem)
        have hargs : cd = st0.env.calldata := rfl
        simp only [cd, hcdA] at hsim hsome
        cases hrun : Tx.run (Core.denote Γ f.core
            (decodeArgs f st0.env.calldata).reverse) ctx w with
        | ok p =>
          simp only [hrun, except_ok_prod, hcdA] at hsim
          obtain ⟨V', st', hexecB, hsucc, hR'⟩ := hsim
          have hbodyStmt :
              ExecStmt evm [[], []] [] stA (.block body) [] st' .halt := by
            have hb := exec_block_halt (funs := [[], []]) (V := []) hfH hexecB
            rw [restore_nil] at hb
            exact hb
          have hcase : ExecStmts evm [[], []] [] stA caseBody [] st' .halt :=
            exec_pair_halt hblkF hbodyStmt
          have hswStmt := switch_halt_nil hselE hswEq hcaseH hcase
          have hexec := exec_cons_normal hG (exec_pair_halt hblk4 hswStmt)
          have hRun := run_of_exec hhoist hexec
          obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
          refine ⟨st', ⟨st', hRun, (committedState_commit hh hk).symm⟩, ?_⟩
          rw [hsome]
          simp only [cd]
          simp only [hrun, except_ok_prod]
          exact ⟨hsucc, hR'⟩
        | error err =>
          simp only [hrun, except_error_prod, hcdA] at hsim
          obtain ⟨V', st', bytes, hexecB, hh, herr⟩ := hsim
          have hbodyStmt :
              ExecStmt evm [[], []] [] stA (.block body) [] st' .halt := by
            have hb := exec_block_halt (funs := [[], []]) (V := []) hfH hexecB
            rw [restore_nil] at hb
            exact hb
          have hcase : ExecStmts evm [[], []] [] stA caseBody [] st' .halt :=
            exec_pair_halt hblkF hbodyStmt
          have hswStmt := switch_halt_nil hselE hswEq hcaseH hcase
          have hexec := exec_cons_normal hG (exec_pair_halt hblk4 hswStmt)
          have hRun := run_of_exec hhoist hexec
          refine ⟨committedState st0 st', ⟨st', hRun, rfl⟩, ?_⟩
          rw [hsome]
          simp only [cd]
          simp only [hrun, except_error_prod]
          refine ⟨bytes, ?_, herr, R_rollback_obs hR hh HaltKind.revert_commits⟩
          simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler.Proof

