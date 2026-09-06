import Lsc.Compiler.Proof.AbiCall
import Lsc.Compiler.Proof.OpsMore
import Lsc.Compiler.Proof.Lift

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
Backward simulation of `emitExtCall` for the M0 mini-fragment (arity 0).

S1 lemmas stay forward on `FunEnv evm`. Threading `∃ fo` through `core_sim` would
restate every S1 case, so M0 proves
`letOp (.call b m []) (ret .word (.var 0))` and `stmtTail (.call b m [])`.

Fault oracle: the call reads `w.ncalls`. Failure uses `composeFault ncalls true rest`
(Core does not bump `ncalls`). Success uses `composeFault ncalls false rest`; a
continuation would see indices `≥ ncalls + 1`. The mini-fragment has no continuation
calls, so `rest := fun _ => false`.
-/

namespace Lsc.Compiler

open YulSemantics
open Lsc hiding Op
open YulSemantics.EVM

def extTok (d : Nat) : YIdent := s!"_tok_{d}"
def extOk (d : Nat) : YIdent := s!"_ok_{d}"

theorem restore_self_open {D : Dialect} (V : VEnv D) : restore V V = V := by
  simp [restore]

theorem execStmts_append_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv (yulD calls)} {st1 : EvmState} {ss2 : YBlock}
    {V2 : VEnv (yulD calls)} {st2 : EvmState} {o : Outcome}
    (h1 : ExecStmts (yulD calls) funs V st ss1 V1 st1 .normal)
    (h2 : ExecStmts (yulD calls) funs V1 st1 ss2 V2 st2 o) :
    ExecStmts (yulD calls) funs V st (ss1 ++ ss2) V2 st2 o := by
  induction ss1 generalizing V st V1 st1 with
  | nil =>
    cases h1
    exact h2
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail => exact Step.seqCons hhead (ih htail h2)
    | seqStop _ hne => exact (hne rfl).elim

theorem execStmts_append_halt_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv (yulD calls)} {st1 : EvmState} {ss2 : YBlock}
    (h1 : ExecStmts (yulD calls) funs V st ss1 V1 st1 .halt) :
    ExecStmts (yulD calls) funs V st (ss1 ++ ss2) V1 st1 .halt := by
  induction ss1 generalizing V st with
  | nil => cases h1
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail => exact Step.seqCons hhead (ih htail)
    | seqStop hs ho => exact Step.seqStop hs ho

theorem yulD_zero (calls : ExternalCalls) : (yulD calls).zero = (0 : U256) := rfl

theorem builtin_iszero (calls : ExternalCalls) (st : EvmState) (x : U256) :
    builtinWithExternal calls .none .none Op.iszero [x] st
      (.ok [b2w (x = 0)] st) :=
  step_iszero st x

theorem builtin_lt (calls : ExternalCalls) (st : EvmState) (a b : U256) :
    builtinWithExternal calls .none .none Op.lt [a, b] st
      (.ok [b2w (a.ult b)] st) :=
  step_lt st a b

theorem selectorBytes_length (n : Nat) : (selectorBytes n).length = 4 := by
  simp [selectorBytes]

theorem wordBytes_length (n : Nat) : (wordBytes n).length = 32 := by
  simp [wordBytes]

theorem abiInput_length (spec : AbiSpec) (args : List Nat) :
    (abiInput spec args).length = 4 + 32 * args.length := by
  simp [abiInput, selectorBytes_length, List.length_append, List.length_flatMap,
    wordBytes_length]
  induction args with
  | nil => simp
  | cons _ args ih =>
    simp [ih]
    omega

theorem Abs.ofState_mstore {G} (α : Abs G) (st : EvmState) (p v : U256) (a : Address) :
    α.ofState { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v } a =
      α.ofState st a := by
  simp [α.ofState_proj, CallWorld.ofState, touchMemory]

theorem eval_sload_open {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) (slot : Nat) :
    EvalExpr (yulD calls) funs V st (bop Op.sload [lit slot])
      (.vals [st.storage (BitVec.ofNat 256 slot)] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) (by
    change builtinWithExternal calls .none .none Op.sload _ _ _
    simp only [evm_litValue_number, step_sload]
    rfl)

theorem exec_let_sload {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) (n : YIdent) (slot : Nat) :
    ExecStmt (yulD calls) funs V st
      (.letDecl [n] (some (bop Op.sload [lit slot])))
      ((n, st.storage (BitVec.ofNat 256 slot)) :: V) st .normal :=
  Step.letVal (eval_sload_open funs V st slot) rfl

theorem eval_shl_sel {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) (sel : Nat) :
    EvalExpr (yulD calls) funs V st (bop Op.shl [lit 224, lit sel])
      (.vals [BitVec.ofNat 256 sel <<< 224] st) :=
  Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) (by
    change builtinWithExternal calls .none .none Op.shl _ _ _
    simp only [evm_litValue_number, step_shl, toNat_224]
    rfl)

theorem exec_mstore_sel {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) (sel : Nat) :
    ExecStmt (yulD calls) funs V st
      (.exprStmt (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit sel]]))
      V { touchMemory st abiPtr 32 with
          memory := storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) } .normal :=
  Step.exprStmt (Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil (eval_shl_sel funs V st sel)) Step.lit)
    (by
      change builtinWithExternal calls .none .none Op.mstore _ _ _
      simp only [evm_litValue_number, step_mstore, toNat_abiPtr]
      rfl))

theorem revert00_exec {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) :
    ExecStmt (yulD calls) funs V st revert00 V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  refine Step.exprStmtHalt (Step.builtinHalt
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
    (by
      change builtinWithExternal calls .none .none Op.revert _ _ _
      simp only [evm_litValue_number, step_revert, toNat_ofNat_of_lt zero_lt_wordBound]
      rfl))

theorem revert00_block {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) :
    ExecStmt (yulD calls) funs V st (.block [revert00]) V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have hhoist : hoist (yulD calls) [revert00] = [] := by
    simp [hoist, revert00]
  have hbody :
      ExecStmts (yulD calls) (hoist (yulD calls) [revert00] :: funs) V st [revert00] V
        { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
    rw [hhoist]
    exact Step.seqStop (revert00_exec ([] :: funs) V st) halt_ne_normal
  have h := Step.block (D := yulD calls) hbody
  rw [restore_self_open] at h
  exact h

theorem eval_call_args {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (tok : YIdent) (target : U256) (hget : VEnv.get V tok = some target)
    (gas insize : Nat) :
    EvalArgs (yulD calls) funs V st
      [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]
      (.vals [BitVec.ofNat 256 gas, target, 0, BitVec.ofNat 256 abiPtr,
        BitVec.ofNat 256 insize, BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 32] st) :=
  Step.argsCons
    (Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons
            (Step.argsCons
              (Step.argsCons Step.argsNil Step.lit)
              Step.lit)
            Step.lit)
          Step.lit)
        Step.lit)
      (Step.var hget))
    Step.lit

theorem eval_call_of_resp {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (tok : YIdent) (target : U256) (hget : VEnv.get V tok = some target)
    (gas insize : Nat) (hstatic : st.env.static = false)
    (resp : CallResponse)
    (hCall : calls.Call
      { kind := .call
        gas := BitVec.ofNat 256 gas
        target := target
        value := 0
        input := readBytes st.memory (BitVec.ofNat 256 abiPtr).toNat
          (BitVec.ofNat 256 insize).toNat }
      st resp) :
    EvalExpr (yulD calls) funs V st
      (bop YulSemantics.EVM.Op.call
        [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])
      (.vals [resp.flag]
        (finishCall .call st resp
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat)) := by
  refine Step.builtinOk (eval_call_args funs V st tok target hget gas insize) ?_
  dsimp [yulD, evmWithExternal]
  simp only [builtinWithExternal, hstatic, Bool.false_and, ↓reduceIte]
  refine ⟨resp, ?_, ?_⟩
  · convert hCall
  · rfl

theorem exec_if_ok_fail {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (ok : YIdent) (hget : VEnv.get V ok = some (0 : U256)) :
    ExecStmt (yulD calls) funs V st
      (.cond (bop Op.iszero [var ok]) [revert00]) V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have hisz :
      EvalExpr (yulD calls) funs V st (bop Op.iszero [var ok]) (.vals [(1 : U256)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil (Step.var hget)) (by
      dsimp [yulD, evmWithExternal]
      simpa [b2w] using builtin_iszero calls st (0 : U256))
  have hne : (1 : U256) ≠ (yulD calls).zero := by simp [yulD_zero]
  exact Step.ifTrue hisz hne (revert00_block funs V st)

theorem exec_if_ok_succ {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (ok : YIdent) (hget : VEnv.get V ok = some (1 : U256)) :
    ExecStmt (yulD calls) funs V st
      (.cond (bop Op.iszero [var ok]) [revert00]) V st .normal := by
  have hisz :
      EvalExpr (yulD calls) funs V st (bop Op.iszero [var ok]) (.vals [(0 : U256)] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil (Step.var hget)) (by
      dsimp [yulD, evmWithExternal]
      simpa [b2w] using builtin_iszero calls st (1 : U256))
  exact Step.ifFalse hisz (by simp [yulD_zero])

theorem eval_rds {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) :
    EvalExpr (yulD calls) funs V st (bop Op.returndatasize [])
      (.vals [BitVec.ofNat 256 st.returndata.length] st) :=
  Step.builtinOk Step.argsNil (by
    change builtinWithExternal calls .none .none Op.returndatasize _ _ _
    exact step_returndatasize st)

theorem exec_word_check_fail {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (h : (BitVec.ofNat 256 st.returndata.length).ult 32 = true) :
    ExecStmt (yulD calls) funs V st
      (.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]) V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have hlt :
      EvalExpr (yulD calls) funs V st (bop Op.lt [bop Op.returndatasize [], lit 32])
        (.vals [(1 : U256)] st) := by
    refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      (eval_rds funs V st)) ?_
    dsimp [yulD, evmWithExternal]
    have heq :
        (BitVec.ofNat 256 st.returndata.length).ult
          (YulSemantics.EVM.litValue (.number 32)) = true := by
      have : YulSemantics.EVM.litValue (.number 32) = (32 : U256) := rfl
      rw [this]
      exact h
    have hbu := builtin_lt calls st (BitVec.ofNat 256 st.returndata.length)
      (YulSemantics.EVM.litValue (.number 32))
    simpa [heq, b2w] using hbu
  have hne : (1 : U256) ≠ (yulD calls).zero := by simp [yulD_zero]
  exact Step.ifTrue hlt hne (revert00_block funs V st)

theorem exec_word_check_ok {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState)
    (h : (BitVec.ofNat 256 st.returndata.length).ult 32 = false) :
    ExecStmt (yulD calls) funs V st
      (.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]) V st .normal := by
  have hlt :
      EvalExpr (yulD calls) funs V st (bop Op.lt [bop Op.returndatasize [], lit 32])
        (.vals [(0 : U256)] st) := by
    refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      (eval_rds funs V st)) ?_
    dsimp [yulD, evmWithExternal]
    have heq :
        (BitVec.ofNat 256 st.returndata.length).ult
          (YulSemantics.EVM.litValue (.number 32)) = false := by
      have : YulSemantics.EVM.litValue (.number 32) = (32 : U256) := rfl
      rw [this]
      exact h
    have hbu := builtin_lt calls st (BitVec.ofNat 256 st.returndata.length)
      (YulSemantics.EVM.litValue (.number 32))
    simpa [heq, b2w] using hbu
  exact Step.ifFalse hlt (by simp [yulD_zero])

theorem eval_mload_abi {calls : ExternalCalls} (funs : FunEnv (yulD calls))
    (V : VEnv (yulD calls)) (st : EvmState) :
    EvalExpr (yulD calls) funs V st (bop Op.mload [lit abiPtr])
      (.vals [loadWord st.memory abiPtr] (touchMemory st abiPtr 32)) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) (by
    change builtinWithExternal calls .none .none Op.mload _ _ _
    simp only [evm_litValue_number, step_mload, toNat_abiPtr]
    rfl)

theorem R_finishCall_fail {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} {resp : CallResponse} {iOff iSz oOff oSz : Nat}
    (hR : R c Γ κ w st) (h : resp.success = false) :
    R c Γ κ w (finishCall .call st resp iOff iSz oOff oSz) := by
  rcases hR with ⟨hs, hl, hk, hwf⟩
  refine ⟨?_, ?_, ?_, hwf⟩
  · rw [finishCall_storage_fail_eq (h := h)]; exact hs
  · unfold logsRel; rw [selfLogs_finishCall_fail (h := h), finishCall_address]; exact hl
  · rw [finishCall_keccak, hk]

theorem R_finishCall_success {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ G} {α : Abs G} {w : World S X E} {st : EvmState} {resp : CallResponse}
    {callee : Address} {iOff iSz oOff oSz : Nat}
    (hR : R c Γ κ w st) (hs : resp.success = true)
    (hni : NoInterfere α st resp.world callee) :
    R c Γ κ w (finishCall .call st resp iOff iSz oOff oSz) := by
  rcases hR with ⟨hsto, hl, hk, hwf⟩
  have ⟨hσ, _, _, _, _, _⟩ := hni
  refine ⟨?_, ?_, ?_, hwf⟩
  · rw [finishCall_storage_success_eq (hs := hs), hσ]; exact hsto
  · unfold logsRel
    rw [selfLogs_finishCall_success (α := α) hs hni, finishCall_address]
    exact hl
  · rw [finishCall_keccak, hk]

theorem emitCallRetCheck_word_stmts (e : Emit) :
    (emitCallRetCheck e .word).stmts =
      e.stmts ++ [.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]] :=
  emitIf_stmts _ _ _

theorem emitCallRetCheck_boolOpt_stmts (e : Emit) :
    (emitCallRetCheck e .boolOpt).stmts =
      e.stmts ++
        [.cond (bop Op.iszero
          [bop Op.or
            [bop Op.iszero [bop Op.returndatasize []],
              bop Op.and
                [bop Op.iszero [bop Op.lt [bop Op.returndatasize [], lit 32]],
                  bop Op.eq [bop Op.mload [lit abiPtr], lit 1]]]])
          [revert00]] :=
  emitIf_stmts _ _ _

theorem emitCallRetCheck_nil_word :
    (emitCallRetCheck {} .word).stmts =
      [.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]] := by
  simp [emitCallRetCheck_word_stmts, Emit.stmts_nil]

theorem emitCallRetCheck_nil_boolOpt :
    (emitCallRetCheck {} .boolOpt).stmts =
      [.cond (bop Op.iszero
        [bop Op.or
          [bop Op.iszero [bop Op.returndatasize []],
            bop Op.and
              [bop Op.iszero [bop Op.lt [bop Op.returndatasize [], lit 32]],
                bop Op.eq [bop Op.mload [lit abiPtr], lit 1]]]])
        [revert00]] := by
  simp [emitCallRetCheck_boolOpt_stmts, Emit.stmts_nil]

theorem emitExtCall_nil_stmts (c : ContractDef) (depth b m : Nat)
    (bind : Option YIdent) :
    (emitExtCall c {} depth b m [] bind).stmts =
      [.letDecl [extTok depth]
        (some (bop Op.sload [lit (bindingSlot c b)]))] ++
      [.exprStmt (bop Op.mstore
        [lit abiPtr, bop Op.shl [lit 224, lit (bindingMethod c b m).1]])] ++
      [.letDecl [extOk depth]
        (some (bop YulSemantics.EVM.Op.call
          [lit extCallGas, var (extTok depth), lit 0, lit abiPtr, lit 4,
            lit abiPtr, lit 32]))] ++
      [.cond (bop Op.iszero [var (extOk depth)]) [revert00]] ++
      (emitCallRetCheck {} (bindingMethod c b m).2).stmts ++
      match bind with
      | none => []
      | some name =>
        match (bindingMethod c b m).2 with
        | .boolOpt | .none => [.letDecl [name] (some (lit 1))]
        | .word => [.letDecl [name] (some (bop Op.mload [lit abiPtr]))] := by
  simp [emitExtCall, List.foldl_nil, emitLet, emitDo, emitIf, Emit.push, Emit.stmts,
    extTok, extOk, bop]
  cases bind with
  | none =>
    cases (bindingMethod c b m).2 with
    | word => simp [emitCallRetCheck, emitIf, Emit.push, bop]
    | boolOpt => simp [emitCallRetCheck, emitIf, Emit.push, bop]
    | none => simp [emitCallRetCheck, bop]
  | some name =>
    cases (bindingMethod c b m).2 with
    | word => simp [emitCallRetCheck, emitIf, emitLet, Emit.push, bop]
    | boolOpt => simp [emitCallRetCheck, emitIf, emitLet, Emit.push, bop]
    | none => simp [emitCallRetCheck, emitLet, Emit.push, bop]

/-- Mini-fragment: one arity-0 external call, then return the word / stop. -/
def CallProbe0 : {t : RetTy} → Core t → Prop
  | .word, .letOp (Lsc.Op.call _ _ args) (.ret (.word (.var 0))) => args = []
  | .unit, .stmtTail (Lsc.Stmt.call _ _ args) => args = []
  | _, _ => False

theorem VEnv.get_cons_open {D : Dialect} {x : Ident} {v : D.Value}
    {V : VEnv D} {y : Ident} :
    VEnv.get ((x, v) :: V) y = if x = y then some v else VEnv.get V y := by
  simp only [VEnv.get, List.find?]
  by_cases h : x = y
  · simp [h]
  · simp [h]

theorem restore_nil_open {D : Dialect} (Vb : VEnv D) :
    restore ([] : VEnv D) Vb = [] := by
  simp [restore]

theorem hoist_nil_open {calls : ExternalCalls} {ss : YBlock}
    (h : ∀ s ∈ ss, notFunDef s = true) : hoist (yulD calls) ss = [] := by
  simp only [hoist]
  refine List.filterMap_eq_nil_iff.mpr ?_
  intro s hs
  have hs' := h s hs
  cases s <;> simp [notFunDef] at hs' ⊢

theorem execStmts_cons_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {s : YStmt} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (yulD calls) funs V st (s :: ss) V' st' o) :
    (∃ V1 st1, ExecStmt (yulD calls) funs V st s V1 st1 .normal ∧
      ExecStmts (yulD calls) funs V1 st1 ss V' st' o) ∨
    (o ≠ .normal ∧ ExecStmt (yulD calls) funs V st s V' st' o) := by
  cases h with
  | seqCons h1 h2 => exact .inl ⟨_, _, h1, h2⟩
  | seqStop hs hne => exact .inr ⟨hne, hs⟩

theorem execStmts_append_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ss1 ss2 : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (yulD calls) funs V st (ss1 ++ ss2) V' st' o) :
    (∃ V1 st1, ExecStmts (yulD calls) funs V st ss1 V1 st1 .normal ∧
      ExecStmts (yulD calls) funs V1 st1 ss2 V' st' o) ∨
    (o ≠ .normal ∧ ExecStmts (yulD calls) funs V st ss1 V' st' o) := by
  induction ss1 generalizing V st with
  | nil =>
    exact .inl ⟨V, st, Step.seqNil, h⟩
  | cons s rest ih =>
    rw [List.cons_append] at h
    cases execStmts_cons_inv h with
    | inl h =>
      obtain ⟨V1, st1, hs, ht⟩ := h
      cases ih ht with
      | inl h2 =>
        obtain ⟨V2, st2, hr, hss⟩ := h2
        exact .inl ⟨V2, st2, Step.seqCons hs hr, hss⟩
      | inr h2 =>
        obtain ⟨hne, hr⟩ := h2
        exact .inr ⟨hne, Step.seqCons hs hr⟩
    | inr h =>
      obtain ⟨hne, hs⟩ := h
      exact .inr ⟨hne, Step.seqStop hs hne⟩

theorem eval_lit_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : Nat} {r}
    (h : EvalExpr (yulD calls) funs V st (lit n) r) :
    r = .vals [BitVec.ofNat 256 n] st := by
  cases h
  rfl

theorem eval_var_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {x : YIdent} {v : U256} {r}
    (hget : VEnv.get V x = some v)
    (h : EvalExpr (yulD calls) funs V st (var x) r) :
    r = .vals [v] st := by
  cases h
  rename_i v' hv
  have : v' = v := Option.some.inj (hv.symm.trans hget)
  subst this
  rfl

theorem evalArgs_nil_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st st' : EvmState} {vs}
    (h : EvalArgs (yulD calls) funs V st [] (.vals vs st')) :
    vs = [] ∧ st' = st := by
  cases h
  · exact ⟨rfl, rfl⟩

theorem evalArgs_cons_lit_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : Nat} {es : List YExpr}
    {vs : List U256} {st' : EvmState}
    (h : EvalArgs (yulD calls) funs V st (lit n :: es) (.vals vs st')) :
    ∃ vs', vs = BitVec.ofNat 256 n :: vs' ∧
      EvalArgs (yulD calls) funs V st es (.vals vs' st') := by
  cases h
  · next hrest hhead =>
    injection (eval_lit_unique hhead) with hlist hst
    injection hlist with hv
    subst hv; subst hst
    exact ⟨_, ⟨rfl, hrest⟩⟩

theorem evalArgs_cons_var_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {x : YIdent} {v : U256}
    {es : List YExpr} {vs : List U256} {st' : EvmState}
    (hget : VEnv.get V x = some v)
    (h : EvalArgs (yulD calls) funs V st (var x :: es) (.vals vs st')) :
    ∃ vs', vs = v :: vs' ∧
      EvalArgs (yulD calls) funs V st es (.vals vs' st') := by
  cases h
  · next hrest hhead =>
    injection (eval_var_unique hget hhead) with hlist hst
    injection hlist with hv
    subst hv; subst hst
    exact ⟨_, ⟨rfl, hrest⟩⟩

theorem eval_call_args_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st st' : EvmState}
    {tok : YIdent} {target : U256} {gas insize : Nat} {vs : List U256}
    (hget : VEnv.get V tok = some target)
    (h : EvalArgs (yulD calls) funs V st
      [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]
      (.vals vs st')) :
    vs = [BitVec.ofNat 256 gas, target, 0, BitVec.ofNat 256 abiPtr,
      BitVec.ofNat 256 insize, BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 32] ∧
    st' = st := by
  obtain ⟨vs1, ⟨e1, h1⟩⟩ := evalArgs_cons_lit_inv h
  subst e1
  obtain ⟨vs2, ⟨e2, h2⟩⟩ := evalArgs_cons_var_inv hget h1
  subst e2
  obtain ⟨vs3, ⟨e3, h3⟩⟩ := evalArgs_cons_lit_inv h2
  subst e3
  obtain ⟨vs4, ⟨e4, h4⟩⟩ := evalArgs_cons_lit_inv h3
  subst e4
  obtain ⟨vs5, ⟨e5, h5⟩⟩ := evalArgs_cons_lit_inv h4
  subst e5
  obtain ⟨vs6, ⟨e6, h6⟩⟩ := evalArgs_cons_lit_inv h5
  subst e6
  obtain ⟨vs7, ⟨e7, h7⟩⟩ := evalArgs_cons_lit_inv h6
  subst e7
  obtain ⟨hnil, hst⟩ := evalArgs_nil_inv h7
  subst hnil; subst hst
  exact ⟨rfl, rfl⟩

theorem eval_call_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {tok : YIdent} {target : U256} {gas insize : Nat} {r}
    (hget : VEnv.get V tok = some target)
    (hstatic : st.env.static = false)
    (h : EvalExpr (yulD calls) funs V st
      (bop YulSemantics.EVM.Op.call
        [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]) r) :
    ∃ resp : CallResponse,
      r = .vals [resp.flag]
        (finishCall .call st resp
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat) ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory (BitVec.ofNat 256 abiPtr).toNat
            (BitVec.ofNat 256 insize).toNat }
        st resp := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨hvs, hst⟩ := eval_call_args_inv hget hargs
    subst hvs; subst hst
    dsimp [yulD, evmWithExternal] at hbu
    simp only [builtinWithExternal, hstatic, Bool.false_and, ↓reduceIte] at hbu
    rcases hbu with ⟨resp, hCall, hres⟩
    injection hres with hrets hst
    subst hrets; subst hst
    exact ⟨resp, rfl, hCall⟩
  | builtinHalt hargs hbu =>
    obtain ⟨hvs, hst⟩ := eval_call_args_inv hget hargs
    subst hvs; subst hst
    dsimp [yulD, evmWithExternal] at hbu
    simp only [builtinWithExternal, hstatic, Bool.false_and, ↓reduceIte] at hbu
    rcases hbu with ⟨_, _, hres⟩
    cases hres
  | builtinArgsHalt hargs =>
    have : False := by
      cases hargs
      · next hh =>
        cases hh
        · next hh =>
          cases hh
          · next hh =>
            cases hh
            · next hh =>
              cases hh
              · next hh =>
                cases hh
                · next hh =>
                  cases hh
                  · next hh => cases hh
                  · next hhead => cases hhead
                · next hhead => cases hhead
              · next hhead => cases hhead
            · next hhead => cases hhead
          · next hhead => cases hhead
        · next hhead => cases hhead
      · next hhead => cases hhead
    exact this.elim

theorem decodeRet_word_ult {bs : List UInt8} {v : Nat} (h : decodeRet .word bs v) :
    (BitVec.ofNat 256 bs.length).ult 32 = false := by
  rcases h with ⟨h32, hwb, _⟩
  have hult := ult_ofNat hwb (by decide : (32 : Nat) < wordBound)
  have : ¬ bs.length < 32 := Nat.not_lt.mpr h32
  simpa [hult, decide_eq_false_iff_not] using this

theorem decodeRet_boolOpt_ok {bs : List UInt8} {v : Nat} (h : decodeRet .boolOpt bs v) :
    BitVec.ofNat 256 bs.length = 0 ∨
      ((BitVec.ofNat 256 bs.length).ult 32 = false ∧ wordFrom bs 0 = (1 : U256)) := by
  rcases h with ⟨_, hwb, hbody⟩
  cases hbody with
  | inl h0 =>
    refine .inl ?_
    simp [h0]
  | inr hge =>
    rcases hge with ⟨h32, hw⟩
    refine .inr ⟨?_, hw⟩
    have hult := ult_ofNat hwb (by decide : (32 : Nat) < wordBound)
    have : ¬ bs.length < 32 := Nat.not_lt.mpr h32
    simpa [hult, decide_eq_false_iff_not] using this

theorem haltSuccess_word_bytes {v : Nat} {h}
    (hh : h = some (.ret, wordBytes v)) : haltSuccess .word v h := by
  simp [haltSuccess, hh, retWords, abiBytes_singleton]

theorem haltSuccess_unit_stop {h} (hh : h = some (.stop, ([] : List UInt8))) :
    haltSuccess .unit () h := by
  simp [haltSuccess, hh]

theorem evalArgs_one_lit_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st st' : EvmState} {n : Nat} {vs}
    (h : EvalArgs (yulD calls) funs V st [lit n] (.vals vs st')) :
    vs = [BitVec.ofNat 256 n] ∧ st' = st := by
  obtain ⟨vs', ⟨e, hrest⟩⟩ := evalArgs_cons_lit_inv h
  subst e
  obtain ⟨hnil, hst⟩ := evalArgs_nil_inv hrest
  subst hnil; subst hst
  exact ⟨rfl, rfl⟩

theorem eval_sload_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {slot : Nat} {r}
    (h : EvalExpr (yulD calls) funs V st (bop Op.sload [lit slot]) r) :
    r = .vals [st.storage (BitVec.ofNat 256 slot)] st := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨hvs, hst⟩ := evalArgs_one_lit_inv hargs
    subst hvs; subst hst
    change builtinWithExternal calls .none .none Op.sload _ _ _ at hbu
    simp only [evm_litValue_number, step_sload] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨hvs, hst⟩ := evalArgs_one_lit_inv hargs
    subst hvs; subst hst
    change builtinWithExternal calls .none .none Op.sload _ _ _ at hbu
    simp only [evm_litValue_number, step_sload] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs
    · next hh => cases hh
    · next hhead => cases hhead

theorem selectorBytes_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : selectorBytes a = selectorBytes b) : a = b := by
  have := congrArg (fun l => l.foldl (fun acc b => acc * 256 + b.toNat) 0) h
  simpa [selectorBytes_beFold a ha, selectorBytes_beFold b hb] using this

theorem exec_let_sload_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {n : YIdent} {slot : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st
      (.letDecl [n] (some (bop Op.sload [lit slot]))) V' st' o) :
    o = .normal ∧ st' = st ∧ V' = (n, st.storage (BitVec.ofNat 256 slot)) :: V := by
  cases h with
  | letVal he hlen =>
    have hr := eval_sload_unique he
    injection hr with hvs hst
    subst hvs; subst hst
    exact ⟨rfl, rfl, rfl⟩
  | letHalt he =>
    have hr := eval_sload_unique he
    injection hr

theorem exec_let_call_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {tok ok : YIdent} {target : U256} {gas insize : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hget : VEnv.get V tok = some target)
    (hstatic : st.env.static = false)
    (h : ExecStmt (yulD calls) funs V st
      (.letDecl [ok] (some (bop YulSemantics.EVM.Op.call
        [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])))
      V' st' o) :
    ∃ resp, o = .normal ∧ V' = (ok, resp.flag) :: V ∧
      st' = finishCall .call st resp
        (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
        (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory (BitVec.ofNat 256 abiPtr).toNat
            (BitVec.ofNat 256 insize).toNat }
        st resp := by
  cases h with
  | letVal he hlen =>
    obtain ⟨resp, hr, hCall⟩ := eval_call_inv hget hstatic he
    injection hr with hvs hst
    subst hvs; subst hst
    exact ⟨resp, rfl, rfl, rfl, hCall⟩
  | letHalt he =>
    obtain ⟨resp, hr, _⟩ := eval_call_inv hget hstatic he
    injection hr

theorem names0_distinct :
    identV 0 ≠ extTok 0 ∧ identV 0 ≠ extOk 0 ∧ extTok 0 ≠ extOk 0 := by
  decide

theorem evalArgs_cons_vals_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {e : YExpr} {es : List YExpr}
    {vs : List U256} {st' : EvmState}
    (h : EvalArgs (yulD calls) funs V st (e :: es) (.vals vs st')) :
    ∃ v vs' st1, vs = v :: vs' ∧
      EvalArgs (yulD calls) funs V st es (.vals vs' st1) ∧
      EvalExpr (yulD calls) funs V st1 e (.vals [v] st') := by
  cases h
  · next hrest hhead => exact ⟨_, _, _, rfl, hrest, hhead⟩

theorem eval_bop1_vals_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {op : YOp} {e : YExpr}
    {vs : List U256} {st' : EvmState}
    (h : EvalExpr (yulD calls) funs V st (bop op [e]) (.vals vs st')) :
    ∃ v st1, EvalExpr (yulD calls) funs V st e (.vals [v] st1) ∧
      (yulD calls).Builtin op [v] st1 (.ok vs st') := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨v, vs', stMid, heq, hrest, hhead⟩ := evalArgs_cons_vals_inv hargs
    subst heq
    obtain ⟨hnil, hstMid⟩ := evalArgs_nil_inv hrest
    subst hnil; subst hstMid
    exact ⟨v, _, hhead, hbu⟩

theorem eval_bop2_vals_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {op : YOp} {e1 e2 : YExpr}
    {vs : List U256} {st' : EvmState}
    (h : EvalExpr (yulD calls) funs V st (bop op [e1, e2]) (.vals vs st')) :
    ∃ v1 v2 stA stB,
      EvalExpr (yulD calls) funs V st e2 (.vals [v2] stA) ∧
      EvalExpr (yulD calls) funs V stA e1 (.vals [v1] stB) ∧
      (yulD calls).Builtin op [v1, v2] stB (.ok vs st') := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨v1, vs1, stA, e1eq, hrest, h1⟩ := evalArgs_cons_vals_inv hargs
    subst e1eq
    obtain ⟨v2, vs2, st0, e2eq, hnilA, h2⟩ := evalArgs_cons_vals_inv hrest
    subst e2eq
    obtain ⟨hnil, hst0⟩ := evalArgs_nil_inv hnilA
    subst hnil; subst hst0
    exact ⟨v1, v2, stA, _, h2, h1, hbu⟩

theorem eval_shl_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {sel : Nat} {r}
    (h : EvalExpr (yulD calls) funs V st (bop Op.shl [lit 224, lit sel]) r) :
    r = .vals [BitVec.ofNat 256 sel <<< 224] st := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨vs1, ⟨e1, h1⟩⟩ := evalArgs_cons_lit_inv hargs
    subst e1
    obtain ⟨vs2, ⟨e2, h2⟩⟩ := evalArgs_cons_lit_inv h1
    subst e2
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv h2
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.shl _ _ _ at hbu
    simp only [evm_litValue_number, step_shl, toNat_224] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨vs1, ⟨e1, h1⟩⟩ := evalArgs_cons_lit_inv hargs
    subst e1
    obtain ⟨vs2, ⟨e2, h2⟩⟩ := evalArgs_cons_lit_inv h1
    subst e2
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv h2
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.shl _ _ _ at hbu
    simp only [evm_litValue_number, step_shl, toNat_224] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs
    · next hh =>
      cases hh
      · next hh => cases hh
      · next hhead => cases hhead
    · next hhead => cases hhead

theorem eval_mstore_sel_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {sel : Nat} {r}
    (h : EvalExpr (yulD calls) funs V st
      (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit sel]]) r) :
    r = .vals []
      { touchMemory st abiPtr 32 with
        memory := storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) } := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨vPtr, vs', stA, heq, hrest, hlit⟩ := evalArgs_cons_vals_inv hargs
    subst heq
    obtain ⟨vSh, vs2, st0, heq2, hnil, hshl⟩ := evalArgs_cons_vals_inv hrest
    subst heq2
    obtain ⟨hnil', hst0⟩ := evalArgs_nil_inv hnil
    subst hnil'; subst hst0
    injection (eval_shl_unique hshl) with hlist hstA
    injection hlist with hvSh
    subst hvSh; subst hstA
    injection (eval_lit_unique hlit) with hlist2 hstB
    injection hlist2 with hvPtr
    subst hvPtr; subst hstB
    change builtinWithExternal calls .none .none Op.mstore _ _ _ at hbu
    simp only [evm_litValue_number, step_mstore, toNat_abiPtr] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨vPtr, vs', stA, heq, hrest, hlit⟩ := evalArgs_cons_vals_inv hargs
    subst heq
    obtain ⟨vSh, vs2, st0, heq2, hnil, hshl⟩ := evalArgs_cons_vals_inv hrest
    subst heq2
    obtain ⟨hnil', hst0⟩ := evalArgs_nil_inv hnil
    subst hnil'; subst hst0
    dsimp [yulD, evmWithExternal] at hbu
    simp only [builtinWithExternal, step_mstore] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs with
    | argsRestHalt hrest =>
      cases hrest with
      | argsRestHalt hempty => cases hempty
      | argsHeadHalt _ hshl =>
        have hr := eval_shl_unique hshl
        injection hr
    | argsHeadHalt _ hlit =>
      cases hlit

theorem exec_mstore_sel_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {sel : Nat}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st
      (.exprStmt (bop Op.mstore [lit abiPtr, bop Op.shl [lit 224, lit sel]]))
      V' st' o) :
    o = .normal ∧ V' = V ∧
      st' = { touchMemory st abiPtr 32 with
        memory := storeWord st.memory abiPtr (BitVec.ofNat 256 sel <<< 224) } := by
  cases h with
  | exprStmt he =>
    have hr := eval_mstore_sel_unique he
    injection hr with _ hst
    exact ⟨rfl, rfl, hst⟩
  | exprStmtHalt he =>
    have hr := eval_mstore_sel_unique he
    injection hr

theorem eval_iszero_var_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ok : YIdent} {v : U256} {r}
    (hget : VEnv.get V ok = some v)
    (h : EvalExpr (yulD calls) funs V st (bop Op.iszero [var ok]) r) :
    r = .vals [b2w (v = 0)] st := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨vs', ⟨heq, hrest⟩⟩ := evalArgs_cons_var_inv hget hargs
    subst heq
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv hrest
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.iszero _ _ _ at hbu
    simp only [step_iszero] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨vs', ⟨heq, hrest⟩⟩ := evalArgs_cons_var_inv hget hargs
    subst heq
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv hrest
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.iszero _ _ _ at hbu
    simp only [step_iszero] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs
    · next hh => cases hh
    · next hhead => cases hhead

theorem eval_revert00_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {r}
    (h : EvalExpr (yulD calls) funs V st (bop Op.revert [lit 0, lit 0]) r) :
    r = .halt { touchMemory st 0 0 with halted := some (.revert, []) } := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨vs1, ⟨e1, h1⟩⟩ := evalArgs_cons_lit_inv hargs
    subst e1
    obtain ⟨vs2, ⟨e2, h2⟩⟩ := evalArgs_cons_lit_inv h1
    subst e2
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv h2
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.revert _ _ _ at hbu
    simp only [evm_litValue_number, step_revert, toNat_ofNat_of_lt zero_lt_wordBound] at hbu
    cases hbu
  | builtinHalt hargs hbu =>
    obtain ⟨vs1, ⟨e1, h1⟩⟩ := evalArgs_cons_lit_inv hargs
    subst e1
    obtain ⟨vs2, ⟨e2, h2⟩⟩ := evalArgs_cons_lit_inv h1
    subst e2
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv h2
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.revert _ _ _ at hbu
    simp only [evm_litValue_number, step_revert, toNat_ofNat_of_lt zero_lt_wordBound] at hbu
    cases hbu
    simp [readBytes]
  | builtinArgsHalt hargs =>
    cases hargs
    · next hh =>
      cases hh
      · next hh => cases hh
      · next hhead => cases hhead
    · next hhead => cases hhead

theorem exec_revert00_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st revert00 V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  cases h with
  | exprStmt he =>
    have hr := eval_revert00_unique he
    injection hr
  | exprStmtHalt he =>
    have hr := eval_revert00_unique he
    injection hr with hst
    exact ⟨rfl, rfl, hst⟩

theorem exec_revert00_block_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st (.block [revert00]) V' st' o) :
    o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) } := by
  cases h with
  | block hbody =>
    have hhoist : hoist (yulD calls) [revert00] = [] := by simp [hoist, revert00]
    rw [hhoist] at hbody
    cases hbody with
    | seqCons hs ht =>
      cases (exec_revert00_inv hs).1
    | seqStop hs _ =>
      obtain ⟨rfl, rfl, hst⟩ := exec_revert00_inv hs
      rw [restore_self_open]
      exact ⟨rfl, rfl, hst⟩

theorem exec_if_ok_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ok : YIdent} {flag : U256}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hget : VEnv.get V ok = some flag)
    (h : ExecStmt (yulD calls) funs V st
      (.cond (bop Op.iszero [var ok]) [revert00]) V' st' o) :
    (flag = 0 ∧ o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) }) ∨
    (flag ≠ 0 ∧ o = .normal ∧ V' = V ∧ st' = st) := by
  cases h with
  | ifTrue he hne hbody =>
    have hr := eval_iszero_var_unique hget he
    injection hr with hvs hst
    subst hst
    injection hvs with hcv
    have hflag : flag = 0 := by
      cases hdec : decide (flag = 0)
      · have hb : b2w (decide (flag = 0)) = (0 : U256) := by rw [hdec]; rfl
        exact (hne (hcv.trans (hb.trans (yulD_zero calls).symm))).elim
      · exact of_decide_eq_true hdec
    obtain ⟨rfl, rfl, hst⟩ := exec_revert00_block_inv hbody
    exact .inl ⟨hflag, rfl, rfl, hst⟩
  | ifFalse he hz =>
    have hr := eval_iszero_var_unique hget he
    injection hr with hvs hst
    subst hst
    injection hvs with hcv
    have hflag : flag ≠ 0 := by
      intro hf
      have hb : b2w (decide (flag = 0)) = (1 : U256) := by simp [hf]; rfl
      have : (1 : U256) = (0 : U256) :=
        (hcv.trans hb).symm.trans (hz.trans (yulD_zero calls))
      cases this
    exact .inr ⟨hflag, rfl, rfl, rfl⟩
  | ifHalt he =>
    have hr := eval_iszero_var_unique hget he
    injection hr

theorem eval_rds_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {r}
    (h : EvalExpr (yulD calls) funs V st (bop Op.returndatasize []) r) :
    r = .vals [BitVec.ofNat 256 st.returndata.length] st := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv hargs
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.returndatasize _ _ _ at hbu
    simp only [step_returndatasize] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨hnil, hst⟩ := evalArgs_nil_inv hargs
    subst hnil; subst hst
    change builtinWithExternal calls .none .none Op.returndatasize _ _ _ at hbu
    simp only [step_returndatasize] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs

theorem eval_lt_rds32_unique {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {r}
    (h : EvalExpr (yulD calls) funs V st
      (bop Op.lt [bop Op.returndatasize [], lit 32]) r) :
    r = .vals [b2w ((BitVec.ofNat 256 st.returndata.length).ult
      (YulSemantics.EVM.litValue (.number 32)))] st := by
  cases h with
  | builtinOk hargs hbu =>
    obtain ⟨vR, vs', stA, heq, hrest, hrds⟩ := evalArgs_cons_vals_inv hargs
    subst heq
    obtain ⟨v32, vs2, st0, heq2, hnil, h32⟩ := evalArgs_cons_vals_inv hrest
    subst heq2
    obtain ⟨hnil', hst0⟩ := evalArgs_nil_inv hnil
    subst hnil'; subst hst0
    injection (eval_rds_unique hrds) with hlist hstA
    injection hlist with hvR
    subst hvR; subst hstA
    injection (eval_lit_unique h32) with hlist2 hstB
    injection hlist2 with hv32
    subst hv32; subst hstB
    change builtinWithExternal calls .none .none Op.lt _ _ _ at hbu
    simp only [step_lt] at hbu
    cases hbu
    rfl
  | builtinHalt hargs hbu =>
    obtain ⟨vR, vs', stA, heq, hrest, hrds⟩ := evalArgs_cons_vals_inv hargs
    subst heq
    obtain ⟨v32, vs2, st0, heq2, hnil, h32⟩ := evalArgs_cons_vals_inv hrest
    subst heq2
    obtain ⟨hnil', hst0⟩ := evalArgs_nil_inv hnil
    subst hnil'; subst hst0
    change builtinWithExternal calls .none .none Op.lt _ _ _ at hbu
    simp only [step_lt] at hbu
    cases hbu
  | builtinArgsHalt hargs =>
    cases hargs with
    | argsRestHalt hrest =>
      cases hrest with
      | argsRestHalt hempty => cases hempty
      | argsHeadHalt _ hlit => cases hlit
    | argsHeadHalt _ hrds =>
      have hr := eval_rds_unique hrds
      injection hr

theorem exec_word_check_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (yulD calls) funs V st
      (.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]) V' st' o) :
    ((BitVec.ofNat 256 st.returndata.length).ult 32 = true ∧
      o = .halt ∧ V' = V ∧
      st' = { touchMemory st 0 0 with halted := some (.revert, []) }) ∨
    ((BitVec.ofNat 256 st.returndata.length).ult 32 = false ∧
      o = .normal ∧ V' = V ∧ st' = st) := by
  have h32 : YulSemantics.EVM.litValue (.number 32) = (32 : U256) := rfl
  cases h with
  | ifTrue he hne hbody =>
    have hr := eval_lt_rds32_unique he
    injection hr with hvs hstSt
    injection hvs with hcv
    cases hstSt
    have hult : (BitVec.ofNat 256 st.returndata.length).ult 32 = true := by
      cases hbit : (BitVec.ofNat 256 st.returndata.length).ult 32
      · have hb : b2w ((BitVec.ofNat 256 st.returndata.length).ult
            (YulSemantics.EVM.litValue (.number 32))) = (0 : U256) := by
          rw [h32, hbit]; rfl
        exact (hne (hcv.trans (hb.trans (yulD_zero calls).symm))).elim
      · rfl
    obtain ⟨rfl, rfl, hst⟩ := exec_revert00_block_inv hbody
    exact .inl ⟨hult, rfl, rfl, hst⟩
  | ifFalse he hz =>
    have hr := eval_lt_rds32_unique he
    injection hr with hvs hstSt
    injection hvs with hcv
    cases hstSt
    have hult : (BitVec.ofNat 256 st.returndata.length).ult 32 = false := by
      cases hbit : (BitVec.ofNat 256 st.returndata.length).ult 32
      · rfl
      · have hb : b2w ((BitVec.ofNat 256 st.returndata.length).ult
            (YulSemantics.EVM.litValue (.number 32))) = (1 : U256) := by
          rw [h32, hbit]; rfl
        have : (1 : U256) = (0 : U256) :=
          (hcv.trans hb).symm.trans (hz.trans (yulD_zero calls))
        cases this
    exact .inr ⟨hult, rfl, rfl, rfl⟩
  | ifHalt he =>
    have hr := eval_lt_rds32_unique he
    injection hr

theorem emitCore_call0_word (c : ContractDef) (b m : Nat) :
    emitCore c {} 0 true
      (.letOp (Lsc.Op.call b m []) (.ret (.word (.var 0)))) =
      some (emitRet (emitExtCall c {} 0 b m [] (some (identV 0))) 1 true
        (.word (.var 0))) := by
  simp [emitCore, emitLetOp]

theorem emitCore_call0_unit (c : ContractDef) (b m : Nat) :
    emitCore c {} 0 true (.stmtTail (Lsc.Stmt.call b m [])) =
      some (emitReturnUnit (emitExtCall c {} 0 b m [] none) true) := by
  simp [emitCore, emitStmt]

theorem atomE_var0 : atomE 1 (.var 0) = var (identV 0) := by
  simp [atomE]

theorem decodeArgs_nil (f : FnDef) (cd : List UInt8) (h : f.params = []) :
    decodeArgs f cd = [] := by
  simp [decodeArgs, h]

theorem bindingSlot_eq {c : ContractDef} {b : Nat} {bd : BindingDef}
    (h : c.bindings[b]? = some bd) : bindingSlot c b = bd.fieldSlot := by
  simp [bindingSlot, h]

theorem bindingMethod_eq {c : ContractDef} {b m : Nat} {bd : BindingDef}
    {p : String × AbiSpec}
    (hb : c.bindings[b]? = some bd) (hm : bd.methods[m]? = some p) :
    bindingMethod c b m = (p.2.selector, p.2.ret) := by
  simp [bindingMethod, hb, hm]

end Lsc.Compiler
