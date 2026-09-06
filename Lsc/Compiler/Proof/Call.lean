import Lsc.Compiler.Proof.AbiCall
import Lsc.Compiler.Proof.CallState
import Lsc.Compiler.Proof.Descend
import Lsc.Compiler.Proof.OpsMore

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
Backward simulation of the scoped `emitExtCall` block (`op_sim_call_bwd`).

Fault oracle: the call reads `w.ncalls`. Failure uses `composeFault ncalls true rest`
(Core does not bump `ncalls`). Success uses `composeFault ncalls false rest`; a
continuation sees indices `≥ ncalls + 1`.
-/

namespace Lsc.Compiler

open YulSemantics
open Lsc hiding Op Stmt
open YulSemantics.EVM

theorem yulD_zero (calls : ExternalCalls) : (yulD calls).zero = (0 : U256) := rfl

theorem hoist_nil_open {calls : ExternalCalls} {ss : YBlock}
    (h : ∀ s ∈ ss, notFunDef s = true) : hoist (yulD calls) ss = [] := by
  simp only [hoist]
  refine List.filterMap_eq_nil_iff.mpr ?_
  intro s hs
  have hs' := h s hs
  cases s <;> simp [notFunDef] at hs' ⊢


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

theorem bindingSlot_eq {c : ContractDef} {b : Nat} {bd : BindingDef}
    (h : c.bindings[b]? = some bd) : bindingSlot c b = bd.fieldSlot := by
  simp [bindingSlot, h]

theorem bindingMethod_eq {c : ContractDef} {b m : Nat} {bd : BindingDef}
    {p : String × AbiSpec}
    (hb : c.bindings[b]? = some bd) (hm : bd.methods[m]? = some p) :
    bindingMethod c b m = (p.2.selector, p.2.ret) := by
  simp [bindingMethod, hb, hm]

theorem emitCallRetCheck_word_stmts (e : Emit) :
    (emitCallRetCheck e .word).stmts =
      e.stmts ++ [.cond (bop Op.lt [bop Op.returndatasize [], lit 32]) [revert00]] :=
  emitIf_stmts _ _ _

theorem emitCallRetCheck_none_stmts (e : Emit) :
    (emitCallRetCheck e .none).stmts = e.stmts := rfl

/-- `let name := 0 { body }` or `{ body }` as produced by `emitExtCall`. -/
theorem emitExtCall_stmts' (c : ContractDef) (e : Emit) (d b m : Nat)
    (args : List Atom) (bind : Option YIdent) :
    (emitExtCall c e d b m args bind).stmts =
      e.stmts ++
        match bind with
        | none => [.block (emitExtCallBody c d b m args none)]
        | some name =>
          [.letDecl [name] (some (lit 0)),
           .block (emitExtCallBody c d b m args (some name))] :=
  emitExtCall_stmts c e d b m args bind

end Lsc.Compiler
