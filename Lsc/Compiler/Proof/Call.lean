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

variable (tag : String)

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

theorem evalArgs_cons_vals_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {e : YExpr} {es : List YExpr}
    {vs : List U256} {st' : EvmState}
    (h : EvalArgs (yulD calls) funs V st (e :: es) (.vals vs st')) :
    ∃ v vs' st1, vs = v :: vs' ∧
      EvalArgs (yulD calls) funs V st es (.vals vs' st1) ∧
      EvalExpr (yulD calls) funs V st1 e (.vals [v] st') := by
  cases h
  · next hrest hhead => exact ⟨_, _, _, rfl, hrest, hhead⟩

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

theorem emitAssign_stmts (e : Emit) (n : YIdent) (x : YExpr) :
    (emitAssign e n x).stmts = e.stmts ++ [.assign [n] x] :=
  Emit.stmts_push _ _

theorem emitCallRetCheck_boolOpt_stmts (e : Emit) :
    (emitCallRetCheck e .boolOpt).stmts =
      e.stmts ++
        [.cond
          (bop Op.iszero
            [bop Op.or
              [bop Op.iszero [bop Op.returndatasize []],
                bop Op.and
                  [bop Op.iszero [bop Op.lt [bop Op.returndatasize [], lit 32]],
                    bop Op.eq [bop Op.mload [lit abiPtr], lit 1]]]])
          [revert00]] :=
  emitIf_stmts _ _ _

theorem emitLetOp_call (c : ContractDef) (e : Emit) (d b m : Nat) (args : List Atom) :
    emitLetOp tag c e d (.call b m args) =
      some (emitExtCall tag c e d b m args (some (identV tag d))) := rfl

theorem emitStmt_call (c : ContractDef) (e : Emit) (d b m : Nat) (args : List Atom) :
    emitStmt tag c e d (.call b m args) = emitExtCall tag c e d b m args none := rfl

theorem extTok_string tag (d : Nat) : extTok tag d = tag ++ "__tok_" ++ toString d := rfl

theorem extOk_string tag (d : Nat) : extOk tag d = tag ++ "__ok_" ++ toString d := rfl

private theorem toDigits10_isDigit {n : Nat} {c : Char}
    (h : c ∈ Nat.toDigits 10 n) : c.isDigit := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by decide : (1 : Nat) < 10)] at h
    split at h
    · simp only [List.mem_singleton] at h
      subst h
      simp [Nat.isDigit_digitChar]
      omega
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) h
      · simp [Nat.isDigit_digitChar]
        exact Nat.mod_lt n (by decide)

private theorem toString_nat_head_ne_underscore (n : Nat) :
    (toString n).toList.head? ≠ some '_' := by
  have hlist : (toString n).toList = Nat.toDigits 10 n := by
    rw [Nat.toString_eq_repr, Nat.toList_repr]
  intro h
  have hmem : '_' ∈ Nat.toDigits 10 n := by
    rw [← hlist]
    exact List.mem_of_mem_head? h
  have hdig := toDigits10_isDigit hmem
  simp at hdig

private theorem string_append_cancel_left {a s t : String}
    (h : a ++ s = a ++ t) : s = t := by
  apply String.ext
  simpa [String.toList_append] using congrArg String.toList h

theorem identV_ne_extTok tag (i d : Nat) : identV tag i ≠ extTok tag d := by
  intro h
  have h' : tag ++ ("_" ++ toString i) = tag ++ ("__tok_" ++ toString d) := by
    simpa [identV_string, extTok_string, String.append_assoc] using h
  have h2 : "_" ++ toString i = "__tok_" ++ toString d :=
    string_append_cancel_left h'
  have h2' : "_" ++ toString i = "_" ++ ("_tok_" ++ toString d) := by
    rw [show "__tok_" = "_" ++ "_tok_" from rfl, String.append_assoc] at h2
    exact h2
  have h3 : toString i = "_tok_" ++ toString d :=
    string_append_cancel_left h2'
  have hhead : (toString i).toList.head? = some '_' := by
    simp [h3, String.toList_append]
  exact toString_nat_head_ne_underscore i hhead

theorem identV_ne_extOk tag (i d : Nat) : identV tag i ≠ extOk tag d := by
  intro h
  have h' : tag ++ ("_" ++ toString i) = tag ++ ("__ok_" ++ toString d) := by
    simpa [identV_string, extOk_string, String.append_assoc] using h
  have h2 : "_" ++ toString i = "__ok_" ++ toString d :=
    string_append_cancel_left h'
  have h2' : "_" ++ toString i = "_" ++ ("_ok_" ++ toString d) := by
    rw [show "__ok_" = "_" ++ "_ok_" from rfl, String.append_assoc] at h2
    exact h2
  have h3 : toString i = "_ok_" ++ toString d :=
    string_append_cancel_left h2'
  have hhead : (toString i).toList.head? = some '_' := by
    simp [h3, String.toList_append]
  exact toString_nat_head_ne_underscore i hhead

end Lsc.Compiler

