import Lsc.Compiler.Proof.CallBwd
import Lsc.Compiler.Proof.DispatchExtProof
import Lsc.Compiler.Proof.ExtOracleProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
S2 Yul progress: `CallsTotal` ⇒ a halted `Run` of the compiled runtime exists.
Call-free cores reuse S1 `core_sim` + lift. Call blocks use `call_prefix_fwd` /
`eval_call_fwd` / `call_suffix_fwd`. Dispatcher wrapper is the S1
guard/selector/`switch` lifted to `yulD`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-! ## FunEnv lift of empty scopes -/

theorem funEnvCast_replicate_nil (calls : ExternalCalls) :
    ∀ n, funEnvCast (evm_op_eq calls .none .none)
        (List.replicate n ([] : FScope evm)) =
      (List.replicate n ([] : FScope (yulD calls)))
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, funEnvCast_cons]
    rw [funEnvCast_replicate_nil calls n]
    rfl

theorem replicate_succ_nil {α} (n : Nat) :
    List.replicate (n + 1) ([] : List α) = [] :: List.replicate n [] :=
  List.replicate_succ ..

theorem execStmts_lift_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} {ss : YBlock}
    {V' : VEnv evm} {st' : EvmState} {o : Outcome}
    (h : ExecStmts evm (List.replicate n []) V st ss V' st' o) :
    ExecStmts (yulD calls) (List.replicate n []) V st ss V' st' o := by
  have hL := execStmts_lift_open (calls := calls) h
  rwa [funEnvCast_replicate_nil] at hL

theorem evalExpr_lift_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} {e : YExpr} {r : EResult evm}
    (h : EvalExpr evm (List.replicate n []) V st e r) :
    EvalExpr (yulD calls) (List.replicate n []) V st e
      (eresCast calls .none .none r) := by
  have hL := evalExpr_lift (calls := calls) .none .none h
  rwa [funEnvCast_replicate_nil] at hL

theorem exec_block_halt_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {body : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState}
    (hh : hoist (yulD calls) body = [])
    (h : ExecStmts (yulD calls) ([] :: funs) V st body V' st' .halt) :
    ExecStmt (yulD calls) funs V st (.block body) (restore V V') st' .halt :=
  Step.block (by rwa [hh])

theorem exec_block_ok_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {body : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState}
    (hh : hoist (yulD calls) body = [])
    (h : ExecStmts (yulD calls) ([] :: funs) V st body V' st' .normal) :
    ExecStmt (yulD calls) funs V st (.block body) (restore V V') st' .normal :=
  Step.block (by rwa [hh])

/-! ## CALL / STATICCALL expression -/

theorem eval_call_args_fwd {calls : ExternalCalls}
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st)) :
    EvalArgs (yulD calls) funs V st
      [lit gas, targetE, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]
      (.vals [BitVec.ofNat 256 gas, target, 0,
        BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 insize,
        BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 32] st) :=
  Step.argsCons
    (Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons
            (Step.argsCons
              (Step.argsCons Step.argsNil Step.lit) Step.lit)
            Step.lit)
          Step.lit)
        Step.lit)
      ht)
    Step.lit

theorem eval_staticcall_args_fwd {calls : ExternalCalls}
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st)) :
    EvalArgs (yulD calls) funs V st
      [lit gas, targetE, lit abiPtr, lit insize, lit abiPtr, lit 32]
      (.vals [BitVec.ofNat 256 gas, target,
        BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 insize,
        BitVec.ofNat 256 abiPtr, BitVec.ofNat 256 32] st) :=
  Step.argsCons
    (Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons
            (Step.argsCons Step.argsNil Step.lit) Step.lit)
          Step.lit)
        Step.lit)
      ht)
    Step.lit

theorem eval_call_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st))
    (hstatic : st.env.static = false) :
    ∃ resp : CallResponse,
      EvalExpr (yulD calls) funs V st
        (bop YulSemantics.EVM.Op.call
          [lit gas, targetE, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])
        (.vals [resp.flag]
          (finishCall .call st resp
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat)) ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
        st resp := by
  let req : CallRequest :=
    { kind := .call
      gas := BitVec.ofNat 256 gas
      target := target
      value := 0
      input := readBytes st.memory
        (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
  obtain ⟨resp, hCall⟩ := htot req st
  refine ⟨resp, ?_, hCall⟩
  have hargs := eval_call_args_fwd (calls := calls) (st := st) funs ht
    (gas := gas) (insize := insize)
  refine Step.builtinOk hargs ?_
  dsimp [yulD, evmWithExternal]
  simp only [builtinWithExternal, hstatic, Bool.false_and, ↓reduceIte]
  exact ⟨resp, hCall, rfl⟩

theorem eval_staticcall_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st)) :
    ∃ resp : CallResponse,
      EvalExpr (yulD calls) funs V st
        (bop YulSemantics.EVM.Op.staticcall
          [lit gas, targetE, lit abiPtr, lit insize, lit abiPtr, lit 32])
        (.vals [resp.flag]
          (finishCall .staticcall st resp
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat)) ∧
      calls.Call
        { kind := .staticcall
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
        st resp := by
  let req : CallRequest :=
    { kind := .staticcall
      gas := BitVec.ofNat 256 gas
      target := target
      value := 0
      input := readBytes st.memory
        (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
  obtain ⟨resp, hCall⟩ := htot req st
  refine ⟨resp, ?_, hCall⟩
  have hargs := eval_staticcall_args_fwd (calls := calls) (st := st) funs ht
    (gas := gas) (insize := insize)
  refine Step.builtinOk hargs ?_
  dsimp [yulD, evmWithExternal]
  simp only [builtinWithExternal]
  exact ⟨resp, hCall, rfl⟩

theorem exec_let_call_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {ok : YIdent} {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st))
    (hstatic : st.env.static = false) :
    ∃ resp : CallResponse,
      ExecStmt (yulD calls) funs V st
        (.letDecl [ok] (some (bop YulSemantics.EVM.Op.call
          [lit gas, targetE, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])))
        ((ok, resp.flag) :: V)
        (finishCall .call st resp
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat)
        .normal ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
        st resp := by
  obtain ⟨resp, he, hCall⟩ := eval_call_fwd htot funs ht hstatic (gas := gas) (insize := insize)
  exact ⟨resp, Step.letVal he rfl, hCall⟩

theorem exec_let_staticcall_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {ok : YIdent} {targetE : YExpr} {target : U256} {gas insize : Nat}
    (ht : EvalExpr (yulD calls) funs V st targetE (.vals [target] st)) :
    ∃ resp : CallResponse,
      ExecStmt (yulD calls) funs V st
        (.letDecl [ok] (some (bop YulSemantics.EVM.Op.staticcall
          [lit gas, targetE, lit abiPtr, lit insize, lit abiPtr, lit 32])))
        ((ok, resp.flag) :: V)
        (finishCall .staticcall st resp
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat
          (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 32).toNat)
        .normal ∧
      calls.Call
        { kind := .staticcall
          gas := BitVec.ofNat 256 gas
          target := target
          value := 0
          input := readBytes st.memory
            (BitVec.ofNat 256 abiPtr).toNat (BitVec.ofNat 256 insize).toNat }
        st resp := by
  obtain ⟨resp, he, hCall⟩ := eval_staticcall_fwd htot funs ht (gas := gas) (insize := insize)
  exact ⟨resp, Step.letVal he rfl, hCall⟩

/-! ## Guard / selector on `yulD` -/

theorem guardLt_halt_nils {calls : ExternalCalls} {n m : Nat}
    {V : VEnv evm} {st : EvmState}
    (hcd : st.env.calldata.length < wordBound) (hn : n < wordBound)
    (hlt : st.env.calldata.length < n) :
    ExecStmts (yulD calls) (List.replicate m []) V st (emitGuardLt {} n).stmts V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt :=
  execStmts_lift_nils (guardLt_halt (funs := List.replicate m []) hcd hn hlt)

theorem guardLt_ok_nils {calls : ExternalCalls} {n m : Nat}
    {V : VEnv evm} {st : EvmState}
    (hcd : st.env.calldata.length < wordBound) (hn : n < wordBound)
    (hge : n ≤ st.env.calldata.length) :
    ExecStmts (yulD calls) (List.replicate m []) V st (emitGuardLt {} n).stmts V st .normal :=
  execStmts_lift_nils (guardLt_ok (funs := List.replicate m []) hcd hn hge)

theorem eval_selector_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} :
    EvalExpr (yulD calls) (List.replicate n []) V st
      (bop EVM.Op.shr [lit 224, bop EVM.Op.calldataload [lit 0]])
      (.vals [BitVec.ofNat 256 (calldataSelector st.env.calldata)] st) := by
  simpa using evalExpr_lift_nils (calls := calls) (n := n)
    (eval_selector (funs := List.replicate n []) V st)

theorem revert00_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} :
    ExecStmts (yulD calls) (List.replicate n []) V st [revert00] V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt :=
  execStmts_lift_nils (revert00_exec (List.replicate n []) V st)

/-! ## Call-free core progress -/

theorem core_progress_callFree {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx haltUnit} (hhalt : haltUnit = true)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {calls : ExternalCalls} {t} (core : Core t) (hM1 : CallFree core)
    {n : Nat} {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState}
    (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    {clearLock : Bool} {e' : Emit}
    (hem : emitCore tag c {} env.length haltUnit core clearLock = some e') :
    ∃ V' st', ExecStmts (yulD calls) (List.replicate n []) V st e'.stmts V' st' .halt := by
  have hS1 :=
    core_sim (tag := tag) (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) hhalt hΓ hκ hlen core hM1
      (funs := List.replicate n []) hwf hn hinv hem
  cases hrun : Tx.run (Core.denote Γ core env) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hS1
    obtain ⟨V', st', hexec, _, _⟩ := hS1
    exact ⟨V', st', execStmts_lift_nils hexec⟩
  | error e =>
    simp only [hrun, except_error_prod] at hS1
    obtain ⟨V', st', _, hexec, _, _⟩ := hS1
    exact ⟨V', st', execStmts_lift_nils hexec⟩

theorem emitCore_seq_split {c : ContractDef} {halt : Bool} {clearLock : Bool} {t : RetTy}
    {s : Lsc.Stmt} {k : Core t} {e' : Emit} {d : Nat}
    (hem : emitCore tag c {} d halt (.seq s k) clearLock = some e') :
    ∃ e0, emitCore tag c {} d halt k clearLock = some e0 ∧
      e'.stmts = (emitStmt tag c {} d s).stmts ++ e0.stmts :=
  emitCore_prefix tag hem

/-! ## `Op.call` / `Op.view` / `Stmt.call` / `Stmt.view` progress -/

theorem outcome_halt_or_normal_of_suffix {ok : U256} {ret : AbiRet}
    {st : EvmState} {checkOk : Bool} {o : Outcome}
    (hok : suffixOk ok ret st checkOk → o = .normal)
    (hfail : ¬ suffixOk ok ret st checkOk → o = .halt) :
    o = .halt ∨ o = .normal := by
  by_cases hS : suffixOk ok ret st checkOk
  · exact .inr (hok hS)
  · exact .inl (hfail hS)

theorem hn1_of_base {env : List Nat} :
    toVEnv tag env = (identV tag env.length, (0 : U256)) :: toVEnv tag env →
      identsNodup tag (env.length + 1) = true := fun h => False.elim (by
  have := congrArg List.length h
  simp [toVEnv, List.length_map, List.length_zip, List.length_range] at this)

theorem eval_atomE_nils {calls : ExternalCalls} {n : Nat}
    {env : List Nat} {V : VEnv evm} {st : EvmState} {a : Atom}
    (hok : localsOK tag env V) :
    EvalExpr (yulD calls) (List.replicate n []) V st (atomE tag env.length a)
      (.vals [BitVec.ofNat 256 (a.eval env)] st) := by
  simpa using evalExpr_lift_nils (calls := calls) (n := n)
    (eval_atom_pre tag (List.replicate n []) st hok a)

theorem op_call_progress {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {n : Nat} {V : VEnv evm} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true)
    (hn1 : identsNodup tag (env.length + 1) = true) :
    ∃ V' st' out,
      ExecStmts (yulD (toCalls o)) (List.replicate n []) V st
        ((emitLetOp tag c {} env.length (.call target sel args ret)).getD {}).stmts
        V' st' out ∧
      (out = .halt ∨
        (out = .normal ∧ ∃ v, Inv tag Γ c κ ctx w (v :: env) V' st')) := by
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  have htot := Proof.toCalls_total o
  let d := env.length
  let funsN : FunEnv (yulD (toCalls o)) := List.replicate n []
  let funsN1 : FunEnv (yulD (toCalls o)) := List.replicate (n + 1) []
  have hlet0 : ExecStmt (yulD (toCalls o)) funsN V st
      (.letDecl [identV tag d] (some (lit 0)))
      ((identV tag d, (0 : U256)) :: V) st .normal :=
    Step.letVal (D := yulD (toCalls o)) Step.lit rfl
  let pre : VEnv evm := (identV tag d, (0 : U256)) :: V
  have hokPre : localsOK tag env pre :=
    localsOK_identV_front (tag := tag) 0 hn1 hinv.venv
  obtain ⟨st1, hpre, hpack, hMO, hstatic, _, _⟩ :=
    call_prefix_fwd tag (funs := List.replicate (n + 1) []) sel args
      hokPre hctx henv hn3 hvals hsel
  have hpre' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hpre
  have htgt := eval_atomE_nils tag (calls := toCalls o) (n := n + 1)
    hokPre (a := target) (st := st1)
  obtain ⟨resp, hlet, hCall⟩ :=
    exec_let_call_fwd (calls := toCalls o) htot funsN1 htgt hstatic
      (ok := extOk tag d) (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  let st2 := finishCall .call st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk tag d, resp.flag) :: pre
  have hgetOk : VEnv.get V2 (extOk tag d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd tag (funs := List.replicate (n + 1) []) (d := d)
      (ok := resp.flag) (ret := ret) (isView := false)
      (assign := some (identV tag d)) hgetOk
  have hsuf' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD (toCalls o)) funsN1 pre st
      (emitExtCallBody tag d target sel args ret false (some (identV tag d)))
      V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD (toCalls o)) funsN1 pre st1
        (callLetOk tag d target args false) V2 st2 .normal := by
      simpa [callLetOk, emitExtCallOp, emitCallGas, V2, st2, d, pre] using hlet
    have hletS : ExecStmts (yulD (toCalls o)) funsN1 pre st1
        [callLetOk tag d target args false] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD (toCalls o)) funsN1 pre st
          (callPrefix tag d sel args ++ [callLetOk tag d target args false])
          V2 st2 .normal :=
      execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    false (some (identV tag d))
  have hemit :
      ((emitLetOp tag c {} env.length (.call target sel args ret)).getD {}).stmts =
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts := rfl
  rw [hemit, emitLetOp_call_stmts]
  rcases outcome_halt_or_normal_of_suffix
      (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    refine ⟨restore pre V3, st3, .halt, ?_, .inl rfl⟩
    exact Step.seqCons hlet0 (Step.seqStop hblk halt_ne_normal)
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag ret st2 (!skipOkGuard false ret) := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, _, hVeq⟩ := hokP hS
    have hflag : resp.flag ≠ 0 := by
      cases hS.1 with
      | inl h => simp [skipOkGuard] at h
      | inr h => exact h
    have hsucc : resp.success = true := (flag_ne_zero_iff resp).mp hflag
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have haddr : st1.env.address = BitVec.ofNat 256 ctx.self := ctxRel_address hctx1
    have hreq :
        ({ kind := .call
           gas := BitVec.ofNat 256 extCallGas
           target := BitVec.ofNat 256 (target.eval env)
           value := 0
           input := readBytes st1.memory abiPtr (4 + 32 * args.length) } : CallRequest) =
          mkCallReq .call (target.eval env) sel (args.map (·.eval env)) := by
      simp [mkCallReq, hpack, List.flatMap_map]
    have hresp : resp = toCall o (mkCallReq .call (target.eval env) sel
        (args.map (·.eval env))) st1 := by
      have hY := (toCalls_call o _ st1 resp).mp hCall
      rw [hreq] at hY
      exact hY
    have ⟨hNoI, _⟩ := hNR
    have hni := hNoI
      (mkCallReq .call (target.eval env) sel (args.map (·.eval env))) st1 haddr
    have hni' : resp.world.storage = st1.storage ∧
        resp.world.transient = st1.transient ∧
        (∀ l ∈ resp.world.logs, l.address ≠ st1.env.address) := by
      simpa [hresp] using hni
    have hR2 : R c Γ κ w st2 := R_finishCall_success hR1 hsucc hni'.1 hni'.2.2
    have hctx2 : ctxRel ctx st2 :=
      ctxRel_finishCall hctx1 .call resp abiPtr (4 + 32 * args.length) abiPtr 32
    have hR3 : R c Γ κ w st3 := R_memOnly hR2 hMO2
    have hctx3 : ctxRel ctx st3 := ctxRel_memOnly hctx2 hMO2
    let vU : U256 := suffixVal ret st2
    have hne : extOk tag d ≠ identV tag d := (identV_ne_extOk tag d d).symm
    have hset : VEnv.set V2 (identV tag d) vU =
        (extOk tag d, resp.flag) :: (identV tag d, vU) :: V := by
      rw [VEnv.set_cons_ne hne]
      simp [VEnv.set, pre]
    have hV3 : V3 = (extOk tag d, resp.flag) :: (identV tag d, vU) :: V := by
      rw [hVeq]; exact hset
    have hrest : restore pre V3 =
        (identV tag d, BitVec.ofNat 256 vU.toNat) :: V := by
      rw [hV3]; exact (restore_call_assign).trans (by rw [ofNat_toNat_u256])
    refine ⟨restore pre V3, st3, .normal, ?_, .inr ⟨rfl, vU.toNat, ?_⟩⟩
    · exact Step.seqCons hlet0 (Step.seqCons hblk Step.seqNil)
    · exact hrest ▸
        ⟨localsOK_cons (tag := tag) vU.toNat hn1 hinv.venv,
          envWF_cons (u256_lt_word vU) henv, hR3, hctx3⟩

theorem op_view_progress {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {n : Nat} {V : VEnv evm} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true)
    (hn1 : identsNodup tag (env.length + 1) = true) :
    ∃ V' st' out,
      ExecStmts (yulD (toCalls o)) (List.replicate n []) V st
        ((emitLetOp tag c {} env.length (.view target sel args ret)).getD {}).stmts
        V' st' out ∧
      (out = .halt ∨
        (out = .normal ∧ ∃ v, Inv tag Γ c κ ctx w (v :: env) V' st')) := by
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  have htot := Proof.toCalls_total o
  let d := env.length
  let funsN : FunEnv (yulD (toCalls o)) := List.replicate n []
  let funsN1 : FunEnv (yulD (toCalls o)) := List.replicate (n + 1) []
  have hlet0 : ExecStmt (yulD (toCalls o)) funsN V st
      (.letDecl [identV tag d] (some (lit 0)))
      ((identV tag d, (0 : U256)) :: V) st .normal :=
    Step.letVal (D := yulD (toCalls o)) Step.lit rfl
  let pre : VEnv evm := (identV tag d, (0 : U256)) :: V
  have hokPre : localsOK tag env pre :=
    localsOK_identV_front (tag := tag) 0 hn1 hinv.venv
  obtain ⟨st1, hpre, _, hMO, _, _, _⟩ :=
    call_prefix_fwd tag (funs := List.replicate (n + 1) []) sel args
      hokPre hctx henv hn3 hvals hsel
  have hpre' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hpre
  have htgt := eval_atomE_nils tag (calls := toCalls o) (n := n + 1)
    hokPre (a := target) (st := st1)
  obtain ⟨resp, hlet, _⟩ :=
    exec_let_staticcall_fwd (calls := toCalls o) htot funsN1 htgt
      (ok := extOk tag d) (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  let st2 := finishCall .staticcall st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk tag d, resp.flag) :: pre
  have hgetOk : VEnv.get V2 (extOk tag d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd tag (funs := List.replicate (n + 1) []) (d := d)
      (ok := resp.flag) (ret := ret) (isView := true)
      (assign := some (identV tag d)) hgetOk
  have hsuf' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD (toCalls o)) funsN1 pre st
      (emitExtCallBody tag d target sel args ret true (some (identV tag d)))
      V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD (toCalls o)) funsN1 pre st1
        (callLetOk tag d target args true) V2 st2 .normal := by
      simpa [callLetOk, emitExtCallOp, emitCallGas, V2, st2, d, pre] using hlet
    have hletS : ExecStmts (yulD (toCalls o)) funsN1 pre st1
        [callLetOk tag d target args true] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD (toCalls o)) funsN1 pre st
          (callPrefix tag d sel args ++ [callLetOk tag d target args true])
          V2 st2 .normal :=
      execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    true (some (identV tag d))
  have hemit :
      ((emitLetOp tag c {} env.length (.view target sel args ret)).getD {}).stmts =
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts := rfl
  rw [hemit, emitLetOp_view_stmts]
  rcases outcome_halt_or_normal_of_suffix
      (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    refine ⟨restore pre V3, st3, .halt, ?_, .inl rfl⟩
    exact Step.seqCons hlet0 (Step.seqStop hblk halt_ne_normal)
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag ret st2 (!skipOkGuard true ret) := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, _, hVeq⟩ := hokP hS
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have hR2 : R c Γ κ w st2 := R_finishCall_static hR1
    have hctx2 : ctxRel ctx st2 :=
      ctxRel_finishCall hctx1 .staticcall resp abiPtr (4 + 32 * args.length) abiPtr 32
    have hR3 : R c Γ κ w st3 := R_memOnly hR2 hMO2
    have hctx3 : ctxRel ctx st3 := ctxRel_memOnly hctx2 hMO2
    let vU : U256 := suffixVal ret st2
    have hne : extOk tag d ≠ identV tag d := (identV_ne_extOk tag d d).symm
    have hset : VEnv.set V2 (identV tag d) vU =
        (extOk tag d, resp.flag) :: (identV tag d, vU) :: V := by
      rw [VEnv.set_cons_ne hne]
      simp [VEnv.set, pre]
    have hV3 : V3 = (extOk tag d, resp.flag) :: (identV tag d, vU) :: V := by
      rw [hVeq]; exact hset
    have hrest : restore pre V3 =
        (identV tag d, BitVec.ofNat 256 vU.toNat) :: V := by
      rw [hV3]; exact (restore_call_assign).trans (by rw [ofNat_toNat_u256])
    refine ⟨restore pre V3, st3, .normal, ?_, .inr ⟨rfl, vU.toNat, ?_⟩⟩
    · exact Step.seqCons hlet0 (Step.seqCons hblk Step.seqNil)
    · exact hrest ▸
        ⟨localsOK_cons (tag := tag) vU.toNat hn1 hinv.venv,
          envWF_cons (u256_lt_word vU) henv, hR3, hctx3⟩

theorem stmt_call_progress {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {n : Nat} {V : VEnv evm} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true) :
    ∃ V' st' out,
      ExecStmts (yulD (toCalls o)) (List.replicate n []) V st
        (emitStmt tag c {} env.length (.call target sel args ret)).stmts V' st' out ∧
      (out = .halt ∨
        (out = .normal ∧ Inv tag Γ c κ ctx w env V' st')) := by
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  have htot := Proof.toCalls_total o
  let d := env.length
  let funsN : FunEnv (yulD (toCalls o)) := List.replicate n []
  let funsN1 : FunEnv (yulD (toCalls o)) := List.replicate (n + 1) []
  let pre : VEnv evm := V
  obtain ⟨st1, hpre, hpack, hMO, hstatic, _, _⟩ :=
    call_prefix_fwd tag (funs := List.replicate (n + 1) []) sel args
      hinv.venv hctx henv hn3 hvals hsel
  have hpre' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hpre
  have htgt := eval_atomE_nils tag (calls := toCalls o) (n := n + 1)
    hinv.venv (a := target) (st := st1)
  obtain ⟨resp, hlet, hCall⟩ :=
    exec_let_call_fwd (calls := toCalls o) htot funsN1 htgt hstatic
      (ok := extOk tag d) (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  let st2 := finishCall .call st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk tag d, resp.flag) :: pre
  have hgetOk : VEnv.get V2 (extOk tag d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd tag (funs := List.replicate (n + 1) []) (d := d)
      (ok := resp.flag) (ret := ret) (isView := false) (assign := none) hgetOk
  have hsuf' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD (toCalls o)) funsN1 pre st
      (emitExtCallBody tag d target sel args ret false none) V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD (toCalls o)) funsN1 pre st1
        (callLetOk tag d target args false) V2 st2 .normal := by
      simpa [callLetOk, emitExtCallOp, emitCallGas, V2, st2, d, pre] using hlet
    have hletS : ExecStmts (yulD (toCalls o)) funsN1 pre st1
        [callLetOk tag d target args false] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD (toCalls o)) funsN1 pre st
          (callPrefix tag d sel args ++ [callLetOk tag d target args false])
          V2 st2 .normal :=
      execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    false none
  rw [emitStmt_call_stmts]
  rcases outcome_halt_or_normal_of_suffix
      (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    exact ⟨restore pre V3, st3, .halt, Step.seqStop hblk halt_ne_normal, .inl rfl⟩
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag ret st2 (!skipOkGuard false ret) := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, _, hVeq⟩ := hokP hS
    have hflag : resp.flag ≠ 0 := by
      cases hS.1 with
      | inl h => simp [skipOkGuard] at h
      | inr h => exact h
    have hsucc : resp.success = true := (flag_ne_zero_iff resp).mp hflag
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have haddr : st1.env.address = BitVec.ofNat 256 ctx.self := ctxRel_address hctx1
    have hreq :
        ({ kind := .call
           gas := BitVec.ofNat 256 extCallGas
           target := BitVec.ofNat 256 (target.eval env)
           value := 0
           input := readBytes st1.memory abiPtr (4 + 32 * args.length) } : CallRequest) =
          mkCallReq .call (target.eval env) sel (args.map (·.eval env)) := by
      simp [mkCallReq, hpack, List.flatMap_map]
    have hresp : resp = toCall o (mkCallReq .call (target.eval env) sel
        (args.map (·.eval env))) st1 := by
      have hY := (toCalls_call o _ st1 resp).mp hCall
      rw [hreq] at hY
      exact hY
    have ⟨hNoI, _⟩ := hNR
    have hni := hNoI
      (mkCallReq .call (target.eval env) sel (args.map (·.eval env))) st1 haddr
    have hni' : resp.world.storage = st1.storage ∧
        resp.world.transient = st1.transient ∧
        (∀ l ∈ resp.world.logs, l.address ≠ st1.env.address) := by
      simpa [hresp] using hni
    have hR3 : R c Γ κ w st3 :=
      R_memOnly (R_finishCall_success hR1 hsucc hni'.1 hni'.2.2) hMO2
    have hctx3 : ctxRel ctx st3 :=
      ctxRel_memOnly
        (ctxRel_finishCall hctx1 .call resp abiPtr (4 + 32 * args.length) abiPtr 32)
        hMO2
    have hV3 : V3 = V2 := by simpa using hVeq
    have hrest : restore pre V3 = V := by
      rw [hV3]; exact restore_drop1
    refine ⟨restore pre V3, st3, .normal, Step.seqCons hblk Step.seqNil,
      .inr ⟨rfl, ⟨hrest.symm ▸ hinv.venv, henv, hR3, hctx3⟩⟩⟩

theorem stmt_view_progress {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {n : Nat} {V : VEnv evm} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true) :
    ∃ V' st' out,
      ExecStmts (yulD (toCalls o)) (List.replicate n []) V st
        (emitStmt tag c {} env.length (.view target sel args ret)).stmts V' st' out ∧
      (out = .halt ∨
        (out = .normal ∧ Inv tag Γ c κ ctx w env V' st')) := by
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  have htot := Proof.toCalls_total o
  let d := env.length
  let funsN : FunEnv (yulD (toCalls o)) := List.replicate n []
  let funsN1 : FunEnv (yulD (toCalls o)) := List.replicate (n + 1) []
  let pre : VEnv evm := V
  obtain ⟨st1, hpre, _, hMO, _, _, _⟩ :=
    call_prefix_fwd tag (funs := List.replicate (n + 1) []) sel args
      hinv.venv hctx henv hn3 hvals hsel
  have hpre' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hpre
  have htgt := eval_atomE_nils tag (calls := toCalls o) (n := n + 1)
    hinv.venv (a := target) (st := st1)
  obtain ⟨resp, hlet, _⟩ :=
    exec_let_staticcall_fwd (calls := toCalls o) htot funsN1 htgt
      (ok := extOk tag d) (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  let st2 := finishCall .staticcall st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk tag d, resp.flag) :: pre
  have hgetOk : VEnv.get V2 (extOk tag d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd tag (funs := List.replicate (n + 1) []) (d := d)
      (ok := resp.flag) (ret := ret) (isView := true) (assign := none) hgetOk
  have hsuf' := execStmts_lift_nils (calls := toCalls o) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD (toCalls o)) funsN1 pre st
      (emitExtCallBody tag d target sel args ret true none) V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD (toCalls o)) funsN1 pre st1
        (callLetOk tag d target args true) V2 st2 .normal := by
      simpa [callLetOk, emitExtCallOp, emitCallGas, V2, st2, d, pre] using hlet
    have hletS : ExecStmts (yulD (toCalls o)) funsN1 pre st1
        [callLetOk tag d target args true] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD (toCalls o)) funsN1 pre st
          (callPrefix tag d sel args ++ [callLetOk tag d target args true])
          V2 st2 .normal :=
      execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    true none
  rw [emitStmt_view_stmts]
  rcases outcome_halt_or_normal_of_suffix
      (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    exact ⟨restore pre V3, st3, .halt, Step.seqStop hblk halt_ne_normal, .inl rfl⟩
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag ret st2 (!skipOkGuard true ret) := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, _, hVeq⟩ := hokP hS
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have hR3 : R c Γ κ w st3 :=
      R_memOnly (R_finishCall_static hR1) hMO2
    have hctx3 : ctxRel ctx st3 :=
      ctxRel_memOnly
        (ctxRel_finishCall hctx1 .staticcall resp abiPtr
          (4 + 32 * args.length) abiPtr 32)
        hMO2
    have hV3 : V3 = V2 := by simpa using hVeq
    have hrest : restore pre V3 = V := by
      rw [hV3]; exact restore_drop1
    refine ⟨restore pre V3, st3, .normal, Step.seqCons hblk Step.seqNil,
      .inr ⟨rfl, ⟨hrest.symm ▸ hinv.venv, henv, hR3, hctx3⟩⟩⟩

/-! ## Memoryguard prefix on `yulD` -/

theorem exec_memoryGuardErased_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} :
    ExecStmt (yulD calls) (List.replicate n []) V st memoryGuardErased V
      (stAfterGuard st) .normal := by
  have h := execStmt_lift (calls := calls) .none .none
    (exec_memoryGuardErased (List.replicate n []) V st)
  rwa [funEnvCast_replicate_nil] at h

theorem exec_lockCheck_ok_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} (h : LockFree st) :
    ExecStmt (yulD calls) (List.replicate n []) V st lockCheckStmt V st .normal := by
  have h' := execStmt_lift (calls := calls) .none .none
    (exec_lockCheck_ok (List.replicate n []) V st h)
  rwa [funEnvCast_replicate_nil] at h'

theorem exec_lockCheck_halt_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} (h : ¬ LockFree st) :
    ExecStmt (yulD calls) (List.replicate n []) V st lockCheckStmt V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt := by
  have h' := execStmt_lift (calls := calls) .none .none
    (exec_lockCheck_halt (List.replicate n []) V st h)
  rwa [funEnvCast_replicate_nil] at h'

theorem exec_valueCheckPrefix_ok_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} {f : FnDef}
    (h : f.payable = true ∨ st.env.callvalue = 0) :
    ExecStmts (yulD calls) (List.replicate n []) V st (valueCheckPrefix f) V st
      .normal :=
  execStmts_lift_nils (exec_valueCheckPrefix_ok h)

theorem exec_valueCheckPrefix_halt_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} {f : FnDef}
    (hp : f.payable = false) (hv : st.env.callvalue ≠ 0) :
    ExecStmts (yulD calls) (List.replicate n []) V st (valueCheckPrefix f) V
      { touchMemory st 0 0 with halted := some (.revert, []) } .halt :=
  execStmts_lift_nils (exec_valueCheckPrefix_halt hp hv)

theorem exec_lockSetStmt_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} (hstatic : st.env.static = false) :
    ExecStmt (yulD calls) (List.replicate n []) V st lockSetStmt V
      (stTstore st (BitVec.ofNat 256 reentrancyLockSlot) 1) .normal := by
  have h' := execStmt_lift (calls := calls) .none .none
    (exec_lockSetStmt (List.replicate n []) V st hstatic)
  rwa [funEnvCast_replicate_nil] at h'

theorem exec_lockClearStmt_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} (hstatic : st.env.static = false) :
    ExecStmt (yulD calls) (List.replicate n []) V st lockClearStmt V
      (stTstore st (BitVec.ofNat 256 reentrancyLockSlot) 0) .normal := by
  have h' := execStmt_lift (calls := calls) .none .none
    (exec_lockClearStmt (List.replicate n []) V st hstatic)
  rwa [funEnvCast_replicate_nil] at h'

theorem execStmts_maybe_lockClear_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} {rest : YBlock}
    {V' : VEnv evm} {st' : EvmState} {o : Outcome}
    (clearLock : Bool) (hstatic : st.env.static = false)
    (h : ExecStmts (yulD calls) (List.replicate n []) V
      (stAfterLockClear clearLock st) rest V' st' o) :
    ExecStmts (yulD calls) (List.replicate n []) V st
      ((if clearLock then [lockClearStmt] else []) ++ rest) V' st' o := by
  cases clearLock with
  | false => simpa [stAfterLockClear] using h
  | true =>
    simpa [stAfterLockClear] using
      Step.seqCons (exec_lockClearStmt_nils (calls := calls) (n := n) hstatic) h

theorem exec_cons_normal_open {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {s : YulSemantics.Stmt YOp} {V1 : VEnv (yulD calls)} {st1 : EvmState}
    {rest : YBlock} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h1 : ExecStmt (yulD calls) funs V st s V1 st1 .normal)
    (h2 : ExecStmts (yulD calls) funs V1 st1 rest V' st' o) :
    ExecStmts (yulD calls) funs V st (s :: rest) V' st' o :=
  Step.seqCons h1 h2

theorem hoist_erased_runtime_open (calls : ExternalCalls) (guard : YBlock)
    (sel : YExpr) (cases : List (YulSemantics.Literal × YBlock)) :
    hoist (yulD calls) (memoryGuardErased ::
      lockCheckStmt ::
      [.block guard, .switch sel cases (some [revert00])]) = [] :=
  hoist_yulD_of_evm (hoist_erased_runtime guard sel cases)

end Lsc.Compiler
