import Lsc.Compiler.Proof.CallBwd
import Lsc.Compiler.Proof.DispatchExtProof

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

/-! ## CALL expression -/

theorem eval_call_args_fwd {calls : ExternalCalls}
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {tok : YIdent} {target : U256} {gas insize : Nat}
    (hget : VEnv.get V tok = some target) :
    EvalArgs (yulD calls) funs V st
      [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]
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
      (Step.var hget))
    Step.lit

theorem eval_call_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {tok : YIdent} {target : U256} {gas insize : Nat}
    (hget : VEnv.get V tok = some target)
    (hstatic : st.env.static = false) :
    ∃ resp : CallResponse,
      EvalExpr (yulD calls) funs V st
        (bop YulSemantics.EVM.Op.call
          [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])
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
  have hargs :=
    eval_call_args_fwd (calls := calls) (st := st) funs hget (gas := gas) (insize := insize)
  refine Step.builtinOk hargs ?_
  dsimp [yulD, evmWithExternal]
  simp only [builtinWithExternal, hstatic, Bool.false_and, ↓reduceIte]
  exact ⟨resp, hCall, rfl⟩

theorem exec_let_call_fwd {calls : ExternalCalls} (htot : CallsTotal calls)
    (funs : FunEnv (yulD calls)) {V : VEnv (yulD calls)} {st : EvmState}
    {tok ok : YIdent} {target : U256} {gas insize : Nat}
    (hget : VEnv.get V tok = some target)
    (hstatic : st.env.static = false) :
    ∃ resp : CallResponse,
      ExecStmt (yulD calls) funs V st
        (.letDecl [ok] (some (bop YulSemantics.EVM.Op.call
          [lit gas, var tok, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32])))
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
  obtain ⟨resp, he, hCall⟩ := eval_call_fwd htot funs hget hstatic (gas := gas) (insize := insize)
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
    (hn : identsNodup (env.length + coreExtraDepth core) = true)
    (hinv : Inv Γ c κ ctx w env V st)
    {e' : Emit} (hem : emitCore c {} env.length haltUnit core = some e') :
    ∃ V' st', ExecStmts (yulD calls) (List.replicate n []) V st e'.stmts V' st' .halt := by
  have hS1 :=
    core_sim (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) hhalt hΓ hκ hlen core hM1
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

theorem emitCore_seq_split {c : ContractDef} {halt : Bool} {t : RetTy}
    {s : Lsc.Stmt} {k : Core t} {e' : Emit} {d : Nat}
    (hem : emitCore c {} d halt (.seq s k) = some e') :
    ∃ e0, emitCore c {} d halt k = some e0 ∧
      e'.stmts = (emitStmt c {} d s).stmts ++ e0.stmts :=
  emitCore_prefix hem

theorem u256_lt_word (v : U256) : v.toNat < wordBound := by
  simpa [wordBound] using v.isLt

theorem toVEnv_cons_u256 (v : U256) (env : List Nat) :
    toVEnv (v.toNat :: env) = (identV env.length, v) :: toVEnv env := by
  rw [toVEnv_cons]
  have h : (BitVec.ofNat 256 v.toNat).toNat = v.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  exact congrArg (fun v => (identV env.length, v) :: toVEnv env)
    (BitVec.eq_of_toNat_eq h)

/-! ## `Op.call` / `Stmt.call` progress -/

theorem outcome_halt_or_normal_of_suffix {ok : U256} {ret : AbiRet}
    {st : EvmState} {o : Outcome}
    (hok : suffixOk ok ret st → o = .normal)
    (hfail : ¬ suffixOk ok ret st → o = .halt) :
    o = .halt ∨ o = .normal := by
  by_cases hS : suffixOk ok ret st
  · exact .inr (hok hS)
  · exact .inl (hfail hS)

theorem op_call_progress {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} (htot : CallsTotal calls)
    {n : Nat} {st : EvmState}
    {b m : Nat} {args : List Atom} {meth : I.Method}
    (hinv : Inv Γ c κ ctx w env (toVEnv env) st)
    (hbd : BindWF c Γ bind b m meth)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hwfCall : callWF c b m args = true)
    (hn : identsNodup env.length = true)
    (hn1 : identsNodup (env.length + 1) = true) :
    ∃ V' st' o,
      ExecStmts (yulD calls) (List.replicate n []) (toVEnv env) st
        ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o ∧
      (o = .halt ∨
        (o = .normal ∧ ∃ v, V' = toVEnv (v :: env) ∧
          Inv Γ c κ ctx w (v :: env) V' st')) := by
  have ⟨hlenA, hvals⟩ := callWF_arity_of_BindWF hwfCall hbd
  have hn3 : args.length ≤ 3 := hlenA ▸ hbd.harity
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  let d := env.length
  let funsN : FunEnv (yulD calls) := List.replicate n []
  let funsN1 : FunEnv (yulD calls) := List.replicate (n + 1) []
  have hlet0 : ExecStmt (yulD calls) funsN (toVEnv env) st
      (.letDecl [identV d] (some (lit 0)))
      ((identV d, (0 : U256)) :: toVEnv env) st .normal :=
    Step.letVal (D := yulD calls) Step.lit rfl
  let pre : VEnv evm := (identV d, (0 : U256)) :: toVEnv env
  obtain ⟨st1, hpre, hpack, hMO, hstatic, hCW⟩ :=
    call_prefix_fwd (I := I) (funs := List.replicate (n + 1) []) pre hR hbd hctx henv
      (.inr rfl) hn (fun _ => hn1) hn3 hvals
  have hpre' := execStmts_lift_nils (calls := calls) (n := n + 1) hpre
  let tokv := BitVec.ofNat 256 (bind.addr w.self)
  let V1 : VEnv evm := (extTok d, tokv) :: pre
  have hget : VEnv.get V1 (extTok d) = some tokv := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨resp, hlet, hCall⟩ :=
    exec_let_call_fwd (calls := calls) htot funsN1 hget hstatic
      (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  let st2 := finishCall .call st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk d, resp.flag) :: V1
  have hgetOk : VEnv.get V2 (extOk d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd (funs := List.replicate (n + 1) []) (d := d) (ok := resp.flag)
      (ret := (bindingMethod c b m).2) (assign := some (identV d)) hgetOk
  have hsuf' := execStmts_lift_nils (calls := calls) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD calls) funsN1 pre st
      (emitExtCallBody c d b m args (some (identV d))) V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD calls) funsN1 V1 st1 (callLetOk d args) V2 st2 .normal := by
      simpa [callLetOk, V1, V2, st2] using hlet
    have hletS : ExecStmts (yulD calls) funsN1 V1 st1 [callLetOk d args] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD calls) funsN1 pre st
          (callPrefix c d b m args ++ [callLetOk d args]) V2 st2 .normal := by
      convert execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody (calls := calls) c d b m args (some (identV d))
  rw [emitLetOp_call_stmts]
  rcases outcome_halt_or_normal_of_suffix (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    refine ⟨restore pre V3, st3, .halt, ?_, .inl rfl⟩
    exact Step.seqCons hlet0 (Step.seqStop hblk halt_ne_normal)
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag (bindingMethod c b m).2 st2 := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, hVeq⟩ := hokP hS
    have hsucc : resp.success = true :=
      (flag_ne_zero_iff resp).mp hS.1
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have haddr : st1.env.address = BitVec.ofNat 256 ctx.self := hctx1.2.2.2.2.1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hni⟩ :=
      hconf _ st1 resp hCall rfl rfl haddr hsucc
    have hR2 : R c Γ κ w st2 := R_finishCall_success (α := α) hR1 hsucc hni
    have hctx2 : ctxRel ctx st2 :=
      ctxRel_finishCall hctx1 .call resp abiPtr (4 + 32 * args.length) abiPtr 32
    have hR3 : R c Γ κ w st3 := R_memOnly hR2 hMO2
    have hctx3 : ctxRel ctx st3 := ctxRel_memOnly hctx2 hMO2
    let vU : U256 := suffixVal (bindingMethod c b m).2 st2
    have h1 : extOk d ≠ identV d := (identV_ne_extOk d d).symm
    have h2 : extTok d ≠ identV d := (identV_ne_extTok d d).symm
    have hset : VEnv.set V2 (identV d) vU =
        (extOk d, resp.flag) :: (extTok d, tokv) :: (identV d, vU) :: toVEnv env := by
      rw [VEnv.set_cons_ne h1, VEnv.set_cons_ne h2]
      simp [VEnv.set, pre]
    have hV3 : V3 = (extOk d, resp.flag) :: (extTok d, tokv) :: (identV d, vU) :: toVEnv env := by
      rw [hVeq]
      simp only
      exact hset
    have hrest : restore pre V3 = (identV d, vU) :: toVEnv env := by
      rw [hV3]; exact restore_call_result
    refine ⟨restore pre V3, st3, .normal, ?_, .inr ⟨rfl, vU.toNat, ?_, ?_⟩⟩
    · exact Step.seqCons hlet0 (Step.seqCons hblk Step.seqNil)
    · exact hrest.trans (toVEnv_cons_u256 vU env).symm
    · exact ⟨hrest.trans (toVEnv_cons_u256 vU env).symm,
        envWF_cons (u256_lt_word vU) henv, hR3, hctx3⟩

theorem stmt_call_progress {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} (htot : CallsTotal calls)
    {n : Nat} {st : EvmState}
    {b m : Nat} {args : List Atom} {meth : I.Method}
    (hinv : Inv Γ c κ ctx w env (toVEnv env) st)
    (hbd : BindWF c Γ bind b m meth)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hwfCall : callWF c b m args = true)
    (hn : identsNodup env.length = true) :
    ∃ V' st' o,
      ExecStmts (yulD calls) (List.replicate n []) (toVEnv env) st
        (emitStmt c {} env.length (.call b m args)).stmts V' st' o ∧
      (o = .halt ∨
        (o = .normal ∧ V' = toVEnv env ∧ Inv Γ c κ ctx w env V' st')) := by
  have ⟨hlenA, hvals⟩ := callWF_arity_of_BindWF hwfCall hbd
  have hn3 : args.length ≤ 3 := hlenA ▸ hbd.harity
  have hR := hinv.rel
  have hctx := hinv.ctxr
  have henv := hinv.wf
  let d := env.length
  let funsN : FunEnv (yulD calls) := List.replicate n []
  let funsN1 : FunEnv (yulD calls) := List.replicate (n + 1) []
  let pre : VEnv evm := toVEnv env
  obtain ⟨st1, hpre, _, hMO, hstatic, _⟩ :=
    call_prefix_fwd (I := I) (funs := List.replicate (n + 1) []) pre hR hbd hctx henv
      (.inl rfl) hn
      (fun h => False.elim (by
        have := congrArg List.length h
        simp [pre, toVEnv, List.length_map, List.length_zip, List.length_range] at this)) hn3 hvals
  have hpre' := execStmts_lift_nils (calls := calls) (n := n + 1) hpre
  let tokv := BitVec.ofNat 256 (bind.addr w.self)
  let V1 : VEnv evm := (extTok d, tokv) :: pre
  have hget : VEnv.get V1 (extTok d) = some tokv := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨resp, hlet, hCall⟩ :=
    exec_let_call_fwd (calls := calls) htot funsN1 hget hstatic
      (gas := extCallGas) (insize := 4 + 32 * args.length)
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hlet
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  let st2 := finishCall .call st1 resp abiPtr (4 + 32 * args.length) abiPtr 32
  let V2 : VEnv evm := (extOk d, resp.flag) :: V1
  have hgetOk : VEnv.get V2 (extOk d) = some resp.flag := by
    rw [VEnv.get_cons, if_pos rfl]
  obtain ⟨V3, st3, o3, hsuf, hokP, hfailP, _⟩ :=
    call_suffix_fwd (funs := List.replicate (n + 1) []) (d := d) (ok := resp.flag)
      (ret := (bindingMethod c b m).2) (assign := none) hgetOk
  have hsuf' := execStmts_lift_nils (calls := calls) (n := n + 1) hsuf
  have hbody : ExecStmts (yulD calls) funsN1 pre st
      (emitExtCallBody c d b m args none) V3 st3 o3 := by
    rw [emitExtCallBody_split]
    have hlet' : ExecStmt (yulD calls) funsN1 V1 st1 (callLetOk d args) V2 st2 .normal := by
      simpa [callLetOk, V1, V2, st2] using hlet
    have hletS : ExecStmts (yulD calls) funsN1 V1 st1 [callLetOk d args] V2 st2 .normal :=
      Step.seqCons hlet' Step.seqNil
    have hpreLet :
        ExecStmts (yulD calls) funsN1 pre st
          (callPrefix c d b m args ++ [callLetOk d args]) V2 st2 .normal := by
      convert execStmts_append_open hpre' hletS
    exact execStmts_append_open hpreLet hsuf'
  have hfuns : funsN1 = [] :: funsN := by simp [funsN1, funsN, List.replicate_succ]
  rw [hfuns] at hbody
  have hh := hoist_emitExtCallBody (calls := calls) c d b m args none
  rw [emitStmt_call_stmts]
  rcases outcome_halt_or_normal_of_suffix (fun hS => (hokP hS).1) (fun h => (hfailP h).1) with ho | ho
  · subst ho
    have hblk := exec_block_halt_open (funs := funsN) hh hbody
    exact ⟨restore pre V3, st3, .halt, Step.seqStop hblk halt_ne_normal, .inl rfl⟩
  · subst ho
    have hblk := exec_block_ok_open (funs := funsN) hh hbody
    have hS : suffixOk resp.flag (bindingMethod c b m).2 st2 := by
      by_contra hns
      cases (hfailP hns).1
    have ⟨_, hMO2, hVeq⟩ := hokP hS
    have hsucc : resp.success = true := (flag_ne_zero_iff resp).mp hS.1
    have hR1 : R c Γ κ w st1 := R_memOnly hR hMO
    have hctx1 : ctxRel ctx st1 := ctxRel_memOnly hctx hMO
    have haddr : st1.env.address = BitVec.ofNat 256 ctx.self := hctx1.2.2.2.2.1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hni⟩ :=
      hconf _ st1 resp hCall rfl rfl haddr hsucc
    have hR3 : R c Γ κ w st3 :=
      R_memOnly (R_finishCall_success (α := α) hR1 hsucc hni) hMO2
    have hctx3 : ctxRel ctx st3 :=
      ctxRel_memOnly (ctxRel_finishCall hctx1 .call resp abiPtr (4 + 32 * args.length) abiPtr 32) hMO2
    have hV3 : V3 = V2 := by simpa using hVeq
    have hrest : restore pre V3 = toVEnv env := by
      rw [hV3]; exact restore_drop2
    refine ⟨restore pre V3, st3, .normal, Step.seqCons hblk Step.seqNil,
      .inr ⟨rfl, hrest, ⟨hrest.symm ▸ rfl, henv, hR3, hctx3⟩⟩⟩

/-! ## Memoryguard prefix on `yulD` -/

theorem exec_memoryGuardErased_nils {calls : ExternalCalls} {n : Nat}
    {V : VEnv evm} {st : EvmState} :
    ExecStmt (yulD calls) (List.replicate n []) V st memoryGuardErased V
      (stAfterGuard st) .normal := by
  have h := execStmt_lift (calls := calls) .none .none
    (exec_memoryGuardErased (List.replicate n []) V st)
  rwa [funEnvCast_replicate_nil] at h

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
      [.block guard, .switch sel cases (some [revert00])]) = [] :=
  hoist_yulD_of_evm (hoist_erased_runtime guard sel cases)

end Lsc.Compiler
