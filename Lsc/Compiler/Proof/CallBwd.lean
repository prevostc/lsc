import Lsc.Compiler.Proof.CallFwd

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Backward simulation of scoped `emitExtCall`:
`call_prefix_fwd` / `call_step_inv` / `call_suffix_fwd`, then `op_sim_call_bwd`
/ `stmt_sim_call_bwd`.
-/

namespace Lsc.Compiler

open YulSemantics
open Lsc hiding Op Stmt
open YulSemantics.EVM

theorem call_prefix_fwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    (funs : FunEnv evm) (pre : VEnv evm)
    (hR : R c Γ κ w st) (hbd : BindWF c Γ bind b m meth)
    (hctx : ctxRel ctx st) (hwf : EnvWF env)
    (htail : pre = toVEnv env ∨
      pre = (identV env.length, (0 : U256)) :: toVEnv env)
    (hn : identsNodup env.length = true)
    (hn1 : pre = (identV env.length, (0 : U256)) :: toVEnv env →
        identsNodup (env.length + 1) = true)
    (hn3 : args.length ≤ 3)
    (hvals : ∀ x ∈ args, atomWF x = true) :
    ∃ st',
      ExecStmts evm funs
        pre st
        (callPrefix c env.length b m args)
        ((extTok env.length, BitVec.ofNat 256 (bind.addr w.self)) :: pre) st' .normal ∧
      readBytes st'.memory abiPtr (4 + 32 * args.length) =
        abiInput (I.abi meth) (args.map (·.eval env)) ∧
      MemOnly st st' ∧
      st'.env.static = false ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  obtain ⟨stSel, hP, _, hMO0, hstatic, hmem, hCW0⟩ :=
    call_prefix_fwd_nil (I := I) funs pre hR hbd hctx
  have hselLt := hbd.hsel meth
  have hbm := bindingMethod_of_BindWF hbd
  let tokv := BitVec.ofNat 256 (bind.addr w.self)
  obtain ⟨st', hM, hpack, hMO, hCW⟩ :=
    mstoreArgs_exec (env := env) (V := (extTok env.length, tokv) :: pre) (tail := pre)
      funs stSel st.memory tokv
      (I.abi meth).selector args rfl htail hn hn1 hn3 hvals hwf hselLt hmem
  refine ⟨st', ?_, ?_, MemOnly.trans hMO0 hMO, ?_, hCW.trans hCW0⟩
  · rw [callPrefix_append]
    exact execStmts_append hP hM
  · simpa [abiInput, List.flatMap_map] using hpack
  · rcases hMO with ⟨_, _, _, _, _, _, _, hs, _, _, _⟩
    exact hs.trans hstatic

/-! ## (2) `call_step_inv` -/

theorem call_step_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {d : Nat} {args : List Atom} {target : U256}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hget : VEnv.get V (extTok d) = some target)
    (hstatic : st.env.static = false)
    (hn3 : args.length ≤ 3)
    (h : ExecStmt (yulD calls) funs V st (callLetOk d args) V' st' o) :
    ∃ resp, o = .normal ∧ V' = (extOk d, resp.flag) :: V ∧
      st' = finishCall .call st resp abiPtr (4 + 32 * args.length) abiPtr 32 ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 extCallGas
          target := target
          value := 0
          input := readBytes st.memory abiPtr (4 + 32 * args.length) }
        st resp := by
  unfold callLetOk at h
  obtain ⟨resp, ho, hV, hst, hCall⟩ :=
    exec_let_call_inv (tok := extTok d) (ok := extOk d) (gas := extCallGas)
      (insize := 4 + 32 * args.length) hget hstatic h
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hst
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  exact ⟨resp, ho, hV, hst, hCall⟩

/-! ## (3) `call_suffix_fwd` -/

theorem call_suffix_fwd (funs : FunEnv evm) {d : Nat} {ok : U256}
    {ret : AbiRet} {assign : Option YIdent}
    {V : VEnv evm} {st : EvmState}
    (hget : VEnv.get V (extOk d) = some ok) :
    ∃ V' st' o,
      ExecStmts evm funs V st (callSuffix d ret assign) V' st' o ∧
      (suffixOk ok ret st →
        o = .normal ∧ MemOnly st st' ∧
          V' = match assign with
            | none => V
            | some name => VEnv.set V name (suffixVal ret st)) ∧
      (¬ suffixOk ok ret st →
        o = .halt ∧ V' = V ∧ st'.halted = some (.revert, [])) ∧
      CallWorld.ofState st' = CallWorld.ofState st := by
  unfold callSuffix
  by_cases hok : ok = 0
  · subst hok
    refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt, ?_, ?_, ?_, ?_⟩
    · exact Step.seqStop (call_guard_fail funs hget) halt_ne_normal
    · intro hS; exact (hS.1 rfl).elim
    · intro; exact ⟨rfl, rfl, rfl⟩
    · simp [CallWorld.ofState, touchMemory]
  · have hguard := call_guard_pass (st := st) funs hget hok
    cases ret with
    | none =>
      cases assign with
      | none =>
        refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard Step.seqNil
        · intro; exact ⟨rfl, by simp [MemOnly], rfl⟩
        · intro hS; exact (hS ⟨hok, trivial⟩).elim
      | some name =>
        have hasn := callAssign_exec funs V st .none name
        refine ⟨VEnv.set V name (1#256), st, .normal, ?_, ?_, ?_, rfl⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard hasn
        · intro; exact ⟨rfl, by simp [MemOnly], by simp [suffixVal]⟩
        · intro hS; exact (hS ⟨hok, trivial⟩).elim
    | word =>
      by_cases hult : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = true
      · refine ⟨V, { touchMemory st 0 0 with halted := some (.revert, []) }, .halt,
          ?_, ?_, ?_, by simp [CallWorld.ofState, touchMemory]⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard
            (Step.seqStop (word_check_fail funs V st hult) halt_ne_normal)
        · intro hS; simp [suffixOk, hok, hult] at hS
        · intro; exact ⟨rfl, rfl, rfl⟩
      · have hpass : (BitVec.ofNat 256 st.returndata.length).ult 32#256 = false := by
          simpa using hult
        have hchk := word_check_pass funs V st hpass
        cases assign with
        | none =>
          refine ⟨V, st, .normal, ?_, ?_, ?_, rfl⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk Step.seqNil)
          · intro; exact ⟨rfl, by simp [MemOnly], rfl⟩
          · intro hS; exact (hS ⟨hok, hpass⟩).elim
        | some name =>
          have hasn := callAssign_exec funs V st .word name
          refine ⟨VEnv.set V name (loadWord st.memory abiPtr),
            touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk hasn)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, by simp [suffixVal]⟩
          · intro hS; exact (hS ⟨hok, hpass⟩).elim
    | boolOpt =>
      by_cases hp : boolOptPass st = true
      · have hchk := boolOpt_check_pass funs V st hp
        cases assign with
        | none =>
          refine ⟨V, touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk Step.seqNil)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, rfl⟩
          · intro hS
            have : suffixOk ok .boolOpt st := (suffixOk_boolOpt hok).mpr hp
            exact (hS this).elim
        | some name =>
          have hasn := callAssign_exec funs V (touchMemory st abiPtr 32) .boolOpt name
          refine ⟨VEnv.set V name (1#256), touchMemory st abiPtr 32, .normal, ?_, ?_, ?_,
            by simp [CallWorld.ofState, touchMemory]⟩
          · simp [callRetCheck]
            exact Step.seqCons hguard (Step.seqCons hchk hasn)
          · intro; exact ⟨rfl, memOnly_touch st abiPtr 32, by simp [suffixVal]⟩
          · intro hS
            have : suffixOk ok .boolOpt st := (suffixOk_boolOpt hok).mpr hp
            exact (hS this).elim
      · have hfail : boolOptPass st = false := by simpa using hp
        refine ⟨V,
          { touchMemory (touchMemory st abiPtr 32) 0 0 with
            halted := some (.revert, []) }, .halt, ?_, ?_, ?_,
          by simp [CallWorld.ofState, touchMemory]⟩
        · simp [callRetCheck]
          exact Step.seqCons hguard
            (Step.seqStop (boolOpt_check_fail funs V st hfail) halt_ne_normal)
        · intro hS
          have : boolOptPass st = true := (suffixOk_boolOpt hok).mp hS
          simp [hfail] at this
        · intro; exact ⟨rfl, rfl, rfl⟩

/-! ## (4) `op_sim_call_bwd` -/

/-- Shared scoped-call core: `emitExtCallBody` under `{ … }`. `assign = none` is
`Stmt.call` (`pre = toVEnv env`); `some (identV d)` is `Op.call` after `let v := 0`. -/
theorem extCall_block_bwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {pre : VEnv (yulD calls)} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    {assign : Option YIdent}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (α : Abs I.Ghost)
    (hR : R c Γ κ w st) (hctx : ctxRel ctx st) (henv : EnvWF env)
    (hbd : BindWF c Γ bind b m meth)
    (hRX : RX α bind w st)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF c b m args = true)
    (htail : pre = toVEnv env ∨
      pre = (identV env.length, (0 : U256)) :: toVEnv env)
    (hassign :
      (assign = none ∧ pre = toVEnv env) ∨
      (assign = some (identV env.length) ∧
        pre = (identV env.length, (0 : U256)) :: toVEnv env))
    (hn : identsNodup env.length = true)
    (hn1 : pre = (identV env.length, (0 : U256)) :: toVEnv env →
        identsNodup (env.length + 1) = true)
    (h : ExecStmt (yulD calls) funs pre st
      (.block (emitExtCallBody c env.length b m args assign)) V' st' o) :
    ∃ bit : Bool,
      (bit = true →
        ∀ g : Nat → Bool, g w.ncalls = true →
          Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
            .error .callFailed ∧
          o = .halt ∧ st'.halted = some (.revert, [])) ∧
      (bit = false →
        ∃ (v : Nat) (w0 : World S X E),
          w0.self = w.self ∧ w0.log = w.log ∧ w0.ncalls = w.ncalls + 1 ∧
          ∀ g : Nat → Bool, g w.ncalls = false →
            Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
              .ok (v, { w0 with faults := g }) ∧
            o = .normal ∧ RX α bind { w0 with faults := g } st' ∧
            (assign = none → V' = toVEnv env ∧
              Inv Γ c κ ctx { w0 with faults := g } env V' st') ∧
            (assign.isSome → V' = toVEnv (v :: env) ∧
              Inv Γ c κ ctx { w0 with faults := g } (v :: env) V' st')) := by
  let d := env.length
  have ⟨harity, hvals⟩ := callWF_arity_of_BindWF hwfCall hbd
  have hn3 : args.length ≤ 3 := by rw [harity]; exact hbd.harity
  have hret := bindingMethod_of_BindWF hbd
  obtain ⟨Vb, hbody, hrestore⟩ := exec_block_inv h
  have hhoist := hoist_emitExtCallBody (calls := calls) c d b m args assign
  rw [hhoist] at hbody
  rw [emitExtCallBody_split] at hbody
  rw [List.append_assoc] at hbody
  have hfunsB : noExtFuns (([] : FScope (yulD calls)) :: funs) = true :=
    noExtFuns_cons_nil hfuns
  let funsE := funEnvUncast calls ([] :: funs)
  cases execStmts_append_inv hbody with
  | inr hPstop =>
    have hdesc := execStmts_descend hfunsB (noExt_callPrefix c d b m args) hPstop.2
    obtain ⟨stP, hfwd, _, _, _, _⟩ :=
      call_prefix_fwd (I := I) funsE pre hR hbd hctx henv htail hn hn1 hn3 hvals
    have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
    exact (hPstop.1 ho.symm).elim
  | inl hPok =>
    obtain ⟨_, _, hP, hrest⟩ := hPok
    have hPdesc := execStmts_descend hfunsB (noExt_callPrefix c d b m args) hP
    obtain ⟨stP, hPfwd, hpack, hMO, hstaticP, hCW⟩ :=
      call_prefix_fwd (I := I) funsE pre hR hbd hctx henv htail hn hn1 hn3 hvals
    have ⟨hVPeq, hstPeq, _⟩ := execStmts_det_evm hPfwd hPdesc
    rw [← hVPeq, ← hstPeq] at hrest
    have hgetTok :
        VEnv.get
          ((extTok d, BitVec.ofNat 256 (bind.addr w.self)) :: pre)
          (extTok d) = some (BitVec.ofNat 256 (bind.addr w.self)) := by
      simp [VEnv.get]
    cases execStmts_cons_inv hrest with
    | inr hCstop =>
      have ⟨resp, ho, _, _, _⟩ :=
        call_step_inv hgetTok hstaticP hn3 hCstop.2
      exact (hCstop.1 ho).elim
    | inl hCok =>
      obtain ⟨_, _, hCall, hS⟩ := hCok
      obtain ⟨resp, _, hV2, hst2, hCallR⟩ :=
        call_step_inv hgetTok hstaticP hn3 hCall
      rw [hV2, hst2] at hS
      have hgetOk :
          VEnv.get
            ((extOk d, resp.flag) ::
              (extTok d, BitVec.ofNat 256 (bind.addr w.self)) :: pre)
            (extOk d) = some resp.flag := by
        simp [VEnv.get]
      rw [show (bindingMethod c b m).2 = (I.abi meth).ret from
        congrArg Prod.snd hret] at hS
      have hSdesc := execStmts_descend hfunsB
        (noExt_callSuffix d (I.abi meth).ret assign) hS
      obtain ⟨VS, stS, oS, hSfwd, hSok, hSfail, hCWS⟩ :=
        call_suffix_fwd
          (st := finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)
          (ret := (I.abi meth).ret)
          (assign := assign) funsE hgetOk
      have ⟨hVSeq, hstSeq, hoeq⟩ := execStmts_det_evm hSfwd hSdesc
      refine ⟨!resp.success, ?_⟩
      constructor
      · intro hbit g hg
        let w₁ : World S X E := { w with faults := g }
        have hsuccF : resp.success = false := by
          cases hsu : resp.success
          · rfl
          · simp [hsu] at hbit
        have hok0 : resp.flag = 0 := (flag_eq_zero_iff resp).mpr hsuccF
        have hnS : ¬ suffixOk resp.flag (I.abi meth).ret
            (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) := by
          intro hSok'
          exact hSok'.1 hok0
        have ⟨hoS, _, hh⟩ := hSfail hnS
        have hrun : Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ =
            .error .callFailed := by
          rw [Op.denote, hbd.hext]
          have hf : w₁.faults w₁.ncalls = true := hg
          simp [Tx.run_call, hf]
        exact ⟨hrun, hoeq.symm.trans hoS, hstSeq ▸ hh⟩
      · intro hbit
        have hsucc : resp.success = true := by
          cases hsu : resp.success
          · simp [hsu] at hbit
          · rfl
        have haddr : stP.env.address = BitVec.ofNat 256 ctx.self := by
          rcases hMO with ⟨_, _, _, _, _, _, ha, _, _, _, _⟩
          rcases hctx with ⟨_, _, _, _, had, _⟩
          exact ha.trans had
        have hα : α.ofState stP (bind.addr w.self) = bind.get w.ext := by
          rw [α.ofState_proj, hCW, ← α.ofState_proj]
          exact hRX
        have ⟨m', args', retv, g', hin, harity', hbdargs, hmodel, hdec, hg, hni⟩ :=
          hconf
            { kind := .call
              gas := BitVec.ofNat 256 extCallGas
              target := BitVec.ofNat 256 (bind.addr w.self)
              value := 0
              input := readBytes stP.memory abiPtr (4 + 32 * args.length) }
            stP resp hCallR rfl rfl haddr hsucc
        have hsel_eq : (I.abi m').selector = (I.abi meth).selector := by
          have ht := congrArg (fun l => l.take 4) (hin.symm.trans hpack)
          have htake : ∀ spec as, (abiInput spec as).take 4 = selectorBytes spec.selector := by
            intro spec as
            simp [abiInput, selectorBytes_length, List.take_append_of_le_length]
          rw [htake, htake] at ht
          exact selectorBytes_inj (hbd.hsel m') (hbd.hsel meth) ht
        have hm' : m' = meth := hbd.huniq m' hsel_eq
        cases hm'
        have hargs : args' = args.map (·.eval env) := by
          refine abiArgs_inj (hbd.hsel meth) hbdargs ?_ ?_ ?_ (hin.symm.trans hpack)
          · intro x hx
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            exact atom_eval_lt henv (hvals a ha)
          · simp [harity', harity]
          · rw [harity']; exact hbd.harity
        subst hargs
        have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
        have hmload : 32 ≤ resp.returndata.length →
            loadWord (finishCall .call stP resp abiPtr (4 + 32 * args.length)
                abiPtr 32).memory abiPtr =
              wordFrom resp.returndata 0 := by
          intro hlen
          exact finishCall_mload_ge32 .call stP resp abiPtr (4 + 32 * args.length)
            abiPtr 32 hlen (by decide)
        have hSok' : suffixOk resp.flag (I.abi meth).ret
            (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) := by
          simpa [finishCall_returndata] using
            decodeRet_suffixOk hflag hdec hmload
        have ⟨hoS, hMOS, hVeq⟩ := hSok hSok'
        have hval : suffixVal (I.abi meth).ret
            (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32) =
            BitVec.ofNat 256 retv := by
          cases hrt : (I.abi meth).ret
          · simp [suffixVal, decodeRet, hrt, finishCall_returndata] at hdec ⊢
            rcases hdec with ⟨hlen, _, hto⟩
            rw [hmload hlen]
            have hv : (wordFrom resp.returndata 0).toNat < wordBound := by
              simpa [wordBound] using (wordFrom resp.returndata 0).isLt
            exact (BitVec.eq_of_toNat_eq (toNat_ofNat_of_lt hv)).symm.trans
              (congrArg (BitVec.ofNat 256) hto)
          · simp [suffixVal, decodeRet, hrt] at hdec ⊢
            simp [hdec.1]
          · rcases hbd.hret with h | h <;> simp [h] at hrt
        have hvlt : retv < wordBound := by
          cases hrt : (I.abi meth).ret
          · simp [decodeRet, hrt] at hdec
            rw [← hdec.2.2]
            simpa [wordBound] using (wordFrom resp.returndata 0).isLt
          · simp [decodeRet, hrt] at hdec
            simp [hdec.1]; decide
          · rcases hbd.hret with h | h <;> simp [h] at hrt
        have hR2 := R_finishCall_success (α := α) (callee := bind.addr w.self)
          (iOff := abiPtr) (iSz := 4 + 32 * args.length)
          (oOff := abiPtr) (oSz := 32)
          (R_memOnly hR hMO) hsucc hni
        have hR3 := R_memOnly hR2 hMOS
        rw [hstSeq] at hR3 hMOS hCWS
        have hctx2 := ctxRel_finishCall (ctxRel_memOnly hctx hMO) .call
          resp abiPtr (4 + 32 * args.length) abiPtr 32
        have hRX2 := RX_finishCall_success (iOff := abiPtr)
          (iSz := 4 + 32 * args.length) (oOff := abiPtr) (oSz := 32)
          hα hsucc hg hni hbd.hgetset
        let w0 : World S X E :=
          { w with ext := bind.set w.ext g', ncalls := w.ncalls + 1 }
        refine ⟨retv, w0, rfl, rfl, rfl, ?_⟩
        intro g hgo
        let w₁ : World S X E := { w with faults := g }
        have hrun : Tx.run (Op.denote Γ env (.call b m args)) ctx w₁ =
            .ok (retv, { w0 with faults := g }) := by
          rw [Op.denote, hbd.hext]
          have hf : w₁.faults w₁.ncalls = false := hgo
          simp [Tx.run_call, hf]
          have hgext : bind.get w₁.ext = bind.get w.ext := rfl
          rw [hgext, ← hα, hmodel]
        have hRX2' : RX α bind { w0 with faults := g } st' := by
          unfold RX at hRX2 ⊢
          rw [α.ofState_proj, hCWS, ← α.ofState_proj]
          exact hRX2
        refine ⟨hrun, hoeq.symm.trans hoS, hRX2', ?_, ?_⟩
        · intro hnone
          have hpreEq : pre = toVEnv env := by
            cases hassign with
            | inl h => exact h.2
            | inr h =>
              rw [hnone] at h
              cases h.1
          have hVS : VS =
              (extOk d, resp.flag) ::
                (extTok d, BitVec.ofNat 256 (bind.addr w.self)) :: pre := by
            rw [hnone] at hVeq
            simpa using hVeq
          have hVeq' : V' = toVEnv env := by
            rw [hrestore, ← hVSeq, hVS, hpreEq]
            exact restore_drop2
          exact ⟨hVeq', hVeq', henv,
            R_with_ghost (bind.set w.ext g') (w.ncalls + 1) g hR3,
            ctxRel_memOnly hctx2 hMOS⟩
        · intro hsome
          have ⟨name, hname⟩ : ∃ n, assign = some n := Option.isSome_iff_exists.mp hsome
          have hpreEq : pre = (identV d, (0 : U256)) :: toVEnv env := by
            cases hassign with
            | inl h => exact nomatch (h.1.symm.trans hname)
            | inr h =>
              cases hname
              exact h.2
          have hname' : name = identV d := by
            cases hassign with
            | inl h =>
              rw [h.1] at hname
              cases hname
            | inr h =>
              cases hname
              cases h.1
              rfl
          subst hname'
          have hset :
              VEnv.set ((extOk d, resp.flag) :: (extTok d,
                  BitVec.ofNat 256 (bind.addr w.self)) ::
                (identV d, (0 : U256)) :: toVEnv env)
                (identV d)
                (suffixVal (I.abi meth).ret
                  (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)) =
              (extOk d, resp.flag) :: (extTok d,
                  BitVec.ofNat 256 (bind.addr w.self)) ::
                (identV d,
                  suffixVal (I.abi meth).ret
                    (finishCall .call stP resp abiPtr (4 + 32 * args.length)
                      abiPtr 32)) :: toVEnv env := by
            rw [VEnv.set_cons_ne (identV_ne_extOk d d).symm,
              VEnv.set_cons_ne (identV_ne_extTok d d).symm, VEnv.set_head]
          have hVS :
              VS = VEnv.set
                ((extOk d, resp.flag) :: (extTok d,
                    BitVec.ofNat 256 (bind.addr w.self)) ::
                  (identV d, (0 : U256)) :: toVEnv env)
                (identV d)
                (suffixVal (I.abi meth).ret
                  (finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)) := by
            rw [hname] at hVeq
            rw [hpreEq] at hVeq
            simpa using hVeq
          have hVeq' : V' = toVEnv (retv :: env) := by
            rw [hrestore, ← hVSeq, hVS, hset, hval, hpreEq, toVEnv_cons]
            exact restore_call_result
          exact ⟨hVeq', hVeq', envWF_cons hvlt henv,
            R_with_ghost (bind.set w.ext g') (w.ncalls + 1) g hR3,
            ctxRel_memOnly hctx2 hMOS⟩

theorem op_sim_call_bwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (α : Abs I.Ghost)
    (hinv : Inv Γ c κ ctx w env V st)
    (hbd : BindWF c Γ bind b m meth)
    (hRX : RX α bind w st)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF c b m args = true)
    (hn : identsNodup (env.length + 1) = true)
    (h : ExecStmts (yulD calls) funs V st
      ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o) :
    ∃ bit : Bool,
      (bit = true →
        ∀ g : Nat → Bool, g w.ncalls = true →
          Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
            .error .callFailed ∧
          o = .halt ∧ st'.halted = some (.revert, [])) ∧
      (bit = false →
        ∃ (v : Nat) (w0 : World S X E),
          w0.self = w.self ∧ w0.log = w.log ∧ w0.ncalls = w.ncalls + 1 ∧
          ∀ g : Nat → Bool, g w.ncalls = false →
            Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
              .ok (v, { w0 with faults := g }) ∧
            o = .normal ∧ V' = toVEnv (v :: env) ∧
            Inv Γ c κ ctx { w0 with faults := g } (v :: env) V' st' ∧
            RX α bind { w0 with faults := g } st') := by
  let d := env.length
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  rw [hVeq, emitLetOp_call_stmts] at h
  cases execStmts_cons_inv h with
  | inr hstop =>
    have ⟨ho, _, _⟩ := exec_let_lit_inv hstop.2
    exact (hstop.1 ho).elim
  | inl hlet =>
    obtain ⟨V1, st1, hdoLet, hblkStmts⟩ := hlet
    have ⟨_, hst1, hV1⟩ := exec_let_lit_inv hdoLet
    rw [hst1, hV1] at hblkStmts
    have hblkStmt : ExecStmt (yulD calls) funs
        ((identV d, (0 : U256)) :: toVEnv env) st
        (.block (emitExtCallBody c d b m args (some (identV d)))) V' st' o :=
      execStmts_one hblkStmts
    have hpre : (identV d, (0 : U256)) :: toVEnv env =
        (identV env.length, (0 : U256)) :: toVEnv env := rfl
    have hbit := extCall_block_bwd (α := α) hR hctx henv hbd hRX hconf hfuns hwfCall
      (.inr hpre) (.inr ⟨rfl, hpre⟩)
      (identsNodup_mono (Nat.le_succ _) hn) (fun _ => hn) hblkStmt
    rcases hbit with ⟨bit, hfail, hok⟩
    refine ⟨bit, hfail, ?_⟩
    intro hb
    obtain ⟨v, w0, hself, hlog, hncalls, hg⟩ := hok hb
    refine ⟨v, w0, hself, hlog, hncalls, ?_⟩
    intro g hgo
    obtain ⟨hrun, ho, hRX', _, hsome⟩ := hg g hgo
    have ⟨hV', hInv⟩ := hsome (by simp)
    exact ⟨hrun, ho, hV', hInv, hRX'⟩

theorem stmt_sim_call_bwd {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env : List Nat}
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {b m : Nat} {args : List Atom} {bind : Binding I S X} {meth : I.Method}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (α : Abs I.Ghost)
    (hinv : Inv Γ c κ ctx w env V st)
    (hbd : BindWF c Γ bind b m meth)
    (hRX : RX α bind w st)
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF c b m args = true)
    (hn : identsNodup env.length = true)
    (h : ExecStmts (yulD calls) funs V st
      (emitStmt c {} env.length (.call b m args)).stmts V' st' o) :
    ∃ bit : Bool,
      (bit = true →
        ∀ g : Nat → Bool, g w.ncalls = true →
          Tx.run (Stmt.denote Γ env (.call b m args)) ctx { w with faults := g } =
            .error .callFailed ∧
          o = .halt ∧ st'.halted = some (.revert, [])) ∧
      (bit = false →
        ∃ (w0 : World S X E),
          w0.self = w.self ∧ w0.log = w.log ∧ w0.ncalls = w.ncalls + 1 ∧
          ∀ g : Nat → Bool, g w.ncalls = false →
            Tx.run (Stmt.denote Γ env (.call b m args)) ctx { w with faults := g } =
              .ok ((), { w0 with faults := g }) ∧
            o = .normal ∧ V' = toVEnv env ∧
            Inv Γ c κ ctx { w0 with faults := g } env V' st' ∧
            RX α bind { w0 with faults := g } st') := by
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  rw [hVeq, emitStmt_call_stmts] at h
  have hblkStmt : ExecStmt (yulD calls) funs (toVEnv env) st
      (.block (emitExtCallBody c env.length b m args none)) V' st' o :=
    execStmts_one h
  have hbit := extCall_block_bwd (α := α) hR hctx henv hbd hRX hconf hfuns hwfCall
    (.inl rfl) (.inl ⟨rfl, rfl⟩) hn
    (fun hpre => by
      have := congrArg List.length hpre
      simp at this)
    hblkStmt
  rcases hbit with ⟨bit, hfail, hok⟩
  refine ⟨bit, ?_, ?_⟩
  · intro hb g hgo
    have ⟨hrun, ho, hh⟩ := hfail hb g hgo
    refine ⟨?_, ho, hh⟩
    have hE :
        (Γ.ext.call b m (args.map (·.eval env))).run ctx { w with faults := g } =
          .error .callFailed := by
      simpa [Op.denote] using hrun
    simp [Stmt.denote, Tx.run_bind, hE]
  · intro hb
    obtain ⟨v, w0, hself, hlog, hncalls, hg⟩ := hok hb
    refine ⟨w0, hself, hlog, hncalls, ?_⟩
    intro g hgo
    obtain ⟨hrun, ho, hRX', hnone, _⟩ := hg g hgo
    have ⟨hV', hInv⟩ := hnone rfl
    refine ⟨?_, ho, hV', hInv, hRX'⟩
    have hE :
        (Γ.ext.call b m (args.map (·.eval env))).run ctx { w with faults := g } =
          .ok (v, { w0 with faults := g }) := by
      simpa [Op.denote] using hrun
    simp [Stmt.denote, Tx.run_bind, hE]

end Lsc.Compiler
