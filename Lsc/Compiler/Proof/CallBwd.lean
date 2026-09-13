import Lsc.Compiler.Proof.CallFwd

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Backward simulation of selector-driven `emitExtCall` under `Oracle.ofExt`.
The only callee hypothesis is `ExtOracle.NoReentry` (reentrancy is not modelled).
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open Lsc hiding Op Stmt
open YulSemantics.EVM

/-! ## CALL / STATICCALL inversion -/

theorem emitExtCallOp_call (targetE : YExpr) (insize : Nat) :
    emitExtCallOp false targetE insize =
      bop EVM.Op.call
        [emitCallGas, targetE, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32] := rfl

theorem emitExtCallOp_view (targetE : YExpr) (insize : Nat) :
    emitExtCallOp true targetE insize =
      bop EVM.Op.staticcall
        [emitCallGas, targetE, lit abiPtr, lit insize, lit abiPtr, lit 32] := rfl

theorem call_step_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {env : List Nat} {target : Atom} {args : List Atom}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hV : V = toVEnv tag env ∨
      V = (identV tag env.length, (0 : U256)) :: toVEnv tag env)
    (hn : identsNodup tag env.length = true)
    (hn1 : V = (identV tag env.length, (0 : U256)) :: toVEnv tag env →
        identsNodup tag (env.length + 1) = true)
    (hstatic : st.env.static = false)
    (hn3 : args.length ≤ 3)
    (h : ExecStmt (yulD calls) funs V st
      (callLetOk tag env.length target args false) V' st' o) :
    ∃ resp, o = .normal ∧ V' = (extOk tag env.length, resp.flag) :: V ∧
      st' = finishCall .call st resp abiPtr (4 + 32 * args.length) abiPtr 32 ∧
      calls.Call
        { kind := .call
          gas := BitVec.ofNat 256 extCallGas
          target := BitVec.ofNat 256 (target.eval env)
          value := 0
          input := readBytes st.memory abiPtr (4 + 32 * args.length) }
        st resp := by
  unfold callLetOk emitExtCallOp emitCallGas at h
  have ht : ∀ {st0 r},
      EvalExpr (yulD calls) funs V st0 (atomE tag env.length target) r →
        r = .vals [BitVec.ofNat 256 (target.eval env)] st0 :=
    fun {_ _} hr => eval_atomE_unique tag hV hn hn1 hr
  obtain ⟨resp, ho, hV', hst, hCall⟩ :=
    exec_let_call_inv (ok := extOk tag env.length) (gas := extCallGas)
      (insize := 4 + 32 * args.length) ht hstatic h
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hst
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  exact ⟨resp, ho, hV', hst, hCall⟩

theorem staticcall_step_inv {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {env : List Nat} {target : Atom} {args : List Atom}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hV : V = toVEnv tag env ∨
      V = (identV tag env.length, (0 : U256)) :: toVEnv tag env)
    (hn : identsNodup tag env.length = true)
    (hn1 : V = (identV tag env.length, (0 : U256)) :: toVEnv tag env →
        identsNodup tag (env.length + 1) = true)
    (hn3 : args.length ≤ 3)
    (h : ExecStmt (yulD calls) funs V st
      (callLetOk tag env.length target args true) V' st' o) :
    ∃ resp, o = .normal ∧ V' = (extOk tag env.length, resp.flag) :: V ∧
      st' = finishCall .staticcall st resp abiPtr (4 + 32 * args.length) abiPtr 32 ∧
      calls.Call
        { kind := .staticcall
          gas := BitVec.ofNat 256 extCallGas
          target := BitVec.ofNat 256 (target.eval env)
          value := 0
          input := readBytes st.memory abiPtr (4 + 32 * args.length) }
        st resp := by
  unfold callLetOk emitExtCallOp emitCallGas at h
  have ht : ∀ {st0 r},
      EvalExpr (yulD calls) funs V st0 (atomE tag env.length target) r →
        r = .vals [BitVec.ofNat 256 (target.eval env)] st0 :=
    fun {_ _} hr => eval_atomE_unique tag hV hn hn1 hr
  obtain ⟨resp, ho, hV', hst, hCall⟩ :=
    exec_let_staticcall_inv (ok := extOk tag env.length) (gas := extCallGas)
      (insize := 4 + 32 * args.length) ht h
  rw [toNat_abiPtr, toNat_insize hn3, toNat_32] at hst
  rw [toNat_abiPtr, toNat_insize hn3] at hCall
  exact ⟨resp, ho, hV', hst, hCall⟩

/-! ## ABI words ↔ Core decode -/

theorem rdsNat_le (bs : List UInt8) : rdsNat bs ≤ bs.length := by
  simp [rdsNat, BitVec.toNat_ofNat]
  exact Nat.mod_le _ _

theorem rdsNat_ge32_length {bs : List UInt8} (h : 32 ≤ rdsNat bs) :
    32 ≤ bs.length :=
  Nat.le_trans h (rdsNat_le bs)

theorem abiWords_zero {bs : List UInt8} (h : rdsNat bs = 0) :
    abiWords bs = [] := by
  simp [abiWords, h]

theorem abiWords_ge32_lt64 {bs : List UInt8}
    (h32 : 32 ≤ rdsNat bs) (h64 : rdsNat bs < 64) :
    abiWords bs = [(wordFrom bs 0).toNat] := by
  have hn0 : rdsNat bs ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 32) h32)
  have hn32 : ¬ rdsNat bs < 32 := Nat.not_lt.mpr h32
  have hdiv : rdsNat bs / 32 = 1 := by omega
  simp [abiWords, hn0, hn32, hdiv, List.range_succ, List.range_zero]

theorem decode_word_of_abi {bs : List UInt8} {v : Nat}
    (h : decodeRet .word bs v) :
    AbiRetType.decode (α := Nat) (abiWords bs) = some v := by
  have hwords := abiWords_ge32_lt64 h.1 h.2.1
  simp [AbiRetType.decode, hwords, h.2.2]

theorem decode_boolOpt_of_abi {bs : List UInt8} {v : Nat}
    (h : decodeRet .boolOpt bs v) :
    AbiRetType.decode (α := Bool) (abiWords bs) = some (v != 0) ∧
      (v = 0 ∨ v = 1) := by
  cases h with
  | inl h0 =>
    rcases h0 with ⟨hn, hv⟩
    subst hv
    simp [AbiRetType.decode, abiWords_zero hn]
  | inr hrest =>
    rcases hrest with ⟨h32, h64, hv⟩
    have hwords := abiWords_ge32_lt64 h32 h64
    simp [AbiRetType.decode, hwords]
    by_cases hz : wordFrom bs 0 = 0
    · rw [if_pos hz] at hv
      simp [AbiRetType.decode, hwords, hz, hv]
    · have hnz : (wordFrom bs 0).toNat ≠ 0 := by
        intro htn
        exact hz (BitVec.eq_of_toNat_eq (by simp [htn]))
      rw [if_neg hz] at hv
      simp [AbiRetType.decode, hwords, hv, hnz]

theorem abiWords_eq_nil_iff (bs : List UInt8) :
    abiWords bs = [] ↔ rdsNat bs = 0 := by
  unfold abiWords
  by_cases h0 : rdsNat bs = 0
  · simp [h0]
  · by_cases h32 : rdsNat bs < 32
    · simp [h0, h32]
    · simp [h0, h32, List.map_eq_nil_iff, List.range_eq_nil]
      try omega

theorem abiWords_length_ne_one {bs : List UInt8}
    (h : ¬ (32 ≤ rdsNat bs ∧ rdsNat bs < 64)) :
    (abiWords bs).length ≠ 1 := by
  by_cases h0 : rdsNat bs = 0
  · simp [abiWords, h0]
  · by_cases h32 : rdsNat bs < 32
    · simp [abiWords, h0, h32]
    · have : 2 ≤ rdsNat bs / 32 := by omega
      simp [abiWords, h0, h32, List.length_map, List.length_range]
      omega

theorem decode_nat_fail {bs : List UInt8}
    (h : ¬ (32 ≤ rdsNat bs ∧ rdsNat bs < 64)) :
    AbiRetType.decode (α := Nat) (abiWords bs) = none := by
  have hn : (abiWords bs).length ≠ 1 := abiWords_length_ne_one h
  cases hlist : abiWords bs with
  | nil => rfl
  | cons w rest =>
    cases rest with
    | nil => simp [hlist] at hn
    | cons _ _ => rfl

theorem decode_bool_fail {bs : List UInt8}
    (hne : rdsNat bs ≠ 0)
    (h : ¬ (32 ≤ rdsNat bs ∧ rdsNat bs < 64)) :
    AbiRetType.decode (α := Bool) (abiWords bs) = none := by
  have hn : (abiWords bs).length ≠ 1 := abiWords_length_ne_one h
  have hnil : abiWords bs ≠ [] := by
    intro he; exact hne ((abiWords_eq_nil_iff bs).mp he)
  cases hlist : abiWords bs with
  | nil => exact (hnil hlist).elim
  | cons w rest =>
    cases rest with
    | nil => simp [hlist] at hn
    | cons _ _ => rfl

theorem skipOkGuard_call (ret : AbiRet) : skipOkGuard false ret = false := by
  simp [skipOkGuard]

theorem skipOkGuard_view (ret : AbiRet) :
    skipOkGuard true ret = decide (ret = .none) := by
  cases ret <;> rfl

theorem mkCallReq_input (kind : CallKind) (addr : Address) (sel : Nat)
    (args : List Nat) :
    (mkCallReq kind addr sel args).input =
      selectorBytes sel ++ args.flatMap wordBytes := rfl

theorem toCalls_call (o : ExtOracle) (req : CallRequest) (st : EvmState)
    (resp : CallResponse) :
    (toCalls o).Call req st resp ↔ resp = o req (ExtView.ofState st) :=
  Iff.rfl

theorem VEnv.set_cons_ne_open {D : Dialect} {x y : Ident} {vx vy : D.Value}
    {V : VEnv D} (h : x ≠ y) :
    VEnv.set ((x, vx) :: V) y vy = (x, vx) :: VEnv.set V y vy := by
  simp [VEnv.set, h]

theorem VEnv.set_head_open {D : Dialect} {x : Ident} {v w : D.Value} {V : VEnv D} :
    VEnv.set ((x, v) :: V) x w = (x, w) :: V := by
  simp [VEnv.set]

theorem u256_lt_word (v : U256) : v.toNat < wordBound := by
  simpa [wordBound] using v.isLt

theorem toVEnv_cons_u256 (v : U256) (env : List Nat) :
    toVEnv tag (v.toNat :: env) = (identV tag env.length, v) :: toVEnv tag env := by
  rw [toVEnv_cons]
  have h : (BitVec.ofNat 256 v.toNat).toNat = v.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  exact congrArg (fun v => (identV tag env.length, v) :: toVEnv tag env)
    (BitVec.eq_of_toNat_eq h)

theorem run_callAsNat_word {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.callAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .word addr sel args =
      Tx.call (α := Nat) addr sel args :=
  rfl

theorem run_callAsNat_boolOpt {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.callAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .boolOpt addr sel args =
      Tx.boolBit <$> Tx.call (α := Bool) addr sel args :=
  rfl

theorem run_callAsNat_none {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.callAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .none addr sel args =
      (fun _ : Unit => (0 : Nat)) <$> Tx.call (α := Unit) addr sel args :=
  rfl

theorem run_viewAsNat_word {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.viewAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .word addr sel args =
      Tx.view (α := Nat) addr sel args :=
  rfl

theorem run_viewAsNat_boolOpt {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.viewAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .boolOpt addr sel args =
      Tx.boolBit <$> Tx.view (α := Bool) addr sel args :=
  rfl

theorem run_viewAsNat_none {S E ε} (addr : Address) (sel : Nat)
    (args : List Nat) :
    Tx.viewAsNat (S := S) (X := ExtState) (E := E) (ε := ε) .none addr sel args =
      (fun _ : Unit => (0 : Nat)) <$> Tx.view (α := Unit) addr sel args :=
  rfl

/-- `Tx.run_call` at the `.run` elaboration of a Core `Nat` target. -/
theorem run_call_eval {S E ε α} [AbiRetType α] (addr : Nat) (sel : Nat)
    (args : List Nat) (ctx : Ctx) (w : World S ExtState E) :
    (Tx.call (S := S) (X := ExtState) (E := E) (ε := ε) (α := α)
        addr sel args).run ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .error .callFailed
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .error .callFailed
        | some v => .ok (v, { w with ext := x' }) := by
  erw [Tx.run_call]
  cases h : w.oracle.call addr sel args w.ext with
  | none => rfl
  | some prod =>
    cases AbiRetType.decode (α := α) prod.1 <;> rfl

/-- `Tx.run_view` at the `.run` elaboration of a Core `Nat` target. -/
theorem run_view_eval {S E ε α} [AbiRetType α] (addr : Nat) (sel : Nat)
    (args : List Nat) (ctx : Ctx) (w : World S ExtState E) :
    (Tx.view (S := S) (X := ExtState) (E := E) (ε := ε) (α := α)
        addr sel args).run ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .error .callFailed
      | some v => .ok (v, w) := by
  erw [Tx.run_view]
  cases AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) <;> rfl

theorem or_one_b2w (b : Bool) : (1 : U256) ||| b2w b = 1 := by
  cases b <;> (
    apply BitVec.eq_of_toNat_eq
    simp [b2w, BitVec.toNat_or]
  )

theorem suffixVal_boolOpt_empty {st : EvmState}
    (h : BitVec.ofNat 256 st.returndata.length = 0#256) :
    suffixVal .boolOpt st = 1 := by
  simp [suffixVal, h, b2w_true]
  exact or_one_b2w _

theorem ite_zero_b2w (w : U256) :
    (if w = 0 then (0 : Nat) else 1) = (b2w (w ≠ 0)).toNat := by
  by_cases h : w = 0
  · simp [h, b2w]
  · simp [b2w, h]
    split_ifs with h0
    · exact (h h0).elim
    · rfl

theorem suffixVal_boolOpt_word {st : EvmState} {w : U256}
    (hne : BitVec.ofNat 256 st.returndata.length ≠ 0)
    (hmw : loadWord st.memory abiPtr = w) :
    suffixVal .boolOpt st = b2w (w ≠ 0) := by
  have hdec : decide (BitVec.ofNat 256 st.returndata.length = 0#256) = false :=
    decide_eq_false (by simpa using hne)
  simp [suffixVal, hmw, b2w, hdec]

theorem ite_zero_decide (w : U256) :
    (if w = 0#256 then (0 : Nat) else 1) =
      (b2w (!decide (w = 0#256))).toNat := by
  by_cases h : w = 0#256
  · simp [h, b2w]
  · simp [h, b2w, decide_eq_false h]

theorem ite_b2w_toNat (b : Bool) :
    (if (b2w b).toNat = 0 then (0 : Nat) else 1) = (b2w b).toNat := by
  cases b <;> simp [b2w]

theorem boolBit_of_wordFrom (w : U256) :
    Tx.boolBit (w.toNat != 0) = (b2w (w ≠ 0)).toNat := by
  by_cases hz : w = 0
  · subst hz
    simp [Tx.boolBit, b2w]
  · have htn : w.toNat ≠ 0 := by
      intro h0
      exact hz (BitVec.eq_of_toNat_eq (by simp [h0]))
    simp [Tx.boolBit, b2w, htn]
    split_ifs with h0
    · exact (hz h0).elim
    · rfl

theorem stmt_run_call {S X E ε} {Γ : ContractSchema S X E ε}
    (env : List Nat) (t : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Stmt.denote Γ env (.call t sel args ret)) ctx w =
      match Tx.run (Op.denote Γ env (.call t sel args ret)) ctx w with
      | .ok (_, w') => .ok ((), w')
      | .error e => .error e := by
  simp [Stmt.denote]
  cases (Op.denote Γ env (.call t sel args ret)).run ctx w <;> rfl

theorem stmt_run_view {S X E ε} {Γ : ContractSchema S X E ε}
    (env : List Nat) (t : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Stmt.denote Γ env (.view t sel args ret)) ctx w =
      match Tx.run (Op.denote Γ env (.view t sel args ret)) ctx w with
      | .ok (_, w') => .ok ((), w')
      | .error e => .error e := by
  simp [Stmt.denote]
  cases (Op.denote Γ env (.view t sel args ret)).run ctx w <;> rfl

/-! ## Shared scoped-call core -/

/-- `emitExtCallBody` of a CALL under `{ … }`. `assign = none` is `Stmt.call`;
`some (identV tag d)` is `Op.call` after `let v := 0`. Reentrancy is excluded
by `NoReentry`; everything else about the callee is adversarial. -/
theorem extCall_block_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {pre : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {assign : Option YIdent}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hR : R c Γ κ w st) (hctx : ctxRel ctx st) (henv : EnvWF env)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (htail : pre = toVEnv tag env ∨
      pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env)
    (hassign :
      (assign = none ∧ pre = toVEnv tag env) ∨
      (assign = some (identV tag env.length) ∧
        pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env))
    (hn : identsNodup tag env.length = true)
    (hn1 : pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env →
        identsNodup tag (env.length + 1) = true)
    (h : ExecStmt (yulD (toCalls o)) funs pre st
      (.block (emitExtCallBody tag env.length target sel args ret false assign))
      V' st' out) :
    match Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok (v, w') =>
        out = .normal ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st' ∧
          (assign = none → V' = toVEnv tag env ∧
            Inv tag Γ c κ ctx w' env V' st') ∧
          (assign.isSome → V' = toVEnv tag (v :: env) ∧
            Inv tag Γ c κ ctx w' (v :: env) V' st') := by
  let d := env.length
  rcases hNR with ⟨hNoI, hIgn⟩
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  obtain ⟨Vb, hbody, hrestore⟩ := exec_block_inv h
  have hhoist := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    false assign
  rw [hhoist] at hbody
  rw [emitExtCallBody_split] at hbody
  rw [List.append_assoc] at hbody
  have hfunsB : noExtFuns (([] : FScope (yulD (toCalls o))) :: funs) = true :=
    noExtFuns_cons_nil hfuns
  let funsE := funEnvUncast (toCalls o) ([] :: funs)
  cases execStmts_append_inv hbody with
  | inr hPstop =>
    have hdesc := execStmts_descend hfunsB (noExt_callPrefix tag d sel args) hPstop.2
    obtain ⟨stP, hfwd, _, _, _, _, _⟩ :=
      call_prefix_fwd tag (env := env) (V := pre) (st := st) (ctx := ctx)
        funsE sel args htail hn hn1 hctx henv hn3 hvals hsel
    have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
    exact (hPstop.1 ho.symm).elim
  | inl hPok =>
    obtain ⟨_, _, hP, hrest⟩ := hPok
    have hPdesc := execStmts_descend hfunsB (noExt_callPrefix tag d sel args) hP
    obtain ⟨stP, hPfwd, hpack, hMO, hstaticP, hCW, hEV⟩ :=
      call_prefix_fwd tag (env := env) (V := pre) (st := st) (ctx := ctx)
        funsE sel args htail hn hn1 hctx henv hn3 hvals hsel
    have ⟨hVPeq, hstPeq, _⟩ := execStmts_det_evm hPfwd hPdesc
    rw [← hVPeq, ← hstPeq] at hrest
    cases execStmts_cons_inv hrest with
    | inr hCstop =>
      have ⟨resp, ho, _, _, _⟩ :=
        call_step_inv tag htail hn hn1 hstaticP hn3 hCstop.2
      exact (hCstop.1 ho).elim
    | inl hCok =>
      obtain ⟨_, _, hCall, hS⟩ := hCok
      obtain ⟨resp, _, hV2, hst2, hCallR⟩ :=
        call_step_inv tag htail hn hn1 hstaticP hn3 hCall
      rw [hV2, hst2] at hS
      have hgetOk :
          VEnv.get ((extOk tag d, resp.flag) :: pre) (extOk tag d) = some resp.flag := by
        simp [VEnv.get]
      have hSdesc := execStmts_descend hfunsB
        (noExt_callSuffix tag d ret false assign) hS
      obtain ⟨VS, stS, oS, hSfwd, hSok, hSfail, hCWS⟩ :=
        call_suffix_fwd
          tag (st := finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32)
          (ret := ret) (isView := false) (assign := assign) funsE hgetOk
      have ⟨hVSeq, hstSeq, hoeq⟩ := execStmts_det_evm hSfwd hSdesc
      rw [hrestore, ← hVSeq, ← hstSeq, ← hoeq]
      let stCall := finishCall .call stP resp abiPtr (4 + 32 * args.length) abiPtr 32
      have hreq :
          ({ kind := .call
             gas := BitVec.ofNat 256 extCallGas
             target := BitVec.ofNat 256 (target.eval env)
             value := 0
             input := readBytes stP.memory abiPtr (4 + 32 * args.length) } : CallRequest) =
            mkCallReq .call (target.eval env) sel (args.map (·.eval env)) := by
        simp [mkCallReq, hpack, List.flatMap_map]
      have hAgrP : ExtAgree ctx.self w.ext stP := ExtAgree_memOnly hAgr hEV
      have haddrP : stP.env.address = BitVec.ofNat 256 ctx.self := by
        rcases hMO with ⟨_, _, _, _, _, _, ha, _, _, _, _⟩
        exact ha.trans (ctxRel_address hctx)
      have hresp : resp = o (mkCallReq .call (target.eval env) sel
          (args.map (·.eval env))) w.ext := by
        have hY := (toCalls_call o _ stP resp).mp hCallR
        have hign := hIgn (mkCallReq .call (target.eval env) sel
            (args.map (·.eval env))) w.ext stP haddrP hAgrP
        rw [hreq] at hY
        exact hY.trans hign.symm
      have hcore_call :
          w.oracle.call (target.eval env) sel (args.map (·.eval env)) w.ext =
            if resp.success then
              some (abiWords resp.returndata, ofCallSuccess w.ext resp)
            else none := by
        simp [hOr, Oracle.ofExt, hresp]
      by_cases hsucc : resp.success = true
      · have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
        have hmload : 32 ≤ resp.returndata.length →
            loadWord stCall.memory abiPtr = wordFrom resp.returndata 0 :=
          fun hlen =>
            finishCall_mload_ge32 .call stP resp abiPtr (4 + 32 * args.length)
              abiPtr 32 hlen (by decide)
        by_cases hSok' : suffixOk resp.flag ret stCall (!skipOkGuard false ret)
        · have ⟨hoS, hMOS, hEVS, hVeq⟩ := hSok hSok'
          rw [hoS]
          have hni := hNoI
            (mkCallReq .call (target.eval env) sel (args.map (·.eval env)))
            stP haddrP
          have hni' : resp.world.storage = stP.storage ∧
              resp.world.transient = stP.transient ∧
              resp.world.selfBalance = stP.env.selfBalance ∧
              resp.world.balanceOf = stP.env.balanceOf ∧
              (∀ l ∈ resp.world.logs, l.address ≠ stP.env.address) := by
            have heq : o (mkCallReq .call (target.eval env) sel
                  (args.map (·.eval env))) w.ext =
                o (mkCallReq .call (target.eval env) sel
                  (args.map (·.eval env))) (ExtView.ofState stP) :=
              hIgn _ w.ext stP haddrP hAgrP
            have hni' := hni
            rw [← heq, ← hresp] at hni'
            exact hni'
          have hR2 := R_finishCall_success (resp := resp) (iOff := abiPtr)
            (iSz := 4 + 32 * args.length) (oOff := abiPtr) (oSz := 32)
            (R_memOnly hR hMO) hsucc hni'.1 hni'.2.2.2.2
          have hR3 := R_memOnly hR2 hMOS
          have hAgr2 := ExtAgree_finishCall_success (resp := resp) (iOff := abiPtr)
            (iSz := 4 + 32 * args.length) (oOff := abiPtr) (oSz := 32) hAgrP hsucc
          have hAgr3 := ExtAgree_memOnly hAgr2 hEVS
          have hctx2 := ctxRel_memOnly
            (ctxRel_finishCall (ctxRel_memOnly hctx hMO) .call resp
              abiPtr (4 + 32 * args.length) abiPtr 32) hMOS
          let sval := suffixVal ret stCall
          let vNat := sval.toNat
          let w' : World S ExtState E := { w with ext := ofCallSuccess w.ext resp }
          have hR4 := R_with_ext (ofCallSuccess w.ext resp) hR3
          have hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w =
              .ok (vNat, w') := by
            simp [Op.denote]
            cases ret with
            | none =>
              simp [Tx.callAsNat, Tx.run_map, run_call_eval, hcore_call, hsucc, AbiRetType.decode,
                suffixVal, vNat, sval, w']
            | word =>
              have hp : wordRetPass stCall = true := by
                simpa [skipOkGuard_call] using hSok'.2
              have ⟨h32, h64⟩ := (wordRetPass_iff stCall).mp hp
              have h32r : 32 ≤ rdsNat resp.returndata := by simpa [stCall] using h32
              have h64r : rdsNat resp.returndata < 64 := by simpa [stCall] using h64
              have hAbi := decode_word_of_abi (bs := resp.returndata) ⟨h32r, h64r, rfl⟩
              have hmw := hmload (by
                simpa [stCall] using
                  (rdsNat_ge32_length (bs := stCall.returndata) h32))
              simp [Tx.callAsNat, run_call_eval, hcore_call, hsucc, hAbi, suffixVal, vNat, sval, w', hmw]
            | boolOpt =>
              have hp := hSok'.2
              simp [skipOkGuard_call, suffixOk] at hp
              simp [Tx.callAsNat, Tx.run_map, run_call_eval]
              cases hp with
              | inl hempty =>
                have hn0 : rdsNat stCall.returndata = 0 := by
                  simpa [rdsNat] using congrArg BitVec.toNat hempty
                have hn0' : rdsNat resp.returndata = 0 := by simpa [stCall] using hn0
                have hAbi : AbiRetType.decode (α := Bool) (abiWords resp.returndata) =
                    some true := by
                  simp [AbiRetType.decode, abiWords_zero hn0']
                have hempty' :
                    BitVec.ofNat 256 stCall.returndata.length = 0#256 := by
                  simpa using hempty
                simp [hcore_call, hsucc, hAbi,
                  suffixVal_boolOpt_empty hempty', vNat, sval, w', Tx.boolBit]
                try exact ite_b2w_toNat _
              | inr hwp =>
                have ⟨h32, h64⟩ := (wordRetPass_iff stCall).mp hwp
                have h32r : 32 ≤ rdsNat resp.returndata := by simpa [stCall] using h32
                have h64r : rdsNat resp.returndata < 64 := by simpa [stCall] using h64
                have hmw := hmload (by
                  simpa [stCall] using
                    (rdsNat_ge32_length (bs := stCall.returndata) h32))
                have hne : BitVec.ofNat 256 stCall.returndata.length ≠ 0 := by
                  intro hz
                  have : rdsNat stCall.returndata = 0 := by
                    simpa [rdsNat] using congrArg BitVec.toNat hz
                  omega
                have hdec : decodeRet .boolOpt resp.returndata
                    (if wordFrom resp.returndata 0 = 0 then 0 else 1) :=
                  .inr ⟨h32r, h64r, rfl⟩
                have ⟨hAbi, _⟩ := decode_boolOpt_of_abi hdec
                simp [hcore_call, hsucc, hAbi,
                  suffixVal_boolOpt_word hne hmw, vNat, sval, w',
                  boolBit_of_wordFrom, ite_zero_b2w, ite_zero_decide, Tx.boolBit]
                try exact ite_b2w_toNat _
          simp [hrun]
          first | refine ⟨rfl, hR4, hAgr3, ?_, ?_⟩ | refine ⟨hR4, hAgr3, ?_, ?_⟩
          · intro hnone
            have hpreEq : pre = toVEnv tag env := by
              cases hassign with
              | inl h => exact h.2
              | inr h =>
                rw [hnone] at h
                cases h.1
            have hVS : VS = (extOk tag d, resp.flag) :: pre := by
              rw [hnone] at hVeq
              simpa using hVeq
            have hVeq' : restore pre VS = toVEnv tag env := by
              rw [hVS, hpreEq]
              exact restore_drop1
            exact ⟨hVeq', hVeq', henv, hR4, hctx2⟩
          · intro hsome
            have ⟨name, hname⟩ : ∃ n, assign = some n := Option.isSome_iff_exists.mp hsome
            have hpreEq : pre = (identV tag d, (0 : U256)) :: toVEnv tag env := by
              cases hassign with
              | inl h =>
                have : none = some name := h.1.symm.trans hname
                cases this
              | inr h =>
                cases hname
                exact h.2
            have hname' : name = identV tag d := by
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
                VEnv.set ((extOk tag d, resp.flag) ::
                    (identV tag d, (0 : U256)) :: toVEnv tag env)
                  (identV tag d) sval =
                (extOk tag d, resp.flag) ::
                  (identV tag d, sval) :: toVEnv tag env := by
              rw [VEnv.set_cons_ne_open (identV_ne_extOk tag d d).symm,
                VEnv.set_head_open]
            have hVeq' : restore pre VS = toVEnv tag (vNat :: env) := by
              rw [hname] at hVeq
              rw [hVeq, hpreEq]
              simp [sval, stCall, vNat]
              rw [VEnv.set_cons_ne_open (identV_ne_extOk tag d d).symm,
                VEnv.set_head_open, restore_call_assign, toVEnv_cons_u256]
            exact ⟨hVeq', hVeq', envWF_cons (u256_lt_word sval) henv, hR4, hctx2⟩
        · have ⟨hoS, _, hh⟩ := hSfail hSok'
          have hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w =
              .error .callFailed := by
            simp [Op.denote]
            cases ret with
            | none =>
              exact (hSok' ⟨Or.inr hflag, trivial⟩).elim
            | word =>
              have hp : ¬ (32 ≤ rdsNat stCall.returndata ∧
                  rdsNat stCall.returndata < 64) := by
                intro hp
                have hwp : wordRetPass stCall = true := (wordRetPass_iff _).mpr hp
                exact hSok' ⟨Or.inr hflag, by simpa [skipOkGuard_call] using hwp⟩
              have hdec : AbiRetType.decode (α := Nat) (abiWords resp.returndata) = none := by
                simpa [stCall] using decode_nat_fail hp
              simp [Tx.callAsNat, run_call_eval, hcore_call, hsucc, hdec]
            | boolOpt =>
              have hempty : BitVec.ofNat 256 stCall.returndata.length ≠ 0 := by
                intro hz
                exact hSok' ⟨Or.inr hflag, by
                  simp [skipOkGuard_call, suffixOk]
                  exact .inl hz⟩
              have hp : ¬ (32 ≤ rdsNat stCall.returndata ∧
                  rdsNat stCall.returndata < 64) := by
                intro hp
                have hwp : wordRetPass stCall = true := (wordRetPass_iff _).mpr hp
                exact hSok' ⟨Or.inr hflag, by
                  simp [skipOkGuard_call, suffixOk]
                  exact .inr hwp⟩
              have hne : rdsNat stCall.returndata ≠ 0 := by
                intro hz
                apply hempty
                exact BitVec.eq_of_toNat_eq (by simpa [rdsNat] using hz)
              have hdec : AbiRetType.decode (α := Bool) (abiWords resp.returndata) = none := by
                simpa [stCall] using decode_bool_fail hne hp
              simp [Tx.callAsNat, Tx.run_map, run_call_eval, hcore_call, hsucc, hdec]
          simp [hrun]
          first | exact ⟨hoS, hh, rfl⟩ | exact ⟨hoS, hh⟩
      · have hfail : resp.success = false := by simpa using hsucc
        have hok0 : resp.flag = 0 := (flag_eq_zero_iff resp).mpr hfail
        have hnS : ¬ suffixOk resp.flag ret stCall (!skipOkGuard false ret) := by
          intro hSok'
          have : resp.flag ≠ 0 := by
            cases hSok'.1 with
            | inl h => simp [skipOkGuard_call] at h
            | inr h => exact h
          exact this hok0
        have ⟨hoS, _, hh⟩ := hSfail hnS
        have hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w =
            .error .callFailed := by
          simp [Op.denote]
          cases ret with
          | word =>
            simp [Tx.callAsNat, run_call_eval, hcore_call, hfail]
          | boolOpt =>
            simp [Tx.callAsNat, Tx.run_map, run_call_eval, hcore_call, hfail]
          | none =>
            simp [Tx.callAsNat, Tx.run_map, run_call_eval, hcore_call, hfail]
        simp [hrun]
        first | exact ⟨hoS, hh, rfl⟩ | exact ⟨hoS, hh⟩

theorem op_sim_call_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag (env.length + 1) = true)
    (h : ExecStmts (yulD (toCalls o)) funs V st
      ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts V' st' out) :
    match Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok (v, w') =>
        out = .normal ∧ V' = toVEnv tag (v :: env) ∧
          Inv tag Γ c κ ctx w' (v :: env) V' st' ∧
          ExtAgree ctx.self w'.ext st' := by
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
    have hblkStmt : ExecStmt (yulD (toCalls o)) funs
        ((identV tag d, (0 : U256)) :: toVEnv tag env) st
        (.block (emitExtCallBody tag d target sel args ret false (some (identV tag d))))
        V' st' out :=
      execStmts_one hblkStmts
    have hpre : (identV tag d, (0 : U256)) :: toVEnv tag env =
        (identV tag env.length, (0 : U256)) :: toVEnv tag env := rfl
    have hbit := extCall_block_bwd tag o hR hctx henv hAgr hOr hNR hfuns hwfCall hsel
      (.inr hpre) (.inr ⟨rfl, hpre⟩)
      (identsNodup_mono tag (Nat.le_succ _) hn) (fun _ => hn) hblkStmt
    cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | error e =>
      simpa [hrun] using hbit
    | ok p =>
      rcases p with ⟨v, w'⟩
      rw [hrun] at hbit
      rcases hbit with ⟨ho, -, hAgr', -, hImp⟩
      have ⟨hV', hInv⟩ := hImp (by simp)
      exact ⟨ho, hV', hInv, hAgr'⟩

theorem stmt_sim_call_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true)
    (h : ExecStmts (yulD (toCalls o)) funs V st
      (emitStmt tag c {} env.length (.call target sel args ret)).stmts V' st' out) :
    match Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok ((), w') =>
        out = .normal ∧ V' = toVEnv tag env ∧
          Inv tag Γ c κ ctx w' env V' st' ∧
          ExtAgree ctx.self w'.ext st' := by
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  rw [hVeq, emitStmt_call_stmts] at h
  have hblkStmt : ExecStmt (yulD (toCalls o)) funs (toVEnv tag env) st
      (.block (emitExtCallBody tag env.length target sel args ret false none)) V' st' out :=
    execStmts_one h
  have hbit := extCall_block_bwd tag o hR hctx henv hAgr hOr hNR hfuns hwfCall hsel
    (.inl rfl) (.inl ⟨rfl, rfl⟩) hn
    (fun hpre => by
      have := congrArg List.length hpre
      simp at this)
    hblkStmt
  rw [stmt_run_call]
  cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
  | error e =>
    simpa [hrun] using hbit
  | ok p =>
    rcases p with ⟨v, w'⟩
    rw [hrun] at hbit
    rcases hbit with ⟨ho, -, hAgr', hImp, -⟩
    have ⟨hV', hInv⟩ := hImp (by simp)
    exact ⟨ho, hV', hInv, hAgr'⟩

/-- `emitExtCallBody` of a STATICCALL under `{ … }`. `assign = none` is
`Stmt.view`; `some (identV tag d)` is `Op.view` after `let v := 0`.
`view` is pure by construction (`CallKind.staticcall` never installs the
callee world). `NoReentry` is still required so Core's lagged `w.ext`
agrees with the Yul request view. Reentrancy is not modelled; everything
else about the callee is adversarial. A `view` of `AbiRet.none` skips the
`ok`-guard (`Tx.viewAsNat .none` is total). -/
theorem extView_block_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {pre : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {assign : Option YIdent}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hR : R c Γ κ w st) (hctx : ctxRel ctx st) (henv : EnvWF env)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (htail : pre = toVEnv tag env ∨
      pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env)
    (hassign :
      (assign = none ∧ pre = toVEnv tag env) ∨
      (assign = some (identV tag env.length) ∧
        pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env))
    (hn : identsNodup tag env.length = true)
    (hn1 : pre = (identV tag env.length, (0 : U256)) :: toVEnv tag env →
        identsNodup tag (env.length + 1) = true)
    (h : ExecStmt (yulD (toCalls o)) funs pre st
      (.block (emitExtCallBody tag env.length target sel args ret true assign))
      V' st' out) :
    match Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok (v, w') =>
        out = .normal ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st' ∧
          (assign = none → V' = toVEnv tag env ∧
            Inv tag Γ c κ ctx w' env V' st') ∧
          (assign.isSome → V' = toVEnv tag (v :: env) ∧
            Inv tag Γ c κ ctx w' (v :: env) V' st') := by
  let d := env.length
  rcases hNR with ⟨hNoI, hIgn⟩
  obtain ⟨_, hvals, hn3⟩ := callWF_elim hwfCall
  obtain ⟨Vb, hbody, hrestore⟩ := exec_block_inv h
  have hhoist := hoist_emitExtCallBody tag (calls := toCalls o) d target sel args ret
    true assign
  rw [hhoist] at hbody
  rw [emitExtCallBody_split] at hbody
  rw [List.append_assoc] at hbody
  have hfunsB : noExtFuns (([] : FScope (yulD (toCalls o))) :: funs) = true :=
    noExtFuns_cons_nil hfuns
  let funsE := funEnvUncast (toCalls o) ([] :: funs)
  cases execStmts_append_inv hbody with
  | inr hPstop =>
    have hdesc := execStmts_descend hfunsB (noExt_callPrefix tag d sel args) hPstop.2
    obtain ⟨stP, hfwd, _, _, _, _, _⟩ :=
      call_prefix_fwd tag (env := env) (V := pre) (st := st) (ctx := ctx)
        funsE sel args htail hn hn1 hctx henv hn3 hvals hsel
    have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
    exact (hPstop.1 ho.symm).elim
  | inl hPok =>
    obtain ⟨_, _, hP, hrest⟩ := hPok
    have hPdesc := execStmts_descend hfunsB (noExt_callPrefix tag d sel args) hP
    obtain ⟨stP, hPfwd, hpack, hMO, _, hCW, hEV⟩ :=
      call_prefix_fwd tag (env := env) (V := pre) (st := st) (ctx := ctx)
        funsE sel args htail hn hn1 hctx henv hn3 hvals hsel
    have ⟨hVPeq, hstPeq, _⟩ := execStmts_det_evm hPfwd hPdesc
    rw [← hVPeq, ← hstPeq] at hrest
    cases execStmts_cons_inv hrest with
    | inr hCstop =>
      have ⟨resp, ho, _, _, _⟩ :=
        staticcall_step_inv tag htail hn hn1 hn3 hCstop.2
      exact (hCstop.1 ho).elim
    | inl hCok =>
      obtain ⟨_, _, hCall, hS⟩ := hCok
      obtain ⟨resp, _, hV2, hst2, hCallR⟩ :=
        staticcall_step_inv tag htail hn hn1 hn3 hCall
      rw [hV2, hst2] at hS
      have hgetOk :
          VEnv.get ((extOk tag d, resp.flag) :: pre) (extOk tag d) = some resp.flag := by
        simp [VEnv.get]
      have hSdesc := execStmts_descend hfunsB
        (noExt_callSuffix tag d ret true assign) hS
      obtain ⟨VS, stS, oS, hSfwd, hSok, hSfail, hCWS⟩ :=
        call_suffix_fwd
          tag (st := finishCall .staticcall stP resp abiPtr (4 + 32 * args.length) abiPtr 32)
          (ret := ret) (isView := true) (assign := assign) funsE hgetOk
      have ⟨hVSeq, hstSeq, hoeq⟩ := execStmts_det_evm hSfwd hSdesc
      rw [hrestore, ← hVSeq, ← hstSeq, ← hoeq]
      let stCall := finishCall .staticcall stP resp abiPtr (4 + 32 * args.length) abiPtr 32
      have hreq :
          ({ kind := .staticcall
             gas := BitVec.ofNat 256 extCallGas
             target := BitVec.ofNat 256 (target.eval env)
             value := 0
             input := readBytes stP.memory abiPtr (4 + 32 * args.length) } : CallRequest) =
            mkCallReq .staticcall (target.eval env) sel (args.map (·.eval env)) := by
        simp [mkCallReq, hpack, List.flatMap_map]
      have hAgrP : ExtAgree ctx.self w.ext stP := ExtAgree_memOnly hAgr hEV
      have haddrP : stP.env.address = BitVec.ofNat 256 ctx.self := by
        rcases hMO with ⟨_, _, _, _, _, _, ha, _, _, _, _⟩
        exact ha.trans (ctxRel_address hctx)
      have hresp : resp = o (mkCallReq .staticcall (target.eval env) sel
          (args.map (·.eval env))) w.ext := by
        have hY := (toCalls_call o _ stP resp).mp hCallR
        have hign := hIgn (mkCallReq .staticcall (target.eval env) sel
            (args.map (·.eval env))) w.ext stP haddrP hAgrP
        rw [hreq] at hY
        exact hY.trans hign.symm
      have hcore_view :
          w.oracle.view (target.eval env) sel (args.map (·.eval env)) w.ext =
            if resp.success then abiWords resp.returndata else [0, 0] := by
        simp [hOr, Oracle.ofExt, hresp]
      have hmload : 32 ≤ resp.returndata.length →
          loadWord stCall.memory abiPtr = wordFrom resp.returndata 0 :=
        fun hlen =>
          finishCall_mload_ge32 .staticcall stP resp abiPtr (4 + 32 * args.length)
            abiPtr 32 hlen (by decide)
      have hR2 :=
        R_finishCall_static (resp := resp) (iOff := abiPtr)
          (iSz := 4 + 32 * args.length) (oOff := abiPtr) (oSz := 32)
          (R_memOnly hR hMO)
      have hAgr2 := ExtAgree_finishCall_noInstall (kind := .staticcall)
        (resp := resp) (iOff := abiPtr) (iSz := 4 + 32 * args.length)
        (oOff := abiPtr) (oSz := 32) hAgrP (Or.inr rfl)
      have hctx1 := ctxRel_finishCall (ctxRel_memOnly hctx hMO) .staticcall resp
        abiPtr (4 + 32 * args.length) abiPtr 32
      by_cases hSok' : suffixOk resp.flag ret stCall (!skipOkGuard true ret)
      · have ⟨hoS, hMOS, hEVS, hVeq⟩ := hSok hSok'
        rw [hoS]
        have hR3 := R_memOnly hR2 hMOS
        have hAgr3 := ExtAgree_memOnly hAgr2 hEVS
        have hctx2 := ctxRel_memOnly hctx1 hMOS
        let sval := suffixVal ret stCall
        let vNat := sval.toNat
        have hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w =
            .ok (vNat, w) := by
          simp [Op.denote]
          cases ret with
          | none =>
            simp [Tx.viewAsNat, Tx.run_map, run_view_eval, AbiRetType.decode, suffixVal, vNat, sval]
          | word =>
            have hp : wordRetPass stCall = true := by
              simpa [skipOkGuard] using hSok'.2
            have hflag : resp.flag ≠ 0 := by
              cases hSok'.1 with
              | inl hck => simp [skipOkGuard] at hck
              | inr hf => exact hf
            have hsucc : resp.success = true := (flag_ne_zero_iff resp).mp hflag
            have ⟨h32, h64⟩ := (wordRetPass_iff stCall).mp hp
            have h32r : 32 ≤ rdsNat resp.returndata := by simpa [stCall] using h32
            have h64r : rdsNat resp.returndata < 64 := by simpa [stCall] using h64
            have hAbi := decode_word_of_abi (bs := resp.returndata) ⟨h32r, h64r, rfl⟩
            have hmw := hmload (by
              simpa [stCall] using
                (rdsNat_ge32_length (bs := stCall.returndata) h32))
            simp [Tx.viewAsNat, run_view_eval, hcore_view, hsucc, hAbi, suffixVal, vNat, sval, hmw]
          | boolOpt =>
            have hflag : resp.flag ≠ 0 := by
              cases hSok'.1 with
              | inl hck => simp [skipOkGuard] at hck
              | inr hf => exact hf
            have hsucc : resp.success = true := (flag_ne_zero_iff resp).mp hflag
            have hp := hSok'.2
            simp [skipOkGuard, suffixOk] at hp
            simp [Tx.viewAsNat, Tx.run_map, run_view_eval, hcore_view, hsucc]
            cases hp with
            | inl hempty =>
              have hn0 : rdsNat stCall.returndata = 0 := by
                simpa [rdsNat] using congrArg BitVec.toNat hempty
              have hn0' : rdsNat resp.returndata = 0 := by simpa [stCall] using hn0
              have hAbi : AbiRetType.decode (α := Bool) (abiWords resp.returndata) =
                  some true := by
                simp [AbiRetType.decode, abiWords_zero hn0']
              have hempty' :
                  BitVec.ofNat 256 stCall.returndata.length = 0#256 := by
                simpa using hempty
              simp [hAbi, suffixVal_boolOpt_empty hempty', vNat, sval, Tx.boolBit]
              try exact ite_b2w_toNat _
            | inr hwp =>
              have ⟨h32, h64⟩ := (wordRetPass_iff stCall).mp hwp
              have h32r : 32 ≤ rdsNat resp.returndata := by simpa [stCall] using h32
              have h64r : rdsNat resp.returndata < 64 := by simpa [stCall] using h64
              have hmw := hmload (by
                simpa [stCall] using
                  (rdsNat_ge32_length (bs := stCall.returndata) h32))
              have hne : BitVec.ofNat 256 stCall.returndata.length ≠ 0 := by
                intro hz
                have : rdsNat stCall.returndata = 0 := by
                  simpa [rdsNat] using congrArg BitVec.toNat hz
                omega
              have hdec : decodeRet .boolOpt resp.returndata
                  (if wordFrom resp.returndata 0 = 0 then 0 else 1) :=
                .inr ⟨h32r, h64r, rfl⟩
              have ⟨hAbi, _⟩ := decode_boolOpt_of_abi hdec
              simp [hAbi, suffixVal_boolOpt_word hne hmw, vNat, sval,
                boolBit_of_wordFrom, ite_zero_b2w, ite_zero_decide, Tx.boolBit]
              try exact ite_b2w_toNat _
        simp [hrun]
        first | refine ⟨rfl, hR3, hAgr3, ?_, ?_⟩ | refine ⟨hR3, hAgr3, ?_, ?_⟩
        · intro hnone
          have hpreEq : pre = toVEnv tag env := by
            cases hassign with
            | inl h => exact h.2
            | inr h =>
              rw [hnone] at h
              cases h.1
          have hVS : VS = (extOk tag d, resp.flag) :: pre := by
            rw [hnone] at hVeq
            simpa using hVeq
          have hVeq' : restore pre VS = toVEnv tag env := by
            rw [hVS, hpreEq]
            exact restore_drop1
          exact ⟨hVeq', hVeq', henv, hR3, hctx2⟩
        · intro hsome
          have ⟨name, hname⟩ : ∃ n, assign = some n := Option.isSome_iff_exists.mp hsome
          have hpreEq : pre = (identV tag d, (0 : U256)) :: toVEnv tag env := by
            cases hassign with
            | inl h =>
              have : none = some name := h.1.symm.trans hname
              cases this
            | inr h =>
              cases hname
              exact h.2
          have hname' : name = identV tag d := by
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
              VEnv.set ((extOk tag d, resp.flag) ::
                  (identV tag d, (0 : U256)) :: toVEnv tag env)
                (identV tag d) sval =
              (extOk tag d, resp.flag) ::
                (identV tag d, sval) :: toVEnv tag env := by
            rw [VEnv.set_cons_ne_open (identV_ne_extOk tag d d).symm,
              VEnv.set_head_open]
          have hVeq' : restore pre VS = toVEnv tag (vNat :: env) := by
            rw [hname] at hVeq
            rw [hVeq, hpreEq]
            simp [sval, stCall, vNat]
            rw [VEnv.set_cons_ne_open (identV_ne_extOk tag d d).symm,
              VEnv.set_head_open, restore_call_assign, toVEnv_cons_u256]
          exact ⟨hVeq', hVeq', envWF_cons (u256_lt_word sval) henv, hR3, hctx2⟩
      · have ⟨hoS, _, hh⟩ := hSfail hSok'
        have hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w =
            .error .callFailed := by
          simp [Op.denote]
          cases ret with
          | none =>
            exact (hSok' ⟨Or.inl (by simp [skipOkGuard]), trivial⟩).elim
          | word =>
            erw [Tx.viewAsNat, run_view_eval]
            by_cases hsucc : resp.success = true
            · simp [hcore_view, hsucc]
              have hp : ¬ (32 ≤ rdsNat stCall.returndata ∧
                  rdsNat stCall.returndata < 64) := by
                intro hp
                have hwp : wordRetPass stCall = true := (wordRetPass_iff _).mpr hp
                have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
                exact hSok' ⟨Or.inr hflag, by simpa [skipOkGuard] using hwp⟩
              have hdec : AbiRetType.decode (α := Nat) (abiWords resp.returndata) = none := by
                simpa [stCall] using decode_nat_fail hp
              simp [hdec]
            · simp [hcore_view, show resp.success = false by simpa using hsucc,
                AbiRetType.decode]
          | boolOpt =>
            erw [Tx.viewAsNat, Tx.run_map, run_view_eval]
            by_cases hsucc : resp.success = true
            · simp [hcore_view, hsucc]
              have hempty : BitVec.ofNat 256 stCall.returndata.length ≠ 0 := by
                intro hz
                have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
                exact hSok' ⟨Or.inr hflag, by
                  simp [skipOkGuard, suffixOk]
                  exact .inl hz⟩
              have hp : ¬ (32 ≤ rdsNat stCall.returndata ∧
                  rdsNat stCall.returndata < 64) := by
                intro hp
                have hwp : wordRetPass stCall = true := (wordRetPass_iff _).mpr hp
                have hflag : resp.flag ≠ 0 := (flag_ne_zero_iff resp).mpr hsucc
                exact hSok' ⟨Or.inr hflag, by
                  simp [skipOkGuard, suffixOk]
                  exact .inr hwp⟩
              have hne : rdsNat stCall.returndata ≠ 0 := by
                intro hz
                apply hempty
                exact BitVec.eq_of_toNat_eq (by simpa [rdsNat] using hz)
              have hdec : AbiRetType.decode (α := Bool) (abiWords resp.returndata) = none := by
                simpa [stCall] using decode_bool_fail hne hp
              simp [hdec]
            · simp [hcore_view, show resp.success = false by simpa using hsucc,
                AbiRetType.decode]
        simp [hrun]
        first | exact ⟨hoS, hh, rfl⟩ | exact ⟨hoS, hh⟩

theorem op_sim_view_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag (env.length + 1) = true)
    (h : ExecStmts (yulD (toCalls o)) funs V st
      ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts V' st' out) :
    match Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok (v, w') =>
        out = .normal ∧ V' = toVEnv tag (v :: env) ∧
          Inv tag Γ c κ ctx w' (v :: env) V' st' ∧
          ExtAgree ctx.self w'.ext st' := by
  let d := env.length
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  rw [hVeq, emitLetOp_view_stmts] at h
  cases execStmts_cons_inv h with
  | inr hstop =>
    have ⟨ho, _, _⟩ := exec_let_lit_inv hstop.2
    exact (hstop.1 ho).elim
  | inl hlet =>
    obtain ⟨V1, st1, hdoLet, hblkStmts⟩ := hlet
    have ⟨_, hst1, hV1⟩ := exec_let_lit_inv hdoLet
    rw [hst1, hV1] at hblkStmts
    have hblkStmt : ExecStmt (yulD (toCalls o)) funs
        ((identV tag d, (0 : U256)) :: toVEnv tag env) st
        (.block (emitExtCallBody tag d target sel args ret true (some (identV tag d))))
        V' st' out :=
      execStmts_one hblkStmts
    have hpre : (identV tag d, (0 : U256)) :: toVEnv tag env =
        (identV tag env.length, (0 : U256)) :: toVEnv tag env := rfl
    have hbit := extView_block_bwd tag o hR hctx henv hAgr hOr hNR hfuns hwfCall hsel
      (.inr hpre) (.inr ⟨rfl, hpre⟩)
      (identsNodup_mono tag (Nat.le_succ _) hn) (fun _ => hn) hblkStmt
    cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | error e =>
      simpa [hrun] using hbit
    | ok p =>
      rcases p with ⟨v, w'⟩
      rw [hrun] at hbit
      rcases hbit with ⟨ho, -, hAgr', -, hImp⟩
      have ⟨hV', hInv⟩ := hImp (by simp)
      exact ⟨ho, hV', hInv, hAgr'⟩

theorem stmt_sim_view_bwd {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    (o : ExtOracle) {funs : FunEnv (yulD (toCalls o))}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true)
    (hsel : sel < 2 ^ 32)
    (hn : identsNodup tag env.length = true)
    (h : ExecStmts (yulD (toCalls o)) funs V st
      (emitStmt tag c {} env.length (.view target sel args ret)).stmts V' st' out) :
    match Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w with
    | .error e =>
        out = .halt ∧ st'.halted = some (.revert, []) ∧ e = .callFailed
    | .ok ((), w') =>
        out = .normal ∧ V' = toVEnv tag env ∧
          Inv tag Γ c κ ctx w' env V' st' ∧
          ExtAgree ctx.self w'.ext st' := by
  rcases hinv with ⟨hVeq, henv, hR, hctx⟩
  rw [hVeq, emitStmt_view_stmts] at h
  have hblkStmt : ExecStmt (yulD (toCalls o)) funs (toVEnv tag env) st
      (.block (emitExtCallBody tag env.length target sel args ret true none)) V' st' out :=
    execStmts_one h
  have hbit := extView_block_bwd tag o hR hctx henv hAgr hOr hNR hfuns hwfCall hsel
    (.inl rfl) (.inl ⟨rfl, rfl⟩) hn
    (fun hpre => by
      have := congrArg List.length hpre
      simp at this)
    hblkStmt
  rw [stmt_run_view]
  cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
  | error e =>
    simpa [hrun] using hbit
  | ok p =>
    rcases p with ⟨v, w'⟩
    rw [hrun] at hbit
    rcases hbit with ⟨ho, -, hAgr', hImp, -⟩
    have ⟨hV', hInv⟩ := hImp (by simp)
    exact ⟨ho, hV', hInv, hAgr'⟩

end Lsc.Compiler
