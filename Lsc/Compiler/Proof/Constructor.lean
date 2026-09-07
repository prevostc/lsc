import Lsc.Compiler.Proof.ConstructorPrologue

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Constructor emission (`toYulCtor`): Solidity CREATE args are the suffix of `env.code`.
S1 / `CallFree` / `NoIte`. Vault constructors with `call` are out of scope.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

/-- Cores without `ite` (Token constructor). Avoids a `.normal` switch lemma. -/
def NoIte : {t : RetTy} → Core t → Prop
  | _, .ite .. => False
  | _, .letOp _ k => NoIte k
  | _, .seq _ k => NoIte k
  | _, .letPure _ _ k => NoIte k
  | _, _ => True

theorem emitReturnUnit_false (e : Emit) : emitReturnUnit e false = e := rfl


theorem core_sim_ctor {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx}
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core) (hNo : NoIte core) (ht : t = .unit) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv evm)
      (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st)
      {e' : Emit} (hem : emitCore c {} env.length false core = some e'),
      match Tx.run (Core.denote Γ core env) ctx w with
      | .ok (_, w') =>
          ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .normal ∧
            R c Γ κ w' st' ∧ st'.halted = none
      | .error e =>
          ∃ V' st' bytes,
            ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  revert ht hNo hM1
  induction core with
  | ret r =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    cases r with
    | unit =>
      simp only [emitCore, emitRet, emitReturnUnit_false, Emit.stmts_nil] at hem
      cases hem
      rw [Core.denote, Tx.run_pure]
      exact ⟨V, st, Step.seqNil, hinv.rel, ctxRel_halted hinv.ctxr⟩
    | word _ | addr _ | flag _ | pair _ _ => cases ht
  | opTail _ | opTailAddr _ | opTailFlag _ =>
    intro hM1 hNo ht
    cases ht
  | stmtTail s =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    simp only [emitCore, emitReturnUnit_false] at hem
    cases hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hsim := stmt_sim funs hinv hΓ hκ hlen (show M1Stmt s by simpa [M1Frag] using hM1)
      (show stmtWF c s = true by simpa [coreWF] using hwf) hn0
    cases hrun : Tx.run (Core.denote Γ (.stmtTail s) env) ctx w with
    | ok p =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      simp only [except_ok_prod]
      exact ⟨V, st1, hexec, hinv1.rel, ctxRel_halted hinv1.ctxr⟩
    | error err =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      exact ⟨V', st', bytes, hexec, hh, herr⟩
  | letOp op k ih =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    cases hE : emitLetOp c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        have ih' := ih hk hNo ht funs hkWF (by simpa using hnK) hinv1 h0
        cases hK : Tx.run (Core.denote Γ k (p.1 :: env)) ctx p.2 with
        | ok q =>
          rw [hK] at ih'
          obtain ⟨V', st', hexeck, hR, hh⟩ := ih'
          rcases p with ⟨v, w'⟩
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod, hK]
          refine ⟨V', st', ?_, hR, hh⟩
          rw [hst]
          exact execStmts_append hexec hexeck
        | error err =>
          rw [hK] at ih'
          obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
          rcases p with ⟨v, w'⟩
          simp only [except_ok_prod, hK, except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append hexec hexeck
      | error err =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append_halt hexec
  | seq s k ih =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hnK : identsNodup (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
    | ok p =>
      have hsim := stmt_sim funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      have ih' := ih hk hNo ht funs hkWF hnK hinv1 h0
      cases hK : Tx.run (Core.denote Γ k env) ctx p.2 with
      | ok q =>
        rw [hK] at ih'
        obtain ⟨V', st', hexeck, hR, hh⟩ := ih'
        rcases p with ⟨u, w'⟩
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod, hK]
        refine ⟨V', st', ?_, hR, hh⟩
        rw [hst]
        exact execStmts_append hexec hexeck
      | error err =>
        rw [hK] at ih'
        obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
        rcases p with ⟨u, w'⟩
        simp only [except_ok_prod, hK, except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append hexec hexeck
    | error err =>
      have hsim := stmt_sim funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      exact execStmts_append_halt hexec
  | letPure p args k ih =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    have ⟨hp, hargs, hk⟩ := m1frag_letPure.mp hM1
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hn1 : identsNodup (env.length + 1) = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom funs (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt evm funs V st
          (.letDecl [identV env.length] (some (atomE env.length a)))
          ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal he rfl
    have hinv1 : Inv Γ c κ ctx w (a.eval env :: env)
        ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have ih' := ih hk hNo ht funs hkWF (by simpa using hnK) hinv1 h0
    cases hK : Tx.run (Core.denote Γ k (a.eval env :: env)) ctx w with
    | ok q =>
      rw [hK] at ih'
      obtain ⟨V', st', hexeck, hR, hh⟩ := ih'
      rcases q with ⟨r, w''⟩
      simp only [except_ok_prod]
      refine ⟨V', st', ?_, hR, hh⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
    | error err =>
      rw [hK] at ih'
      obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
  | ite _ _ _ =>
    intro hM1 hNo ht
    exact (show False from hNo).elim
  | revertTail err args =>
    intro hM1 hNo ht w env V st funs hwf hn hinv e' hem
    have hnil : args.length = 0 := by simpa [M1Frag] using hM1
    match args with
    | _ :: _ => cases hnil
    | [] =>
      simp only [emitCore] at hem
      cases hem
      simp only [Core.denote, Tx.run_revert]
      exact revertTail_sim funs hinv hwf

theorem toYulCtor_inv {c f yul} (h : toYulCtor c f = some yul) :
    coreWF c f.core = true ∧
    identsNodup (maxDepth f) = true ∧
    ∃ e, emitCore c (emitCtorParams {} f.params.length) f.params.length false f.core
        = some e ∧ yul = e.stmts := by
  unfold toYulCtor at h
  have hwfB : coreWF c f.core = true := by
    by_contra hne
    have : (!coreWF c f.core) = true := by
      cases hcore : coreWF c f.core
      · rfl
      · exact (hne hcore).elim
    simp [this] at h
  have hnodB : identsNodup (maxDepth f) = true := by
    by_contra hne
    have : (!identsNodup (maxDepth f)) = true := by
      cases hnd : identsNodup (maxDepth f)
      · rfl
      · exact (hne hnd).elim
    simp [hwfB, this] at h
  simp [hwfB, hnodB] at h
  obtain ⟨e, hem⟩ := emitCore_some (c := c) (halt := false) f.core
    (emitCtorParams {} f.params.length) f.params.length
  simp [hem] at h
  exact ⟨hwfB, hnodB, e, hem, by cases h; rfl⟩

theorem toYulCtor_hoist {c f yul} (h : toYulCtor c f = some yul) :
    hoist evm yul = [] := by
  have ⟨_, _, e, hem, hy⟩ := toYulCtor_inv h
  subst hy
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  rw [hst, hoist_append, hoist_ctorParams, hoist_emitCore h0]
  simp

theorem constructor_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hk : f.kind = .constructor) (hret : f.ret = .unit)
    (hM1 : CallFree f.core) (hNo : NoIte f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : 32 * f.params.length < wordBound)
    (hptr : abiPtr + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulCtor c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hle : 32 * f.params.length ≤ st0.env.code.length)
    (hcode : st0.env.code.length < wordBound) :
    ConstructorCorrect c Γ κ f yul ctx w st0 := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulCtor_inv hyul
  subst hy
  set args := decodeCtorArgs f.params.length st0.env.code
  have henv : EnvWF args.reverse := decodeCtorArgs_wf f.params.length st0.env.code
  obtain ⟨stP, hMO, hpar⟩ := params_sim_ctor (funs := ([[]] : FunEnv evm)) st0
    f.params.length hle hcode hptr
  have hinv : Inv Γ c κ ctx w args.reverse (toVEnv args.reverse) stP :=
    ⟨rfl, henv, R_memOnly hR hMO, ctxRel_memOnly hctx hMO⟩
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  have hn : identsNodup (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeCtorArgs_length, List.length_reverse] using hn
  have h0' : emitCore c {} args.reverse.length false f.core = some e0 := by
    simpa [args, decodeCtorArgs_length, List.length_reverse] using h0
  have hsim := core_sim_ctor (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) hΓ hκ hlen
    f.core hM1 hNo hret (funs := [[]]) hwf hn' hinv h0'
  have hhoist := toYulCtor_hoist hyul
  simp only [ConstructorCorrect]
  cases hrun : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hsim ⊢
    obtain ⟨V', st', hexec, hR', hh⟩ := hsim
    rcases p with ⟨v, w'⟩
    refine ⟨st', ?_, hR'⟩
    have hbody := execStmts_append hpar hexec
    have hblock := Step.block (D := evm) (by
      rw [hhoist, hst]
      exact hbody)
    rwa [restore_nil] at hblock
  | error err =>
    simp only [hrun, except_error_prod] at hsim ⊢
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    refine ⟨st', bytes, ?_, hh, herr, hR⟩
    have hblock := Step.block (D := evm) (by
      rw [hhoist, hst]
      exact execStmts_append hpar hexec)
    rwa [restore_nil] at hblock

theorem eval_datasize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : YIdent) :
    EvalExpr evm funs V st
      (bop Op.datasize [YulSemantics.Expr.lit (YulSemantics.Literal.string n)])
      (.vals [st.env.dataSize (litValue (.string n))] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) (by simp [step_datasize])

theorem eval_dataoffset (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : YIdent) :
    EvalExpr evm funs V st
      (bop Op.dataoffset [YulSemantics.Expr.lit (YulSemantics.Literal.string n)])
      (.vals [st.env.dataOffset (litValue (.string n))] st) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) (by simp [step_dataoffset])

theorem readBytes_copyInto (mem : Nat → UInt8) (src n : Nat) (code : List UInt8) :
    readBytes (copyInto mem 0 src n code) 0 n = readBytes (byteFrom code) src n := by
  simp only [readBytes]
  refine List.map_congr_left ?_
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  have hin : 0 ≤ i ∧ i < n := by omega
  simp only [copyInto, Nat.zero_add]
  rw [if_pos hin, Nat.sub_zero]

theorem run_of_execStmts {prog st0 st' o}
    (hh : hoist evm prog = [])
    (h : ExecStmts evm [[]] [] st0 prog [] st' o) :
    Run evm prog st0 [] st' o := by
  have hb := Step.block (D := evm) (by rwa [hh])
  rw [restore_nil] at hb
  exact hb

theorem hoist_constructorCode (n : YIdent) :
    hoist evm (constructorCode n) = [] := by
  simp [constructorCode, hoist]

theorem constructorCode_run (st0 : EvmState) (n : YIdent) :
    ∃ st, Run evm (constructorCode n) st0 [] st .halt ∧
      st.halted = some (.ret,
        readBytes (byteFrom st0.env.code)
          (st0.env.dataOffset (litValue (.string n))).toNat
          (st0.env.dataSize (litValue (.string n))).toNat) := by
  set off := st0.env.dataOffset (litValue (.string n))
  set sz := st0.env.dataSize (litValue (.string n))
  let stC : EvmState :=
    { touchMemory st0 0 sz.toNat with
      memory := copyInto st0.memory 0 off.toNat sz.toNat st0.env.code }
  let stH : EvmState :=
    { touchMemory stC 0 sz.toNat with
      halted := some (.ret, readBytes stC.memory 0 sz.toNat) }
  have h0 : (BitVec.ofNat 256 0).toNat = 0 := toNat_ofNat_of_lt (by simp [wordBound])
  have hdc :
      EvalExpr evm [[]] [] st0
        (bop Op.datacopy
          [lit 0,
            bop Op.dataoffset [YulSemantics.Expr.lit (YulSemantics.Literal.string n)],
            bop Op.datasize [YulSemantics.Expr.lit (YulSemantics.Literal.string n)]])
        (.vals [] stC) := by
    refine Step.builtinOk
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons Step.argsNil (eval_datasize [[]] [] st0 n))
          (eval_dataoffset [[]] [] st0 n))
        Step.lit) ?_
    simp only [litValue_number, step_datacopy, stC, off, sz, h0]
  have hretE :
      EvalExpr evm [[]] [] stC
        (bop Op.ret [lit 0, bop Op.datasize [YulSemantics.Expr.lit (YulSemantics.Literal.string n)]])
        (.halt stH) := by
    refine Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil (eval_datasize [[]] [] stC n)) Step.lit) ?_
    have hsz : stC.env.dataSize (litValue (.string n)) = sz := by
      simp [stC, touchMemory, sz]
    simp only [litValue_number, step_ret, h0, hsz]
    rfl
  have hexec : ExecStmts evm [[]] [] st0 (constructorCode n) [] stH .halt :=
    Step.seqCons (Step.exprStmt hdc)
      (Step.seqStop (Step.exprStmtHalt hretE) halt_ne_normal)
  refine ⟨stH, run_of_execStmts (hoist_constructorCode n) hexec, ?_⟩
  simp [stH, stC, off, sz, touchMemory, readBytes_copyInto]

/-- Init block = constructor body ++ `constructorCode "runtime"`. Success: body
falls through, then the object constructor returns the layout's `"runtime"` slice. -/
theorem deployBlock_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hctor : c.ctor = some f)
    (hk : f.kind = .constructor) (hret : f.ret = .unit)
    (hM1 : CallFree f.core) (hNo : NoIte f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : 32 * f.params.length < wordBound)
    (hptr : abiPtr + 32 * f.params.length < wordBound)
    (body : YBlock) (hbody : toYulCtor c f = some body)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hle : 32 * f.params.length ≤ st0.env.code.length)
    (hcode : st0.env.code.length < wordBound) :
    let yul := body ++ constructorCode "runtime"
    let args := decodeCtorArgs f.params.length st0.env.code
    match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
    | .ok (_, w') =>
        ∃ st1 st2,
          Run evm body st0 [] st1 .normal ∧ R c Γ κ w' st1 ∧
          Run evm (constructorCode "runtime") st1 [] st2 .halt ∧
          st2.halted = some (.ret,
            readBytes (byteFrom st1.env.code)
              (st1.env.dataOffset (litValue (.string "runtime"))).toNat
              (st1.env.dataSize (litValue (.string "runtime"))).toNat)
    | .error e =>
        ∃ stObs bytes,
          Run evm body st0 [] stObs .halt ∧
          stObs.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes ∧ R c Γ κ w st0 := by
  have hC := constructor_correct c Γ hΓ κ hκ f hk hret hM1 hNo hlen hbound hptr
    body hbody ctx w st0 hctx hR hle hcode
  simp only [ConstructorCorrect] at hC
  cases hrun : Tx.run (Core.denote Γ f.core
      (decodeCtorArgs f.params.length st0.env.code).reverse) ctx w with
  | ok p =>
    simp only [hrun] at hC ⊢
    obtain ⟨st1, hRun, hR1⟩ := hC
    rcases p with ⟨_, w'⟩
    obtain ⟨st2, hRt, hh⟩ := constructorCode_run st1 "runtime"
    exact ⟨st1, st2, hRun, hR1, hRt, hh⟩
  | error e =>
    simp only [hrun] at hC ⊢
    obtain ⟨stObs, bytes, hRun, hh, herr, hR0⟩ := hC
    exact ⟨stObs, bytes, hRun, hh, herr, hR0⟩

end Lsc.Compiler

