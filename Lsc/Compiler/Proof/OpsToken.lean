import Lsc.Compiler.Proof.Maps2
import Lsc.Compiler.Proof.OpsMore

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Token-fragment simulation: context words, 3-word `log1`, 0-arg `revert`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc (Stmt Tx Core Err RetTy Atom)

theorem step_caller (st : EvmState) :
    stepOp Op.caller [] st = some (.ok [st.env.caller] st) := rfl

theorem step_address (st : EvmState) :
    stepOp Op.address [] st = some (.ok [st.env.address] st) := rfl

theorem step_callvalue (st : EvmState) :
    stepOp Op.callvalue [] st = some (.ok [st.env.callvalue] st) := rfl

theorem step_timestamp (st : EvmState) :
    stepOp YulSemantics.EVM.Op.timestamp [] st = some (.ok [st.env.timestamp] st) := rfl

theorem step_number (st : EvmState) :
    stepOp Op.number [] st = some (.ok [st.env.number] st) := rfl

theorem toNat_96 : (BitVec.ofNat 256 96).toNat = 96 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_abiPtr32 : (BitVec.ofNat 256 (abiPtr + 32)).toNat = abiPtr + 32 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem toNat_abiPtr64 : (BitVec.ofNat 256 (abiPtr + 64)).toNat = abiPtr + 64 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem op_sim_nullary {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (op : YOp) (v : Nat) (hv : v < wordBound)
    (he : EvalExpr evm funs V st (bop op []) (.vals [BitVec.ofNat 256 v] st)) :
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop op [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  refine ⟨st, ?_, ⟨by rw [hV, toVEnv_cons], envWF_cons hv henv, hR, hctx⟩⟩
  simp only [emitLet_stmts, Emit.stmts_nil, List.nil_append]
  exact Step.seqCons (Step.letVal he rfl) Step.seqNil

theorem op_sim_sender {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st) :
    let v := ctx.sender
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop Op.caller [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv.ctxr with ⟨hc, _, _, _, _, _, _, _, ⟨hs, _⟩⟩
  refine op_sim_nullary funs hinv Op.caller ctx.sender hs ?_
  refine Step.builtinOk Step.argsNil ?_
  simp only [step_caller, hc]

theorem op_sim_value {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st) :
    let v := ctx.value
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop Op.callvalue [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv.ctxr with ⟨_, hv, _, _, _, _, _, _, ⟨_, hval, _⟩⟩
  refine op_sim_nullary funs hinv Op.callvalue ctx.value hval ?_
  refine Step.builtinOk Step.argsNil ?_
  simp only [step_callvalue, hv]

theorem op_sim_timestamp {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st) :
    let v := ctx.timestamp
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop YulSemantics.EVM.Op.timestamp [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv.ctxr with ⟨_, _, ht, _, _, _, _, _, ⟨_, _, hts, _⟩⟩
  refine op_sim_nullary funs hinv YulSemantics.EVM.Op.timestamp ctx.timestamp hts ?_
  refine Step.builtinOk Step.argsNil ?_
  simp only [step_timestamp, ht]

theorem op_sim_blockNumber {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st) :
    let v := ctx.blockNumber
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop Op.number [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv.ctxr with ⟨_, _, _, hn, _, _, _, _, ⟨_, _, _, hbn, _⟩⟩
  refine op_sim_nullary funs hinv Op.number ctx.blockNumber hbn ?_
  refine Step.builtinOk Step.argsNil ?_
  simp only [step_number, hn]

theorem op_sim_selfAddress {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st) :
    let v := ctx.self
    ∃ st',
      ExecStmts evm funs V st
        (emitLet {} (identV env.length) (bop Op.address [])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv.ctxr with ⟨_, _, _, _, ha, _, _, _, ⟨_, _, _, _, hs⟩⟩
  refine op_sim_nullary funs hinv Op.address ctx.self hs ?_
  refine Step.builtinOk Step.argsNil ?_
  simp only [step_address, ha]

theorem emitLog1_three (e : Emit) (topic : Nat) (a b c : YExpr) :
    (emitLog1 e topic [a, b, c]).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, a]),
          .exprStmt (bop Op.mstore [lit (abiPtr + 32), b]),
          .exprStmt (bop Op.mstore [lit (abiPtr + 64), c]),
          .exprStmt (bop Op.log1 [lit abiPtr, lit 96, lit topic])] := by
  simp [emitLog1, emitDo, Emit.push, Emit.stmts, bop]

theorem emitStmt_emit_three (c : ContractDef) (e : Emit) (d ev : Nat) (a b c' : Atom)
    {ed : EventDef} (h : c.events[ev]? = some ed) :
    (emitStmt c e d (.emit ev [a, b, c'])).stmts =
      e.stmts ++
        [.exprStmt (bop Op.mstore [lit abiPtr, atomE d a]),
          .exprStmt (bop Op.mstore [lit (abiPtr + 32), atomE d b]),
          .exprStmt (bop Op.mstore [lit (abiPtr + 64), atomE d c']),
          .exprStmt (bop Op.log1 [lit abiPtr, lit 96, lit ed.topic0])] := by
  simp [emitStmt, h, emitLog1_three]

theorem readBytes_abi_three (mem : Nat → UInt8) (n0 n1 n2 : Nat)
    (h0 : n0 < wordBound) (h1 : n1 < wordBound) (h2 : n2 < wordBound) :
    readBytes
      (storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
        (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2))
      abiPtr 96 = wordBytes n0 ++ wordBytes n1 ++ wordBytes n2 := by
  have h96 : (96 : Nat) = 32 + (32 + 32) := rfl
  rw [h96, readBytes_split, readBytes_split, ← List.append_assoc]
  have h2' :
      readBytes (storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2))
        (abiPtr + 64) 32 = wordBytes n2 :=
    readBytes_storeWord_wordBytes _ _ _ h2
  have h1' :
      readBytes (storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2))
        (abiPtr + 32) 32 = wordBytes n1 := by
    have hout64 : ∀ i ∈ List.range 32,
        storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
            (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2)
          (abiPtr + 32 + i) =
          storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
            (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + 32 + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      exact storeWord_out _ _ _ _ (.inl (by simp only [abiPtr]; omega))
    have hout0 : ∀ i ∈ List.range 32,
        storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + 32 + i) =
          storeWord mem (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + 32 + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      have hin : abiPtr + 32 ≤ abiPtr + 32 + i ∧ abiPtr + 32 + i < abiPtr + 32 + 32 := by omega
      rw [storeWord_in (h := hin), storeWord_in (h := hin)]
    unfold readBytes
    refine Eq.trans (List.map_congr_left hout64)
      (Eq.trans (List.map_congr_left hout0) ?_)
    change readBytes (storeWord mem (abiPtr + 32) (BitVec.ofNat 256 n1))
      (abiPtr + 32) 32 = wordBytes n1
    exact readBytes_storeWord_wordBytes _ _ _ h1
  have h0' :
      readBytes (storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2))
        abiPtr 32 = wordBytes n0 := by
    have hout64 : ∀ i ∈ List.range 32,
        storeWord (storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
            (abiPtr + 32) (BitVec.ofNat 256 n1)) (abiPtr + 64) (BitVec.ofNat 256 n2)
          (abiPtr + i) =
          storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
            (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      exact storeWord_out _ _ _ _ (.inl (by simp only [abiPtr]; omega))
    have hout32 : ∀ i ∈ List.range 32,
        storeWord (storeWord mem abiPtr (BitVec.ofNat 256 n0))
          (abiPtr + 32) (BitVec.ofNat 256 n1) (abiPtr + i) =
          storeWord mem abiPtr (BitVec.ofNat 256 n0) (abiPtr + i) := by
      intro i hi
      have : i < 32 := List.mem_range.mp hi
      exact storeWord_out _ _ _ _ (.inl (by simp only [abiPtr]; omega))
    unfold readBytes
    refine Eq.trans (List.map_congr_left hout64)
      (Eq.trans (List.map_congr_left hout32) ?_)
    change readBytes (storeWord mem abiPtr (BitVec.ofNat 256 n0)) abiPtr 32 = wordBytes n0
    exact readBytes_storeWord_wordBytes _ _ _ h0
  rw [h0', h1', h2']

theorem stmt_sim_emit3 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {ev : Nat} {a b c' : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : stmtWF c (.emit ev [a, b, c']) = true)
    (hn : identsNodup env.length = true) :
    let args := [a.eval env, b.eval env, c'.eval env]
    let w' := { w with log := w.log ++ [Γ.ev.build ev args] }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.emit ev [a, b, c'])).stmts
        V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have hwf' : eventOK c ev 3 = true ∧
      atomWF a = true ∧ atomWF b = true ∧ atomWF c' = true := by
    simpa [stmtWF, Bool.and_eq_true, List.all_cons, List.all_nil] using hwf
  have ⟨ed, hed, _⟩ := (eventOK_iff c ev 3).mp hwf'.1
  have hev : ev < c.events.length := (List.getElem?_eq_some_iff.mp hed).1
  have ha := atom_eval_lt henv hwf'.2.1
  have hb := atom_eval_lt henv hwf'.2.2.1
  have hc := atom_eval_lt henv hwf'.2.2.2
  have hstatic := ctxRel_static hctx
  have hea := eval_atom funs (st := st) hV hn a
  let st0 :=
    { touchMemory st abiPtr 32 with
      memory := storeWord st.memory abiPtr (BitVec.ofNat 256 (a.eval env)) }
  have heb := eval_atom funs (st := st0) hV hn b
  let st1 :=
    { touchMemory st0 (abiPtr + 32) 32 with
      memory := storeWord st0.memory (abiPtr + 32) (BitVec.ofNat 256 (b.eval env)) }
  have hec := eval_atom funs (st := st1) hV hn c'
  let st2 :=
    { touchMemory st1 (abiPtr + 64) 32 with
      memory := storeWord st1.memory (abiPtr + 64) (BitVec.ofNat 256 (c'.eval env)) }
  have hm0 :
      ExecStmt evm funs V st
        (.exprStmt (bop Op.mstore [lit abiPtr, atomE env.length a])) V st0 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hea) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, toNat_abiPtr]; rfl))
  have hm1 :
      ExecStmt evm funs V st0
        (.exprStmt (bop Op.mstore [lit (abiPtr + 32), atomE env.length b])) V st1 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heb) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, toNat_abiPtr32]; rfl))
  have hm2 :
      ExecStmt evm funs V st1
        (.exprStmt (bop Op.mstore [lit (abiPtr + 64), atomE env.length c'])) V st2 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hec) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, toNat_abiPtr64]; rfl))
  let stL := appendLog st2 [BitVec.ofNat 256 ed.topic0]
    (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 96)
  have hstatic2 : st2.env.static = false := by
    simp [st2, st1, st0, touchMemory, hstatic]
  have hlog :
      ExecStmt evm funs V st2
        (.exprStmt (bop Op.log1 [lit abiPtr, lit 96, lit ed.topic0])) V stL .normal :=
    Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) Step.lit)
      (by simp only [litValue, step_log1 st2 _ _ _ hstatic2]; rfl))
  refine ⟨stL, ?_, ?_⟩
  · simp only [emitStmt_emit_three (h := hed), Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hm0 (Step.seqCons hm1 (Step.seqCons hm2 (Step.seqCons hlog Step.seqNil)))
  · have hR' : R c Γ κ
        { w with log := w.log ++ [Γ.ev.build ev [a.eval env, b.eval env, c'.eval env]] } stL := by
      rcases hR with ⟨hs, hl, hk, hW⟩
      have hl' := logsRel_emit (c := c) (Γ := Γ) (st := st2)
        (args := [a.eval env, b.eval env, c'.eval env])
        (by
          unfold logsRel at hl ⊢
          simp [st2, st1, st0, touchMemory]
          exact hl) hev
      have hdata :
          readBytes st2.memory abiPtr 96 =
            abiBytes [a.eval env, b.eval env, c'.eval env] := by
        simp [st2, st1, st0, abiBytes, readBytes_abi_three _ _ _ _ ha hb hc]
      have hptr := toNat_abiPtr
      have hn96 := toNat_96
      have : stL.logs = st2.logs ++
          [LogEntry.mk st2.env.address [BitVec.ofNat 256 ed.topic0]
            (readBytes st2.memory abiPtr 96)] := by
        simp [stL, appendLog, hptr, hn96]
      have haddr : stL.env.address = st2.env.address := by
        simp [stL, appendLog, touchMemory]
      refine ⟨?_, ?_, ?_, hW⟩
      · simpa [stL, appendLog, touchMemory, st2, st1, st0] using hs
      · unfold logsRel at hl' ⊢
        have hget : c.events[ev] = ed := (List.getElem?_eq_some_iff.mp hed).2
        simpa [this, haddr, hdata, st2, st1, st0, touchMemory, hget] using hl'
      · simpa [stL, appendLog, touchMemory, st2, st1, st0] using hk
    exact ⟨hV, henv, hR',
      ctxRel_appendLog (st := st2)
        (ctxRel_memOnly hctx (by simp [MemOnly, st2, st1, st0, touchMemory]))
        [BitVec.ofNat 256 ed.topic0]
        (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 96)⟩

theorem emitStmt_revert_nil (c : ContractDef) (e : Emit) (d err : Nat) {ed : ErrorDef}
    (h : c.errors[err]? = some ed) :
    (emitStmt c e d (.revert err [])).stmts =
      e.stmts ++ (emitCustomError c {} err []).stmts := by
  rw [show emitStmt c e d (.revert err []) = emitCustomError c e err [] from rfl]
  rw [emitCustomError_acc, Emit.cat_stmts]

theorem stmt_sim_revert {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {err : Nat}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : stmtWF c (.revert err []) = true) :
    match Tx.run (Stmt.denote Γ env (.revert err [])) ctx w with
    | .ok (_, w') =>
        ∃ st', ExecStmts evm funs V st (emitStmt c {} env.length (.revert err [])).stmts
          V st' .normal ∧ Inv Γ c κ ctx w' env V st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st (emitStmt c {} env.length (.revert err [])).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have ⟨ed, hed, _⟩ := (errorOK_iff c err 0).mp (by simpa [stmtWF, Bool.and_eq_true] using hwf)
  simp [Stmt.denote, Tx.run_revert]
  obtain ⟨st', hp, hh⟩ := customError_nil_sim funs V st c err hed
  refine ⟨V, st', ?_, selectorBytes ed.selector, hh, ?_⟩
  · simpa [emitStmt_revert_nil (h := hed), Emit.stmts_nil] using hp
  · exact ⟨err, [], rfl, (customErrorBytes_nil c hed).symm⟩

theorem revertTail_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {err : Nat} {t : RetTy}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : coreWF c (Core.revertTail (t := t) err []) = true) :
    ∃ V' st' bytes,
      ExecStmts evm funs V st (emitCustomError c {} err []).stmts V' st' .halt ∧
        st'.halted = some (.revert, bytes) ∧
        haltError c Γ (Err.user (Γ.err.build err [])) bytes := by
  have ⟨ed, hed, _⟩ := (errorOK_iff c err 0).mp (by simpa [coreWF] using hwf)
  obtain ⟨st', hp, hh⟩ := customError_nil_sim funs V st c err hed
  exact ⟨V, st', selectorBytes ed.selector, hp, hh,
    ⟨err, [], rfl, (customErrorBytes_nil c hed).symm⟩⟩

end Lsc.Compiler
