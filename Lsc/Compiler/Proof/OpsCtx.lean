import Lsc.Compiler.Proof.OpsToken

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
0-arg `log1` (Vault `Paused` / `Unpaused`).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem toNat_0_word : (BitVec.ofNat 256 0).toNat = 0 :=
  toNat_ofNat_of_lt zero_lt_wordBound

theorem emitLog1_nil (e : Emit) (topic : Nat) :
    (emitLog1 e topic []).stmts =
      e.stmts ++ [.exprStmt (bop Op.log1 [lit abiPtr, lit 0, lit topic])] := by
  simp [emitLog1, emitDo, Emit.push, Emit.stmts, bop]

theorem emitStmt_emit_nil (c : ContractDef) (e : Emit) (d ev : Nat)
    {ed : EventDef} (h : c.events[ev]? = some ed) :
    (emitStmt c e d (.emit ev [])).stmts =
      e.stmts ++ [.exprStmt (bop Op.log1 [lit abiPtr, lit 0, lit ed.topic0])] := by
  simp [emitStmt, h, emitLog1_nil]

theorem readBytes_zero' (mem : Nat → UInt8) (p : Nat) : readBytes mem p 0 = [] := by
  simp [readBytes]

theorem stmt_sim_emit0 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {ev : Nat}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hwf : stmtWF c (.emit ev []) = true) :
    let w' := { w with log := w.log ++ [Γ.ev.build ev []] }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.emit ev [])).stmts
        V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  have ⟨ed, hed, _⟩ := (eventOK_iff c ev 0).mp (by simpa [stmtWF] using hwf)
  have hev : ev < c.events.length := (List.getElem?_eq_some_iff.mp hed).1
  have hstatic := ctxRel_static hctx
  let stL := appendLog st [BitVec.ofNat 256 ed.topic0]
    (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 0)
  have hlog :
      ExecStmt evm funs V st
        (.exprStmt (bop Op.log1 [lit abiPtr, lit 0, lit ed.topic0])) V stL .normal :=
    Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) Step.lit)
      (by simp only [litValue, step_log1 st _ _ _ hstatic]; rfl))
  refine ⟨stL, ?_, ?_⟩
  · simp only [emitStmt_emit_nil (h := hed), Emit.stmts_nil, List.nil_append]
    exact Step.seqCons hlog Step.seqNil
  · have hR' : R c Γ κ { w with log := w.log ++ [Γ.ev.build ev []] } stL := by
      rcases hR with ⟨hs, hl, hk, hW⟩
      have hl' := logsRel_emit (c := c) (Γ := Γ) (st := st) (args := []) hl hev
      have hdata : readBytes st.memory abiPtr 0 = abiBytes ([] : List Nat) := by
        simp [abiBytes, readBytes_zero']
      have hptr := toNat_abiPtr
      have hn0 := toNat_0_word
      have : stL.logs = st.logs ++
          [LogEntry.mk st.env.address [BitVec.ofNat 256 ed.topic0]
            (readBytes st.memory abiPtr 0)] := by
        simp [stL, appendLog, hptr, hn0]
      have haddr : stL.env.address = st.env.address := by
        simp [stL, appendLog, touchMemory]
      refine ⟨?_, ?_, ?_, hW⟩
      · simpa [stL, appendLog, touchMemory] using hs
      · unfold logsRel at hl' ⊢
        have hget : c.events[ev] = ed := (List.getElem?_eq_some_iff.mp hed).2
        simpa [this, haddr, hdata, hget, touchMemory] using hl'
      · simpa [stL, appendLog, touchMemory] using hk
    exact ⟨hV, henv, hR',
      ctxRel_appendLog hctx [BitVec.ofNat 256 ed.topic0]
        (BitVec.ofNat 256 abiPtr) (BitVec.ofNat 256 0)⟩

end Lsc.Compiler
