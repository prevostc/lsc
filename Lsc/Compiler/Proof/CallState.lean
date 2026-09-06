import Lsc.Compiler.Proof.AbiCall
import Lsc.Compiler.Proof.Lift

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`R` after `finishCall`, and generic block/`restore` facts used by `op_sim_call_bwd`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem restore_nil_open {D : Dialect} (Vb : VEnv D) : restore ([] : VEnv D) Vb = [] := by
  simp [restore]

theorem restore_self_open {D : Dialect} (V : VEnv D) : restore V V = V := by
  simp [restore]

theorem restore_call_result {D : Dialect} {ok tok name : Ident}
    {f a v0 v : D.Value} {V : VEnv D} :
    restore ((name, v0) :: V)
      ((ok, f) :: (tok, a) :: (name, v) :: V) = (name, v) :: V := by
  simp [restore]

theorem restore_drop2 {D : Dialect} {x y : Ident} {vx vy : D.Value} {V : VEnv D} :
    restore V ((x, vx) :: (y, vy) :: V) = V := by
  simp [restore]
  have : V.length + 1 + 1 - V.length = 2 := by omega
  simp [this]

theorem exec_block_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {body : YulSemantics.Block D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmt D funs V st (.block body) V' st' o) :
    ∃ Vb, ExecStmts D (hoist D body :: funs) V st body Vb st' o ∧
      V' = restore V Vb := by
  cases h with
  | block hbody => exact ⟨_, hbody, rfl⟩

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

theorem RX_finishCall_fail {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} {w : World S X E} {st : EvmState}
    {resp : CallResponse} {iOff iSz oOff oSz : Nat}
    (h : RX α bind w st) (hf : resp.success = false) :
    RX α bind w (finishCall .call st resp iOff iSz oOff oSz) := by
  unfold RX at h ⊢
  rw [Abs.ofState_finishCall_fail (h := hf)]
  exact h

/-- After a successful CALL, the callee ghost is `g'` and other addresses are unchanged
(`NoInterfere`). `bind.set` updates only this ghost. -/
theorem RX_finishCall_success {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} {w : World S X E} {st : EvmState}
    {resp : CallResponse} {iOff iSz oOff oSz : Nat} {g' : I.Ghost}
    (hRX : RX α bind w st)
    (hs : resp.success = true)
    (hg : α.ofWorld resp.world (bind.addr w.self) = g')
    (hni : NoInterfere α st resp.world (bind.addr w.self))
    (hset : ∀ x g, bind.get (bind.set x g) = g) :
    RX α bind { w with ext := bind.set w.ext g' }
      (finishCall .call st resp iOff iSz oOff oSz) := by
  unfold RX
  rw [Abs.ofState_finishCall_success (hs := hs), hg, hset]

end Lsc.Compiler
