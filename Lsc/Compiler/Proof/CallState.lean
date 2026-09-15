import Lsc.Compiler.Proof.AbiCall
import Lsc.Compiler.Proof.Lift

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`R` after `finishCall`, restore after scoped `ok`, and `ExtAgree` facts
used by `op_sim_call_bwd`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem restore_self_open {D : Dialect} (V : VEnv D) : restore V V = V := by
  simp [restore]

theorem restore_drop1 {D : Dialect} {x : Ident} {vx : D.Value} {V : VEnv D} :
    restore V ((x, vx) :: V) = V := by
  simp [restore]

theorem restore_drop2 {D : Dialect} {x y : Ident} {vx vy : D.Value} {V : VEnv D} :
    restore V ((x, vx) :: (y, vy) :: V) = V := by
  simp [restore]
  have : V.length + 1 + 1 - V.length = 2 := by omega
  simp [this]

/-- After `let v := 0 { … v := r }` the block's `ok` temp is dropped. -/
theorem restore_call_assign {D : Dialect} {ok name : Ident}
    {f v0 v : D.Value} {V : VEnv D} :
    restore ((name, v0) :: V) ((ok, f) :: (name, v) :: V) = (name, v) :: V := by
  simp [restore]

theorem exec_block_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {body : YulSemantics.Block D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmt D funs V st (.block body) V' st' o) :
    ∃ Vb, ExecStmts D (hoist D body :: funs) V st body Vb st' o ∧
      V' = restore V Vb := by
  cases h with
  | block hbody => exact ⟨_, hbody, rfl⟩

theorem ExtView.ofState_touch (st : EvmState) (p n : Nat) :
    ExtView.ofState (touchMemory st p n) = ExtView.ofState st := by
  simp [ExtView.ofState, ExtState.ofState, touchMemory]

theorem ExtView.ofState_mstore (st : EvmState) (p : Nat) (v : U256) :
    ExtView.ofState
      { touchMemory st p 32 with memory := storeWord st.memory p v } =
      ExtView.ofState st := by
  simp [ExtView.ofState, ExtState.ofState, touchMemory]

theorem ExtAgree_of_scrub {self : Address} {x : Lsc.ExtState} {st st' : EvmState}
    (h : ExtAgree self x st)
    (hs : scrubSelf self (ExtView.ofState st') = scrubSelf self (ExtView.ofState st)) :
    ExtAgree self x st' := by
  unfold ExtAgree agreeExceptSelf at *
  exact h.trans hs.symm

theorem ExtAgree_touch {self : Address} {x : Lsc.ExtState} {st : EvmState}
    (h : ExtAgree self x st) (p n : Nat) :
    ExtAgree self x (touchMemory st p n) :=
  ExtAgree_of_scrub h (by rw [ExtView.ofState_touch])

theorem ExtAgree_memOnly {self : Address} {x : Lsc.ExtState} {st st' : EvmState}
    (h : ExtAgree self x st)
    (he : ExtView.ofState st' = ExtView.ofState st) :
    ExtAgree self x st' :=
  ExtAgree_of_scrub h (by rw [he])

/-- Successful CALL: `R` is restored because the callee did not write our
storage or emit logs as `self` (`NoReentry.noInterfere`). -/
theorem R_finishCall_success {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} {resp : CallResponse}
    {iOff iSz oOff oSz : Nat}
    (hR : R c Γ κ w st) (hs : resp.success = true)
    (hσ : resp.world.storage = st.storage)
    (hlogs : ∀ l ∈ resp.world.logs, l.address ≠ st.env.address) :
    R c Γ κ w (finishCall .call st resp iOff iSz oOff oSz) := by
  rcases hR with ⟨hsto, hl, hk, hwf⟩
  refine ⟨?_, ?_, ?_, hwf⟩
  · rw [finishCall_storage_success_eq (hs := hs), hσ]; exact hsto
  · unfold logsRel
    rw [selfLogs_finishCall_success hs hlogs, finishCall_address]
    exact hl
  · rw [finishCall_keccak, hk]

theorem finishCall_storage_static (st : EvmState) (resp : CallResponse)
    (iOff iSz oOff oSz : Nat) :
    (finishCall .staticcall st resp iOff iSz oOff oSz).storage = st.storage := by
  simp [finishCall, touchMemory2, touchMemory]

theorem finishCall_logs_static (st : EvmState) (resp : CallResponse)
    (iOff iSz oOff oSz : Nat) :
    (finishCall .staticcall st resp iOff iSz oOff oSz).logs = st.logs := by
  simp [finishCall, touchMemory2, touchMemory]

theorem selfLogs_finishCall_static (st : EvmState) (resp : CallResponse)
    (iOff iSz oOff oSz : Nat) :
    selfLogs (finishCall .staticcall st resp iOff iSz oOff oSz) = selfLogs st := by
  simp [selfLogs, finishCall_logs_static, finishCall_address]

theorem R_finishCall_static {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} {resp : CallResponse}
    {iOff iSz oOff oSz : Nat} (hR : R c Γ κ w st) :
    R c Γ κ w (finishCall .staticcall st resp iOff iSz oOff oSz) := by
  rcases hR with ⟨hsto, hl, hk, hwf⟩
  refine ⟨?_, ?_, ?_, hwf⟩
  · rw [finishCall_storage_static]; exact hsto
  · unfold logsRel
    rw [selfLogs_finishCall_static, finishCall_address]
    exact hl
  · rw [finishCall_keccak, hk]

/-- Frame fields that `scrubSelf` preserves (everything except `storageOf` /
`transientOf` at `self`). -/
theorem agreeExceptSelf_frame {self : Address} {x y : Lsc.ExtState}
    (h : agreeExceptSelf self x y) :
    x.env.address = y.env.address ∧
    x.env.origin = y.env.origin ∧
    x.env.caller = y.env.caller ∧
    x.env.callvalue = y.env.callvalue ∧
    x.env.gasprice = y.env.gasprice ∧
    x.env.createdThisTx = y.env.createdThisTx ∧
    x.env.static = y.env.static ∧
    x.env.coinbase = y.env.coinbase ∧
    x.env.timestamp = y.env.timestamp ∧
    x.env.number = y.env.number ∧
    x.env.prevrandao = y.env.prevrandao ∧
    x.env.gaslimit = y.env.gaslimit ∧
    x.env.chainid = y.env.chainid ∧
    x.env.basefee = y.env.basefee ∧
    x.env.blobbasefee = y.env.blobbasefee ∧
    x.env.calldata = y.env.calldata ∧
    x.env.code = y.env.code ∧
    x.env.keccakOf = y.env.keccakOf ∧
    x.env.blockHashOf = y.env.blockHashOf ∧
    x.env.blobHashOf = y.env.blobHashOf ∧
    x.env.dataOffset = y.env.dataOffset ∧
    x.env.dataSize = y.env.dataSize ∧
    x.env.immutable = y.env.immutable := by
  unfold agreeExceptSelf scrubSelf at h
  injection h with _ _ henv
  injection henv with haddr ho hc hv hg _ hct hs' hcb ht hn hpr hgl hci hbf hbb
    hcd hcode hkec _ _ _ _ _ _ hbh hbh2 hdo hds himm
  exact ⟨haddr, ho, hc, hv, hg, hct, hs', hcb, ht, hn, hpr, hgl, hci, hbf, hbb,
    hcd, hcode, hkec, hbh, hbh2, hdo, hds, himm⟩

/-- Successful CALL: Core `ofCallSuccess` on the unrestored oracle response
matches Yul `finishCall` of the lock-restored response, after `scrubSelf`
(local storage / transient / logs / returndata are dropped). -/
theorem ExtAgree_finishCall_restored {self : Address} {x : Lsc.ExtState}
    {st : EvmState} {raw : CallResponse} {iOff iSz oOff oSz : Nat}
    (h : ExtAgree self x st) (hs : raw.success = true) :
    ExtAgree self (ofCallSuccess x raw)
      (finishCall .call st (restoreCall (ExtView.ofState st) raw)
        iOff iSz oOff oSz) := by
  unfold ExtAgree agreeExceptSelf at h ⊢
  have hf := agreeExceptSelf_frame (self := self) h
  have hk : CallKind.call ≠ .staticcall := by decide
  have hsY : (restoreCall (ExtView.ofState st) raw).success = true := by
    simpa [restoreCall] using hs
  simp only [ofCallSuccess, finishCall, hs, hsY, hk, and_true, ite_true]
  unfold scrubSelf scrubSelfWord ExtView.ofState ExtState.ofState installWorld
    CallWorld.install touchMemory2 touchMemory restoreCall restoreSelfWorld
  rcases hf with ⟨haddr, ho, hc, hv, hg, hct, hs', hcb, ht, hn, hpr, hgl, hci, hbf, hbb,
    hcd, hcode, hkec, hbh, hbh2, hdo, hds, himm⟩
  simp [haddr, ho, hc, hv, hg, hct, hs', hcb, ht, hn, hpr, hgl, hci, hbf, hbb,
    hcd, hcode, hkec, hbh, hbh2, hdo, hds, himm, ExtView.ofState, ExtState.ofState]

/-- Successful CALL: Core `ofCallSuccess` matches the installed Yul world
after `scrubSelf` (local storage/logs/returndata dropped). Same response
on both sides (the restored `toCall` form). -/
theorem ExtAgree_finishCall_success {self : Address} {x : Lsc.ExtState}
    {st : EvmState} {resp : CallResponse} {iOff iSz oOff oSz : Nat}
    (h : ExtAgree self x st) (hs : resp.success = true) :
    ExtAgree self (ofCallSuccess x resp)
      (finishCall .call st resp iOff iSz oOff oSz) := by
  unfold ExtAgree agreeExceptSelf at h ⊢
  have hf := agreeExceptSelf_frame (self := self) h
  have hk : CallKind.call ≠ .staticcall := by decide
  simp only [ofCallSuccess, finishCall, hs, hk, and_true, ite_true]
  unfold scrubSelf scrubSelfWord ExtView.ofState ExtState.ofState installWorld
    CallWorld.install touchMemory2 touchMemory
  rcases hf with ⟨haddr, ho, hc, hv, hg, hct, hs', hcb, ht, hn, hpr, hgl, hci, hbf, hbb,
    hcd, hcode, hkec, hbh, hbh2, hdo, hds, himm⟩
  simp [haddr, ho, hc, hv, hg, hct, hs', hcb, ht, hn, hpr, hgl, hci, hbf, hbb,
    hcd, hcode, hkec, hbh, hbh2, hdo, hds, himm, ExtView.ofState, ExtState.ofState]

theorem ExtAgree_finishCall_noInstall {self : Address} {x : Lsc.ExtState}
    {kind : CallKind} {st : EvmState} {resp : CallResponse}
    {iOff iSz oOff oSz : Nat}
    (h : ExtAgree self x st)
    (hni : resp.success = false ∨ kind = .staticcall) :
    ExtAgree self x (finishCall kind st resp iOff iSz oOff oSz) := by
  unfold ExtAgree agreeExceptSelf at h ⊢
  have hpost :
      (if resp.success = true ∧ kind ≠ .staticcall then
          resp.world.install (touchMemory2 st iOff iSz oOff oSz)
        else touchMemory2 st iOff iSz oOff oSz) =
        touchMemory2 st iOff iSz oOff oSz := by
    cases hni with
    | inl hf => simp [hf]
    | inr hk => simp [hk]
  simp only [finishCall, hpost]
  simp [scrubSelf, scrubSelfWord, ExtView.ofState, ExtState.ofState,
    touchMemory2, touchMemory] at h ⊢
  exact h

end Lsc.Compiler
