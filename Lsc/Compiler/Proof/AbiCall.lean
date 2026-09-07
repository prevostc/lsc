import Lsc.Compiler.Proof.Calldata
import Lsc.Compiler.Proof.Layout
import Lsc.Compiler.Externals
import YulSemantics.Dialect.EVM

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Pack / `finishCall` / return-check lemmas for S2 `op_sim_call`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem step_mload (st : EvmState) (p : U256) :
    stepOp Op.mload [p] st = some (.ok [loadWord st.memory p.toNat]
      (touchMemory st p.toNat 32)) := rfl

theorem step_returndatasize (st : EvmState) :
    stepOp Op.returndatasize [] st =
      some (.ok [BitVec.ofNat 256 st.returndata.length] st) := rfl

theorem step_or (st : EvmState) (a b : U256) :
    stepOp Op.or [a, b] st = some (.ok [a ||| b] st) := rfl

theorem step_and (st : EvmState) (a b : U256) :
    stepOp Op.and [a, b] st = some (.ok [a &&& b] st) := rfl

theorem selectorBytes_length (n : Nat) : (selectorBytes n).length = 4 := by
  simp [selectorBytes]

theorem wordBytes_length (n : Nat) : (wordBytes n).length = 32 := by
  simp [wordBytes]

theorem extCallGas_lt_wordBound : extCallGas < wordBound := by
  unfold extCallGas wordBound
  exact Nat.lt_trans (by decide : 1000000 < 2 ^ 20)
    (Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : (20 : Nat) < 256))

theorem finishCall_storage_fail_eq (kind : CallKind) (st : EvmState)
    (resp : CallResponse) (iOff iSz oOff oSz : Nat) (h : resp.success = false) :
    (finishCall kind st resp iOff iSz oOff oSz).storage = st.storage :=
  funext fun k => finishCall_failure_storage kind st resp iOff iSz oOff oSz k h

theorem finishCall_returndata (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).returndata = resp.returndata :=
  rfl

theorem CallResponse.flag_of (resp : CallResponse) :
    resp.flag = if resp.success then (1 : U256) else (0 : U256) := rfl

theorem finishCall_address (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.address = st.env.address := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_caller (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.caller = st.env.caller := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_callvalue (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.callvalue = st.env.callvalue := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_timestamp (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.timestamp = st.env.timestamp := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_number (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.number = st.env.number := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_static (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.static = st.env.static := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_calldata (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.calldata = st.env.calldata := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_keccak (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).env.keccakOf = st.env.keccakOf := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem finishCall_halted (kind st resp iOff iSz oOff oSz) :
    (finishCall kind st resp iOff iSz oOff oSz).halted = st.halted := by
  simp only [finishCall]; split <;> simp [CallWorld.install, touchMemory2, touchMemory]

theorem ctxRel_finishCall {ctx st} (h : ctxRel ctx st) (kind : CallKind)
    (resp : CallResponse) (iOff iSz oOff oSz : Nat) :
    ctxRel ctx (finishCall kind st resp iOff iSz oOff oSz) := by
  rcases h with ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf⟩
  · rw [finishCall_caller, h1]
  · rw [finishCall_callvalue, h2]
  · rw [finishCall_timestamp, h3]
  · rw [finishCall_number, h4]
  · rw [finishCall_address, h5]
  · rw [finishCall_static, hs]
  · rw [finishCall_halted, hh]
  · rw [finishCall_calldata]; exact hcd

theorem finishCall_logs_fail (kind st resp iOff iSz oOff oSz)
    (h : resp.success = false) :
    (finishCall kind st resp iOff iSz oOff oSz).logs = st.logs := by
  simp [finishCall, h, touchMemory2, touchMemory]

theorem finishCall_logs_success (kind st resp iOff iSz oOff oSz)
    (hs : resp.success = true) (hk : kind ≠ .staticcall) :
    (finishCall kind st resp iOff iSz oOff oSz).logs = st.logs ++ resp.world.logs := by
  simp [finishCall, hs, hk, CallWorld.install, touchMemory2, touchMemory]

theorem selfLogs_finishCall_fail (kind st resp iOff iSz oOff oSz)
    (h : resp.success = false) :
    selfLogs (finishCall kind st resp iOff iSz oOff oSz) = selfLogs st := by
  simp [selfLogs, finishCall_logs_fail (h := h), finishCall_address]

theorem selfLogs_finishCall_success {G} {α : Abs G} {st : EvmState}
    {resp : CallResponse} {callee : Address} {iOff iSz oOff oSz : Nat}
    (hs : resp.success = true)
    (hni : NoInterfere α st resp.world callee) :
    selfLogs (finishCall .call st resp iOff iSz oOff oSz) = selfLogs st := by
  have ⟨_, _, _, _, hlogs, _⟩ := hni
  have hk : CallKind.call ≠ .staticcall := by decide
  simp only [selfLogs, finishCall_logs_success .call st resp iOff iSz oOff oSz hs hk,
    finishCall_address, List.filter_append]
  have hnone : resp.world.logs.filter (fun l => l.address = st.env.address) = [] :=
    List.filter_eq_nil_iff.mpr fun l hl => by simp [hlogs l hl]
  simp [hnone]

theorem copyReturn_in (mem : Nat → UInt8) (dst osz : Nat) (bs : List UInt8)
    (a : Nat) (h : dst ≤ a ∧ a < dst + min osz bs.length) :
    copyReturn mem dst osz bs a = byteFrom bs (a - dst) := by
  simp [copyReturn, h]

theorem loadWord_copyReturn_ge32 (mem : Nat → UInt8) (dst osz : Nat)
    (bs : List UInt8) (hlen : 32 ≤ bs.length) (hoz : 32 ≤ osz) :
    loadWord (copyReturn mem dst osz bs) dst = wordFrom bs 0 := by
  unfold loadWord wordFrom
  refine foldl_congr ?_
  intro acc i hi
  have hi' : i < 32 := List.mem_range.mp hi
  have hin : dst ≤ dst + i ∧ dst + i < dst + min osz bs.length := by omega
  rw [copyReturn_in mem dst osz bs (dst + i) hin, Nat.add_sub_cancel_left, Nat.zero_add]

theorem finishCall_mload_ge32 (kind st resp iOff iSz oOff oSz)
    (hlen : 32 ≤ resp.returndata.length) (hoz : 32 ≤ oSz) :
    loadWord (finishCall kind st resp iOff iSz oOff oSz).memory oOff =
      wordFrom resp.returndata 0 := by
  change loadWord (copyReturn st.memory oOff oSz resp.returndata) oOff =
    wordFrom resp.returndata 0
  exact loadWord_copyReturn_ge32 st.memory oOff oSz resp.returndata hlen hoz

theorem readBytes_pack0 (mem : Nat → UInt8) (sel : Nat) (hsel : sel < 2 ^ 32) :
    readBytes (storeWord mem abiPtr (BitVec.ofNat 256 sel <<< 224)) abiPtr 4 =
      selectorBytes sel :=
  selectorBytes_mem mem sel hsel

theorem boolOpt_or_b2w (rds mload : U256) :
    b2w (rds = 0) ||| (b2w (rds.ult 32 = false) &&& b2w (mload = 1)) =
      b2w (decide (rds = 0) || (rds.ult 32 = false && decide (mload = 1))) := by
  simp [b2w_or, b2w_and]

theorem Abs.ofState_finishCall_fail {G} (α : Abs G) (kind st resp a iOff iSz oOff oSz)
    (h : resp.success = false) :
    α.ofState (finishCall kind st resp iOff iSz oOff oSz) a = α.ofState st a := by
  have hproj := α.ofState_proj
  rw [hproj, hproj]
  congr 1
  simp [CallWorld.ofState, finishCall, h, touchMemory2, touchMemory]

theorem finishCall_storage_success_eq (st : EvmState) (resp : CallResponse)
    (iOff iSz oOff oSz : Nat) (hs : resp.success = true) :
    (finishCall .call st resp iOff iSz oOff oSz).storage = resp.world.storage :=
  funext fun k => finishCall_success_storage .call st resp iOff iSz oOff oSz k hs
    (by decide)

theorem CallWorld.ofState_finishCall_success (st : EvmState) (resp : CallResponse)
    (iOff iSz oOff oSz : Nat) (hs : resp.success = true) :
    CallWorld.ofState (finishCall .call st resp iOff iSz oOff oSz) =
      CallWorld.ofState (resp.world.install (touchMemory2 st iOff iSz oOff oSz)) := by
  simp [finishCall, hs, CallWorld.ofState, CallWorld.install, touchMemory2, touchMemory]

theorem Abs.ofState_finishCall_success {G} (α : Abs G) (st : EvmState)
    (resp : CallResponse) (a : Address) (iOff iSz oOff oSz : Nat)
    (hs : resp.success = true) :
    α.ofState (finishCall .call st resp iOff iSz oOff oSz) a = α.ofWorld resp.world a := by
  rw [α.ofState_proj, CallWorld.ofState_finishCall_success st resp iOff iSz oOff oSz hs,
    α.ofWorld_install]

private theorem storeWord_out_prefix (mem : Nat → UInt8) (dst : Nat) (v : U256)
    (p n : Nat) (h : p + n ≤ dst) :
    readBytes (storeWord mem dst v) p n = readBytes mem p n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  exact storeWord_out mem dst v (p + i) (.inl (by omega))

/-- Store one ABI word at offset `off` and extend a packed prefix. -/
theorem readBytes_pack_snoc (mem : Nat → UInt8) (off v : Nat)
    (hv : v < wordBound) {pre : List UInt8}
    (hpre : readBytes mem abiPtr (4 + 32 * off) = pre) :
    readBytes (storeWord mem (abiAfterSel + 32 * off) (BitVec.ofNat 256 v))
      abiPtr (4 + 32 * (off + 1)) = pre ++ wordBytes v := by
  have hlen : 4 + 32 * (off + 1) = (4 + 32 * off) + 32 := by omega
  rw [hlen, readBytes_split]
  have hptr : abiPtr + (4 + 32 * off) = abiAfterSel + 32 * off := by
    simp [abiPtr, abiAfterSel]; omega
  rw [hptr, readBytes_storeWord_wordBytes (hn := hv)]
  refine congrArg (fun l => l ++ wordBytes v) ?_
  have hle : abiPtr + (4 + 32 * off) ≤ abiAfterSel + 32 * off := by
    simp [abiPtr, abiAfterSel]; omega
  rw [storeWord_out_prefix (h := hle), hpre]

end Lsc.Compiler
