import Lsc.Compiler.Proof.CoreProof
import Lsc.Compiler.Proof.Calldata
import Lsc.Compiler.Proof.OpsToken
import YulSemantics.ObjectRun

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Constructor prologue: `codecopy` / `mload` of CREATE args from `env.code`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc

theorem step_codesize (st : EvmState) :
    stepOp Op.codesize [] st = some (.ok [BitVec.ofNat 256 st.env.code.length] st) :=
  rfl

private theorem step_mload' (st : EvmState) (p : U256) :
    stepOp Op.mload [p] st = some (.ok [loadWord st.memory p.toNat]
      (touchMemory st p.toNat 32)) := rfl

theorem step_codecopy (st : EvmState) (d s0 nn : U256) :
    stepOp Op.codecopy [d, s0, nn] st = some (.ok []
      { touchMemory st d.toNat nn.toNat with
        memory := copyInto st.memory d.toNat s0.toNat nn.toNat st.env.code }) :=
  rfl

theorem step_datasize (st : EvmState) (k : U256) :
    stepOp Op.datasize [k] st = some (.ok [st.env.dataSize k] st) := rfl

theorem step_dataoffset (st : EvmState) (k : U256) :
    stepOp Op.dataoffset [k] st = some (.ok [st.env.dataOffset k] st) := rfl

theorem step_datacopy (st : EvmState) (d s0 nn : U256) :
    stepOp Op.datacopy [d, s0, nn] st = some (.ok []
      { touchMemory st d.toNat nn.toNat with
        memory := copyInto st.memory d.toNat s0.toNat nn.toNat st.env.code }) := rfl

theorem emitCtorCopy_zero (e : Emit) : emitCtorCopy e 0 = e := rfl

theorem emitCtorLoads_zero (e : Emit) : emitCtorLoads tag e 0 = e := rfl

theorem emitCtorLoads_succ (e : Emit) (n : Nat) :
    emitCtorLoads tag e (n + 1) =
      (emitCtorLoads tag e n).push
        (.letDecl [identV tag n]
          (some (bop Op.mload [lit (abiPtr + 32 * n)]))) := by
  have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
  dsimp only [emitCtorLoads]
  rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem emitCtorCopy_succ (e : Emit) (n : Nat) :
    emitCtorCopy e (n + 1) =
      emitDo e Op.codecopy
        [lit abiPtr,
         bop Op.sub [bop Op.codesize [], lit (32 * (n + 1))],
         lit (32 * (n + 1))] := by
  simp [emitCtorCopy]

private theorem foldl_congr' {α β} {xs : List α} {f g : β → α → β} {b : β}
    (h : ∀ (b : β) (a : α), a ∈ xs → f b a = g b a) :
    xs.foldl f b = xs.foldl g b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    have hx : f b x = g b x := h b x (List.mem_cons.mpr (Or.inl rfl))
    rw [List.foldl_cons, hx]
    exact ih (fun b a ha => h b a (List.mem_cons.mpr (Or.inr ha)))

theorem copyInto_get (mem : Nat → UInt8) (dst src n : Nat) (bytes : List UInt8)
    (a : Nat) (h : dst ≤ a ∧ a < dst + n) :
    copyInto mem dst src n bytes a = byteFrom bytes (src + (a - dst)) := by
  simp [copyInto, h]

theorem loadWord_copyInto (mem : Nat → UInt8) (dst src len : Nat) (bytes : List UInt8)
    (p : Nat) (hp : dst ≤ p ∧ p + 32 ≤ dst + len) :
    loadWord (copyInto mem dst src len bytes) p = wordFrom bytes (src + (p - dst)) := by
  unfold loadWord wordFrom
  refine foldl_congr' ?_
  intro acc i hi
  have hi' : i < 32 := List.mem_range.mp hi
  have hin : dst ≤ p + i ∧ p + i < dst + len := by omega
  have hidx : src + (p + i - dst) = src + (p - dst) + i := by omega
  rw [copyInto_get (h := hin), hidx]

theorem memOnly_codecopy (st : EvmState) (d s0 nn : U256) :
    MemOnly st { touchMemory st d.toNat nn.toNat with
      memory := copyInto st.memory d.toNat s0.toNat nn.toNat st.env.code } := by
  simp [MemOnly, touchMemory]

theorem touchMemory_memory (st : EvmState) (p n : Nat) :
    (touchMemory st p n).memory = st.memory := rfl

theorem decodeCtorArgs_length (n : Nat) (code : List UInt8) :
    (decodeCtorArgs n code).length = n := by
  simp [decodeCtorArgs]

theorem decodeCtorArgs_wf (n : Nat) (code : List UInt8) :
    EnvWF (decodeCtorArgs n code).reverse := by
  intro v hv
  have hv' : v ∈ decodeCtorArgs n code := List.mem_reverse.mp hv
  unfold decodeCtorArgs at hv'
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv'
  exact wordFrom_toNat_lt _ _

theorem decodeCtorArgs_append (pref : List UInt8) (args : List Nat)
    (hbound : ∀ n ∈ args, n < wordBound) :
    decodeCtorArgs args.length (pref ++ ctorCalldata args) = args := by
  apply List.ext_getElem
  · simp [decodeCtorArgs, ctorCalldata, length_flatMap_wordBytes]
  · intro i hi _hi'
    simp only [decodeCtorArgs, List.getElem_map, List.getElem_range]
    have hiargs : i < args.length := by simpa [decodeCtorArgs] using hi
    have hoff : (pref ++ ctorCalldata args).length - 32 * args.length = pref.length := by
      simp [ctorCalldata, length_flatMap_wordBytes, Nat.mul_comm]
    rw [hoff]
    have hpref : pref.length ≤ pref.length + 32 * i := Nat.le_add_right _ _
    rw [wordFrom_append_right pref (ctorCalldata args) (pref.length + 32 * i) hpref]
    simp only [Nat.add_sub_cancel_left, ctorCalldata]
    rw [wordFrom_flatMap_wordBytes args i hiargs hbound,
      toNat_ofNat_of_lt (hbound args[i] (List.getElem_mem hiargs))]

theorem eval_codesize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st (bop Op.codesize [])
      (.vals [BitVec.ofNat 256 st.env.code.length] st) :=
  Step.builtinOk Step.argsNil (by simp [step_codesize])

theorem eval_sub_codesize (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    (argsLen : Nat) (hLen : argsLen ≤ st.env.code.length)
    (hcode : st.env.code.length < wordBound) :
    EvalExpr evm funs V st
      (bop Op.sub [bop Op.codesize [], lit argsLen])
      (.vals [BitVec.ofNat 256 (st.env.code.length - argsLen)] st) := by
  have hLit : EvalExpr evm funs V st (lit argsLen)
      (.vals [BitVec.ofNat 256 argsLen] st) := Step.lit
  refine Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hLit) (eval_codesize funs V st)) ?_
  simp only [litValue_number, step_sub]
  rw [ofNat_sub_of_le hLen hcode]

def ctorCopied (st : EvmState) (n : Nat) : EvmState :=
  { touchMemory st abiPtr (32 * n) with
    memory := copyInto st.memory abiPtr (st.env.code.length - 32 * n) (32 * n)
      st.env.code }

theorem ctorCopied_code (st : EvmState) (n : Nat) :
    (ctorCopied st n).env.code = st.env.code := rfl

theorem memOnly_ctorCopied (st : EvmState) (n : Nat) :
    MemOnly st (ctorCopied st n) := by
  simp [MemOnly, ctorCopied, touchMemory]

theorem codecopy_sim (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (n : Nat)
    (hn : 0 < n) (hle : 32 * n ≤ st.env.code.length)
    (hcode : st.env.code.length < wordBound)
    (hptr : abiPtr + 32 * n < wordBound) :
    ExecStmts evm funs V st (emitCtorCopy {} n).stmts V (ctorCopied st n) .normal := by
  cases n with
  | zero => exact (Nat.lt_irrefl _ hn).elim
  | succ n =>
    rw [emitCtorCopy_succ, emitDo_stmts, Emit.stmts_nil, List.nil_append]
    have hsrc := eval_sub_codesize funs V st (32 * (n + 1)) hle hcode
    have hdst : EvalExpr evm funs V st (lit abiPtr)
        (.vals [BitVec.ofNat 256 abiPtr] st) := Step.lit
    have hnn : EvalExpr evm funs V st (lit (32 * (n + 1)))
        (.vals [BitVec.ofNat 256 (32 * (n + 1))] st) := Step.lit
    have hnn2 : (BitVec.ofNat 256 (32 * (n + 1))).toNat = 32 * (n + 1) :=
      toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hptr)
    have hsrcT : (BitVec.ofNat 256 (st.env.code.length - 32 * (n + 1))).toNat =
        st.env.code.length - 32 * (n + 1) :=
      toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcode)
    have he :
        EvalExpr evm funs V st
          (bop Op.codecopy
            [lit abiPtr,
             bop Op.sub [bop Op.codesize [], lit (32 * (n + 1))],
             lit (32 * (n + 1))])
          (.vals [] (ctorCopied st (n + 1))) := by
      refine Step.builtinOk
        (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hnn) hsrc) hdst) ?_
      simp only [litValue_number, step_codecopy, toNat_abiPtr, ctorCopied]
      rw [hnn2, hsrcT]
    exact Step.seqCons (Step.exprStmt he) Step.seqNil

/-- Loads `v_0 … v_{k-1}` from a memory that already holds the `32n`-byte suffix copy. -/
theorem ctorLoads_from (funs : FunEnv evm) (st0 st : EvmState) (n k : Nat)
    (hk : k ≤ n)
    (hmem : st.memory = copyInto st0.memory abiPtr
      (st0.env.code.length - 32 * n) (32 * n) st0.env.code)
    (hcode : st.env.code = st0.env.code)
    (hle : 32 * n ≤ st0.env.code.length)
    (hptr : abiPtr + 32 * n < wordBound) :
    ∃ st', st'.memory = st.memory ∧ MemOnly st st' ∧
      ExecStmts evm funs [] st (emitCtorLoads tag {} k).stmts
        (toVEnv tag ((List.range k).map (fun i =>
          (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
        st' .normal := by
  induction k generalizing st with
  | zero =>
    refine ⟨st, rfl, ?_, ?_⟩
    · simp [MemOnly]
    · simp [emitCtorLoads_zero, Emit.stmts_nil, toVEnv_nil]
      exact Step.seqNil
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    obtain ⟨st1, hmem1, hMO, hexec⟩ := ih st hk' hmem hcode
    have hptrk : abiPtr + 32 * k < wordBound := by
      have : 32 * k ≤ 32 * n := Nat.mul_le_mul_left 32 hk'
      omega
    have hp : abiPtr ≤ abiPtr + 32 * k ∧ abiPtr + 32 * k + 32 ≤ abiPtr + 32 * n := by
      have : 32 * (k + 1) ≤ 32 * n := Nat.mul_le_mul_left 32 hk
      omega
    have hlit : (BitVec.ofNat 256 (abiPtr + 32 * k)).toNat = abiPtr + 32 * k :=
      toNat_ofNat_of_lt hptrk
    have hloadW :
        loadWord st1.memory (abiPtr + 32 * k) =
          wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k) := by
      rw [hmem1, hmem, loadWord_copyInto (hp := hp)]
      simp
    have heval :
        EvalExpr evm funs
          (toVEnv tag ((List.range k).map (fun i =>
            (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          st1 (bop Op.mload [lit (abiPtr + 32 * k)])
          (.vals [wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k)]
            (touchMemory st1 (abiPtr + 32 * k) 32)) :=
      Step.builtinOk (Step.argsCons Step.argsNil Step.lit)
        (by simp only [litValue_number, step_mload', hlit]; rw [hloadW])
    have hlet :
        ExecStmt evm funs
          (toVEnv tag ((List.range k).map (fun i =>
            (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          st1
          (.letDecl [identV tag k]
            (some (bop Op.mload [lit (abiPtr + 32 * k)])))
          ((identV tag k,
              BitVec.ofNat 256
                (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k)).toNat) ::
            toVEnv tag ((List.range k).map (fun i =>
              (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          (touchMemory st1 (abiPtr + 32 * k) 32) .normal := by
      have h0 := Step.letVal (vars := [identV tag k]) heval (by simp)
      convert h0 using 1
      simp [List.zip_cons_cons]
    refine ⟨touchMemory st1 (abiPtr + 32 * k) 32, by simp [touchMemory, hmem1],
      hMO.trans (memOnly_touch st1 _ _), ?_⟩
    rw [emitCtorLoads_succ, Emit.stmts_push]
    have hrange : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    have hmap :
        (List.range (k + 1)).map (fun i =>
          (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat) =
          (List.range k).map (fun i =>
            (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat) ++
            [(wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k)).toNat] := by
      rw [hrange, List.map_append, List.map_cons, List.map_nil]
    rw [hmap, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, toVEnv_cons]
    simp only [List.length_reverse, List.length_map, List.length_range]
    exact execStmts_append hexec (Step.seqCons hlet Step.seqNil)

theorem ctorLoads_sim (funs : FunEnv evm) (st0 : EvmState) (n : Nat)
    (hle : 32 * n ≤ st0.env.code.length)
    (hptr : abiPtr + 32 * n < wordBound) :
    ∃ st', st'.memory = (ctorCopied st0 n).memory ∧ MemOnly (ctorCopied st0 n) st' ∧
      ExecStmts evm funs [] (ctorCopied st0 n) (emitCtorLoads tag {} n).stmts
        (toVEnv tag (decodeCtorArgs n st0.env.code).reverse) st' .normal := by
  have hdec : decodeCtorArgs n st0.env.code =
      (List.range n).map (fun i =>
        (wordFrom st0.env.code ((st0.env.code.length - 32 * n) + 32 * i)).toNat) :=
    rfl
  have ⟨st', hm, hMO, hexec⟩ :=
    ctorLoads_from tag funs st0 (ctorCopied st0 n) n n (Nat.le_refl _)
      (by simp [ctorCopied]) (ctorCopied_code st0 n) hle hptr
  refine ⟨st', hm, hMO, ?_⟩
  convert hexec using 1
  simp [hdec]

theorem hoist_ctorLoads (e : Emit) (n : Nat) :
    hoist evm (emitCtorLoads tag e n).stmts = hoist evm e.stmts := by
  induction n generalizing e with
  | zero => simp [emitCtorLoads_zero]
  | succ n ih =>
    rw [emitCtorLoads_succ, Emit.stmts_push, hoist_append, ih]
    simp [hoist]

theorem hoist_ctorCopy (n : Nat) : hoist evm (emitCtorCopy {} n).stmts = [] := by
  cases n with
  | zero => simp [emitCtorCopy_zero, Emit.stmts_nil, hoist]
  | succ n =>
    rw [emitCtorCopy_succ, emitDo_stmts, Emit.stmts_nil]
    simp [hoist]

theorem hoist_ctorParams tag (n : Nat) : hoist evm (emitCtorParams tag {} n).stmts = [] := by
  simp only [emitCtorParams]
  cases n with
  | zero =>
    simp [emitCtorCopy_zero, emitCtorLoads_zero, Emit.stmts_nil, hoist]
  | succ n =>
    have h := hoist_ctorLoads tag (emitCtorCopy {} (n + 1)) (n + 1)
    simpa [hoist_ctorCopy] using h

theorem emitCtorParams_stmts (n : Nat) :
    (emitCtorParams tag {} n).stmts =
      (emitCtorCopy {} n).stmts ++ (emitCtorLoads tag {} n).stmts := by
  cases n with
  | zero => simp [emitCtorParams, emitCtorCopy_zero, emitCtorLoads_zero, Emit.stmts_nil]
  | succ n =>
    simp only [emitCtorParams]
    -- `emitCtorLoads tag (emitCtorCopy {} (n+1)) (n+1)`: loads fold onto the copy emitter
    have hacc : ∀ k, emitCtorLoads tag (emitCtorCopy {} (n + 1)) k =
        { acc := (emitCtorLoads tag {} k).acc ++ (emitCtorCopy {} (n + 1)).acc } := by
      intro k
      induction k with
      | zero => simp [emitCtorLoads_zero]
      | succ k ih =>
        rw [emitCtorLoads_succ, emitCtorLoads_succ, ih]
        simp [Emit.push]
    rw [hacc]
    simp [Emit.stmts, List.reverse_append]

theorem params_sim_ctor (funs : FunEnv evm) (st : EvmState) (n : Nat)
    (hle : 32 * n ≤ st.env.code.length)
    (hcode : st.env.code.length < wordBound)
    (hptr : abiPtr + 32 * n < wordBound) :
    ∃ st', MemOnly st st' ∧
      ExecStmts evm funs [] st (emitCtorParams tag {} n).stmts
        (toVEnv tag (decodeCtorArgs n st.env.code).reverse) st' .normal := by
  cases n with
  | zero =>
    refine ⟨st, ?_, ?_⟩
    · simp [MemOnly]
    · simp [emitCtorParams, emitCtorCopy_zero, emitCtorLoads_zero, Emit.stmts_nil,
        decodeCtorArgs, toVEnv_nil]
      exact Step.seqNil
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos _
    have hcopy := codecopy_sim funs [] st (n + 1) hn hle hcode hptr
    obtain ⟨st', hm, hMO, hloads⟩ := ctorLoads_sim tag funs st (n + 1) hle hptr
    refine ⟨st', (memOnly_ctorCopied st (n + 1)).trans hMO, ?_⟩
    rw [emitCtorParams_stmts]
    exact execStmts_append hcopy hloads

end Lsc.Compiler
