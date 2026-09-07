import Lsc.Compiler.Proof.Core
import Lsc.Compiler.Proof.Calldata
import Lsc.Compiler.Proof.OpsToken
import YulSemantics.ObjectRun

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

private theorem step_datasize (st : EvmState) (k : U256) :
    stepOp Op.datasize [k] st = some (.ok [st.env.dataSize k] st) := rfl

private theorem step_dataoffset (st : EvmState) (k : U256) :
    stepOp Op.dataoffset [k] st = some (.ok [st.env.dataOffset k] st) := rfl

private theorem step_datacopy (st : EvmState) (d s0 nn : U256) :
    stepOp Op.datacopy [d, s0, nn] st = some (.ok []
      { touchMemory st d.toNat nn.toNat with
        memory := copyInto st.memory d.toNat s0.toNat nn.toNat st.env.code }) := rfl

theorem emitCtorCopy_zero (e : Emit) : emitCtorCopy e 0 = e := rfl

theorem emitCtorLoads_zero (e : Emit) : emitCtorLoads e 0 = e := rfl

theorem emitCtorLoads_succ (e : Emit) (n : Nat) :
    emitCtorLoads e (n + 1) =
      (emitCtorLoads e n).push
        (.letDecl [identV n]
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
      ExecStmts evm funs [] st (emitCtorLoads {} k).stmts
        (toVEnv ((List.range k).map (fun i =>
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
          (toVEnv ((List.range k).map (fun i =>
            (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          st1 (bop Op.mload [lit (abiPtr + 32 * k)])
          (.vals [wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k)]
            (touchMemory st1 (abiPtr + 32 * k) 32)) :=
      Step.builtinOk (Step.argsCons Step.argsNil Step.lit)
        (by simp only [litValue_number, step_mload', hlit]; rw [hloadW])
    have hlet :
        ExecStmt evm funs
          (toVEnv ((List.range k).map (fun i =>
            (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          st1
          (.letDecl [identV k]
            (some (bop Op.mload [lit (abiPtr + 32 * k)])))
          ((identV k,
              BitVec.ofNat 256
                (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * k)).toNat) ::
            toVEnv ((List.range k).map (fun i =>
              (wordFrom st0.env.code (st0.env.code.length - 32 * n + 32 * i)).toNat)).reverse)
          (touchMemory st1 (abiPtr + 32 * k) 32) .normal := by
      have h0 := Step.letVal (vars := [identV k]) heval (by simp)
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
      ExecStmts evm funs [] (ctorCopied st0 n) (emitCtorLoads {} n).stmts
        (toVEnv (decodeCtorArgs n st0.env.code).reverse) st' .normal := by
  have hdec : decodeCtorArgs n st0.env.code =
      (List.range n).map (fun i =>
        (wordFrom st0.env.code ((st0.env.code.length - 32 * n) + 32 * i)).toNat) :=
    rfl
  have ⟨st', hm, hMO, hexec⟩ :=
    ctorLoads_from funs st0 (ctorCopied st0 n) n n (Nat.le_refl _)
      (by simp [ctorCopied]) (ctorCopied_code st0 n) hle hptr
  refine ⟨st', hm, hMO, ?_⟩
  convert hexec using 1
  simp [hdec]

theorem hoist_ctorLoads (e : Emit) (n : Nat) :
    hoist evm (emitCtorLoads e n).stmts = hoist evm e.stmts := by
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

theorem hoist_ctorParams (n : Nat) : hoist evm (emitCtorParams {} n).stmts = [] := by
  simp only [emitCtorParams]
  cases n with
  | zero =>
    simp [emitCtorCopy_zero, emitCtorLoads_zero, Emit.stmts_nil, hoist]
  | succ n =>
    have h := hoist_ctorLoads (emitCtorCopy {} (n + 1)) (n + 1)
    simpa [hoist_ctorCopy] using h

theorem emitCtorParams_stmts (n : Nat) :
    (emitCtorParams {} n).stmts =
      (emitCtorCopy {} n).stmts ++ (emitCtorLoads {} n).stmts := by
  cases n with
  | zero => simp [emitCtorParams, emitCtorCopy_zero, emitCtorLoads_zero, Emit.stmts_nil]
  | succ n =>
    simp only [emitCtorParams]
    -- `emitCtorLoads (emitCtorCopy {} (n+1)) (n+1)`: loads fold onto the copy emitter
    have hacc : ∀ k, emitCtorLoads (emitCtorCopy {} (n + 1)) k =
        { acc := (emitCtorLoads {} k).acc ++ (emitCtorCopy {} (n + 1)).acc } := by
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
      ExecStmts evm funs [] st (emitCtorParams {} n).stmts
        (toVEnv (decodeCtorArgs n st.env.code).reverse) st' .normal := by
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
    obtain ⟨st', hm, hMO, hloads⟩ := ctorLoads_sim funs st (n + 1) hle hptr
    refine ⟨st', (memOnly_ctorCopied st (n + 1)).trans hMO, ?_⟩
    rw [emitCtorParams_stmts]
    exact execStmts_append hcopy hloads

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

