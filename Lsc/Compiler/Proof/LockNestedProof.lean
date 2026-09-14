import Lsc.Compiler.LockDefs
import Lsc.Compiler.Proof.LockPrefixProof
import YulEvmCompiler.OpStep
import YulEvmCompiler.Decode
import EvmSemantics.EVM.BigStep
import EvmSemantics.EVM.Gas

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option autoImplicit false

/-!
Nested CALL/STATICCALL frame: held lock reverts in the prologue
against `StepRunning` / `StepReturn` (slice 8C-1). Not routed through
`compile_correct` (`FrameOK` requires an empty call stack).
-/

namespace Lsc.Compiler

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

namespace Proof

theorem assemble_eq_mkCode (is : List Instr) :
    assemble is = mkCode (assembleBytes is) := rfl

theorem NestedFrame.with_stack_pc_gas {code : ByteArray} {s : State}
    (hf : NestedFrame code s) (stk : List UInt256) (pc' : UInt256)
    (gas' : Nat) :
    NestedFrame code { s with stack := stk, pc := pc', gasAvailable := gas' } :=
  ⟨hf.hcode, hf.codeSmall, hf.fork, hf.noPrecompile, hf.running⟩

theorem decoded_op_nested {code : ByteArray} {s : State} {pre post : List UInt8}
    {o : Operation} (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hb : EVM.Decode.opcodeOf (Instr.opByte o) = some o) (hp : plainOp o)
    (havail : o.availableInFork .Osaka = true) :
    s.decodedOp = some o := by
  have hsz : code.size = pre.length + 1 + post.length := by
    subst hcode; simp [Instr.bytes]; omega
  have hlen : pre.length < 2 ^ 256 := by
    have := hf.codeSmall; omega
  have hpcn : s.pc.toNat = pre.length := by
    rw [hpc]; exact YulEvmCompiler.toNat_ofNat_of_lt hlen
  have hdec : s.decoded = some (o, none) := by
    unfold State.decoded
    rw [hf.hcode, hpcn, hcode, decodeAt_op pre post o hb hp]
    have hfork : s.fork = .Osaka := hf.fork
    simp [Option.bind, hfork, havail]
  exact State.decoded_to_op hdec

theorem decoded_push_nested {code : ByteArray} {s : State} {pre post : List UInt8}
    {w : Fin 33} {v : UInt256} (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.push w v).bytes ++ post))
    (hwf : v.toNat < 256 ^ w.val)
    (hpc : s.pc = UInt256.ofNat pre.length) :
    s.decoded = some (.Push ⟨w⟩, some (v, w.val)) := by
  have hsz : code.size = pre.length + (1 + w.val) + post.length := by
    subst hcode; simp [Instr.bytes]; omega
  have hlen : pre.length < 2 ^ 256 := by
    have := hf.codeSmall; omega
  have hpcn : s.pc.toNat = pre.length := by
    rw [hpc]; exact YulEvmCompiler.toNat_ofNat_of_lt hlen
  unfold State.decoded
  rw [hf.hcode, hpcn, hcode, decodeAt_push pre post w v hwf]
  have hfork : s.fork = .Osaka := hf.fork
  simp [Option.bind, hfork]

theorem byteWidth_pos {k : Nat} (hk : 0 < k) : 0 < Instr.byteWidth k := by
  unfold Instr.byteWidth
  split
  · omega
  · omega

theorem uint256_toNat_ne_zero {u : UInt256} (h : u ≠ ⟨0⟩) : u.toNat ≠ 0 := by
  intro hz
  exact h (u256ext (hz.trans rfl))

theorem revertTotal_zero (s : State) :
    Gas.revertTotal s ⟨0⟩ ⟨0⟩ = 0 := by
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hbase : Gas.baseCost s.executionEnv.fork .REVERT = 0 := by
    simp [Gas.baseCost]
  unfold Gas.revertTotal MachineState.memExpansionDelta
    MachineState.activeWordsAfter
  simp [hbase, hz]

theorem readPadded_zero_toList (bs : ByteArray) :
    (MachineState.readPadded bs 0 0).toList = [] := by
  unfold MachineState.readPadded
  simp [Nat.zero_min, Nat.min_zero]
  native_decide

theorem pushMin_zero : Instr.pushMin ⟨0⟩ = Instr.push ⟨0, by decide⟩ ⟨0⟩ := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hz : Instr.byteWidth 0 = 0 := by native_decide
  have hw : Instr.widthOf ⟨0⟩ = ⟨0, by decide⟩ :=
    Fin.ext (by
      change Instr.byteWidth (⟨0⟩ : UInt256).toNat = 0
      rw [h0, hz])
  simp [Instr.pushMin, hw]

theorem lockPrefixInstrs_bytes (k dest : Nat) :
    assembleBytes (lockPrefixInstrs k dest) =
      (Instr.pushMin (UInt256.ofNat k)).bytes ++
        (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++
        (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++
        (Instr.op .ISZERO).bytes ++
        (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        (Instr.op .JUMPI).bytes ++
        (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .REVERT).bytes ++
        (Instr.op .JUMPDEST).bytes := by
  simp [lockPrefixInstrs, assembleBytes]

theorem baseCost_push_pos (w : Fin 33) (h : 0 < w.val) :
    Gas.baseCost .Osaka (.Push ⟨w, w.isLt⟩) = 3 := by
  simp only [Gas.baseCost]
  have hne : w.val ≠ 0 := Nat.ne_of_gt h
  rw [if_neg hne]

theorem baseCost_push0 :
    Gas.baseCost .Osaka (.Push ⟨(0 : Fin 33), by decide⟩) = 2 := by
  decide

theorem not_isTrue_isZero_of_ne {u : UInt256} (h : u ≠ ⟨0⟩) :
    ¬ UInt256.isTrue (UInt256.isZero u) := by
  have hz : u.toNat ≠ 0 := uint256_toNat_ne_zero h
  simp only [UInt256.isTrue, UInt256.isZero, hz, ↓reduceIte]
  have : (UInt256.ofNat 0).toNat = 0 := rfl
  simp [this]

/-- `PUSHk` of a nonzero constant (never `PUSH0` on this prologue). -/
theorem step_pushMin_pos {code : ByteArray} {pre post : List UInt8}
    {v : UInt256} {s : State} (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.pushMin v).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hpos : 0 < Instr.byteWidth v.toNat)
    (hcap : s.stack.length < 1024)
    (hgas : 3 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + (1 + Instr.byteWidth v.toNat)) ∧
      s'.stack = v :: s.stack ∧
      s'.gasAvailable = s.gasAvailable - 3 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  have hwf := Instr.pushMin_wf v
  have hdec := decoded_push_nested (w := Instr.widthOf v) (v := v) hf
    (by simpa [Instr.pushMin] using hcode) hwf hpc
  have hfork : s.fork = .Osaka := hf.fork
  have hwpos : 0 < (Instr.widthOf v).val := by
    simpa [Instr.widthOf_val] using hpos
  have hcost := baseCost_push_pos (Instr.widthOf v) hwpos
  have hgas' : Gas.baseCost s.fork (.Push ⟨Instr.widthOf v, (Instr.widthOf v).isLt⟩) ≤
      s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.pushN s (Instr.widthOf v) v (Instr.widthOf v).val hwpos hdec hgas' hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc + UInt256.ofNat ((Instr.widthOf v).val + 1) = _
    rw [hpc, Instr.widthOf_val]
    rw [YulEvmCompiler.ofNat_add_ofNat (by
      have hsz : code.size =
          pre.length + (1 + Instr.byteWidth v.toNat) + post.length := by
        subst hcode; simp [Instr.length_bytes_pushMin]; omega
      have := hf.codeSmall; omega)]
    try (congr 1; omega)
  · show s.gasAvailable -
        Gas.baseCost s.fork (.Push ⟨Instr.widthOf v, (Instr.widthOf v).isLt⟩) =
      s.gasAvailable - 3
    rw [hfork, hcost]

theorem step_push0 {code : ByteArray} {pre post : List UInt8} {s : State}
    (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.pushMin ⟨0⟩).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hcap : s.stack.length < 1024)
    (hgas : 2 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + 1) ∧
      s'.stack = ⟨0⟩ :: s.stack ∧
      s'.gasAvailable = s.gasAvailable - 2 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  rw [pushMin_zero] at hcode
  have hwf : (⟨0⟩ : UInt256).toNat < 256 ^ (0 : Fin 33).val := by decide
  have hdec := decoded_push_nested (w := ⟨0, by decide⟩) (v := ⟨0⟩) hf hcode hwf hpc
  have hdecOp : s.decodedOp = some (.Push ⟨0, by decide⟩) := by
    unfold State.decodedOp
    rw [hdec]
    simp
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork (.Push ⟨(0 : Fin 33), by decide⟩) ≤
      s.gasAvailable := by
    rw [hfork, baseCost_push0]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.push0 s hdecOp hgas' hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc.succ = _
    rw [hpc]
    exact YulEvmCompiler.succ_ofNat (by
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega)
  · show s.gasAvailable - Gas.baseCost s.fork (.Push ⟨(0 : Fin 33), by decide⟩) =
      s.gasAvailable - 2
    rw [hfork, baseCost_push0]

theorem step_iszero {code : ByteArray} {pre post : List UInt8}
    {a : UInt256} {rest : List UInt256} {s : State}
    (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op .ISZERO).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .ISZERO ≤
      1024 + Operation.popArity .ISZERO)
    (hgas : 3 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + 1) ∧
      s'.stack = UInt256.isZero a :: rest ∧
      s'.gasAvailable = s.gasAvailable - 3 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  have hdec := decoded_op_nested hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hcost : Gas.baseCost .Osaka .ISZERO = 3 := by decide
  have hgas' : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.iszero s a rest hdec hgas' hstk hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc.succ = _
    rw [hpc]
    exact YulEvmCompiler.succ_ofNat (by
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega)
  · rw [hfork, hcost]

theorem step_pop {code : ByteArray} {pre post : List UInt8}
    {a : UInt256} {rest : List UInt256} {s : State}
    (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op .POP).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .POP ≤
      1024 + Operation.popArity .POP)
    (hgas : 2 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + 1) ∧
      s'.stack = rest ∧
      s'.gasAvailable = s.gasAvailable - 2 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  obtain ⟨hb, hplain, havail⟩ := pop_roundtrip
  have hdec := decoded_op_nested hf hcode hpc hb hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hcost : Gas.baseCost .Osaka .POP = 2 := by decide
  have hgas' : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.pop s a rest hdec hgas' hstk hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc.succ = _
    rw [hpc]
    exact YulEvmCompiler.succ_ofNat (by
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega)
  · rw [hfork, hcost]

theorem step_tload {code : ByteArray} {pre post : List UInt8}
    {key : UInt256} {rest : List UInt256} {s : State}
    (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op .TLOAD).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = key :: rest)
    (hcap : s.stack.length + Operation.pushArity .TLOAD ≤
      1024 + Operation.popArity .TLOAD)
    (hgas : 100 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + 1) ∧
      s'.stack =
        ((s.accountMap s.executionEnv.address).tstorage key) :: rest ∧
      s'.gasAvailable = s.gasAvailable - 100 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  obtain ⟨hb, hplain⟩ := opTable_roundtrip (yop := .tload) rfl
  have hdec := decoded_op_nested hf hcode hpc hb hplain
    (opTable_available (yop := .tload) rfl)
  have hfork : s.fork = .Osaka := hf.fork
  have hcost : Gas.baseCost .Osaka .TLOAD = 100 := by decide
  have hgas' : Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.tload s key rest hdec hgas' hstk hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc.succ = _
    rw [hpc]
    exact YulEvmCompiler.succ_ofNat (by
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega)
  · rw [hfork, hcost]

theorem step_push2 {code : ByteArray} {pre post : List UInt8}
    {dest : Nat} {s : State} (hf : NestedFrame code s)
    (hcode : code =
      mkCode (pre ++ (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hdest : dest < 2 ^ 256)
    (hsmall : dest < 256 ^ labelWidth)
    (hcap : s.stack.length < 1024)
    (hgas : 3 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + (1 + labelWidth)) ∧
      s'.stack = UInt256.ofNat dest :: s.stack ∧
      s'.gasAvailable = s.gasAvailable - 3 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  have hwf : (UInt256.ofNat dest).toNat < 256 ^ labelWidthFin.val := by
    rw [labelWidthFin_val, YulEvmCompiler.toNat_ofNat_of_lt hdest]; exact hsmall
  have hdec := decoded_push_nested (w := labelWidthFin) (v := UInt256.ofNat dest)
    hf hcode hwf hpc
  have hfork : s.fork = .Osaka := hf.fork
  have hwpos : 0 < labelWidthFin.val := by simp [labelWidthFin, labelWidth]
  have hcost := baseCost_push_pos labelWidthFin hwpos
  have hgas' : Gas.baseCost s.fork (.Push ⟨labelWidthFin, labelWidthFin.isLt⟩) ≤
      s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.pushN s labelWidthFin (UInt256.ofNat dest) labelWidthFin.val
      hwpos hdec hgas' hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc + UInt256.ofNat (labelWidthFin.val + 1) = _
    rw [hpc, labelWidthFin_val]
    rw [YulEvmCompiler.ofNat_add_ofNat (by
      have hsz : code.size = pre.length + (1 + labelWidth) + post.length := by
        subst hcode; simp [Instr.length_bytes_push, labelWidthFin_val]; omega
      have := hf.codeSmall; omega)]
    rw [Nat.add_comm labelWidth 1]
  · rw [hfork, hcost]

theorem step_jumpi_notTaken {code : ByteArray} {pre post : List UInt8}
    {dest cond : UInt256} {rest : List UInt256} {s : State}
    (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op .JUMPI).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = dest :: cond :: rest)
    (hcond : ¬ UInt256.isTrue cond)
    (hcap : s.stack.length + Operation.pushArity .JUMPI ≤
      1024 + Operation.popArity .JUMPI)
    (hgas : 10 ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧ NestedFrame code s' ∧
      s'.pc = UInt256.ofNat (pre.length + 1) ∧
      s'.stack = rest ∧
      s'.gasAvailable = s.gasAvailable - 10 ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap ∧
      s'.executionEnv.address = s.executionEnv.address := by
  have hdec := decoded_op_nested hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hcost : Gas.baseCost .Osaka .JUMPI = 10 := by decide
  have hgas' : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    rw [hfork, hcost]; exact hgas
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.jumpi_notTaken s dest cond rest hdec hgas' hstk hcond hcap),
    NestedFrame.with_stack_pc_gas hf _ _ _, ?_, rfl, ?_, rfl, rfl, rfl⟩
  · show s.pc.succ = _
    rw [hpc]
    exact YulEvmCompiler.succ_ofNat (by
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega)
  · rw [hfork, hcost]

theorem step_revert00 {code : ByteArray} {pre post : List UInt8}
    {rest : List UInt256} {s : State} (hf : NestedFrame code s)
    (hcode : code = mkCode (pre ++ (Instr.op .REVERT).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = ⟨0⟩ :: ⟨0⟩ :: rest)
    (hcap : s.stack.length + Operation.pushArity .REVERT ≤
      1024 + Operation.popArity .REVERT)
    (hgas : Gas.revertTotal s ⟨0⟩ ⟨0⟩ ≤ s.gasAvailable) :
    ∃ s', Step s s' ∧
      s'.halt = .Reverted ∧ s'.hReturn.toList = [] ∧
      s'.callStack = s.callStack ∧
      s'.accountMap = s.accountMap := by
  obtain ⟨hb, hplain⟩ := opTable_roundtrip (yop := .revert) rfl
  have hdec := decoded_op_nested hf hcode hpc hb hplain
    (opTable_available (yop := .revert) rfl)
  refine ⟨_, Step.running hf.running hf.noPrecompile
    (StepRunning.revert s ⟨0⟩ ⟨0⟩ rest hdec hstk hgas hcap),
    rfl, ?_, rfl, rfl⟩
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [hz, readPadded_zero_toList]

theorem layout_pushK (k dest : Nat) (restB : List UInt8) :
    assembleBytes (lockPrefixInstrs k dest) ++ restB =
      (Instr.pushMin (UInt256.ofNat k)).bytes ++
        ((Instr.op .ISZERO).bytes ++
          ((Instr.op .POP).bytes ++
            ((Instr.pushMin ⟨0⟩).bytes ++
              ((Instr.op .TLOAD).bytes ++
                ((Instr.op .ISZERO).bytes ++
                  ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
                    ((Instr.op .JUMPI).bytes ++
                      ((Instr.pushMin ⟨0⟩).bytes ++
                        ((Instr.pushMin ⟨0⟩).bytes ++
                          ((Instr.op .REVERT).bytes ++
                            ((Instr.op .JUMPDEST).bytes ++ restB))))))))))) := by
  simp [lockPrefixInstrs, assembleBytes, List.append_assoc]

theorem nested_lock_reverts {c : ContractDef} {rt : YBlock} {is : List Instr}
    {self : AccountAddress} {s : State} {f : Frame} {rest : List Frame}
    (hrt : runtimeBlock c = some rt) (hcomp : compileBlock rt = some is)
    (hf : NestedFrame (assemble is) s)
    (hself : s.executionEnv.address = self)
    (hacc : (s.accountMap self).code = assemble is)
    (hpc : s.pc = UInt256.ofNat 0)
    (hstack : s.stack = [])
    (hlock : (s.accountMap self).tstorage ⟨0⟩ ≠ ⟨0⟩)
    (hcs : s.callStack = f :: rest)
    (hcreate : f.createAddr = none) :
    ∃ b, b ≤ lockPrefixGasBound ∧
      (b ≤ s.gasAvailable →
        ∃ sR sP, Steps s sR ∧ sR.halt = .Reverted ∧ sR.hReturn.toList = [] ∧
          sR.callStack = f :: rest ∧ Step sR sP ∧
          sP.accountMap = f.snapAccountMap ∧
          sP.substate = f.snapSubstate) := by
  obtain ⟨k, dest, restB, hk, hpos, hdest, hbytes⟩ :=
    runtime_prefix_instrs hrt hcomp
  have _hpin : s.executionEnv.code = (s.accountMap self).code :=
    hf.hcode.trans hacc.symm
  have hfull : assemble is =
      mkCode (assembleBytes (lockPrefixInstrs k dest) ++ restB) := by
    rw [assemble_eq_mkCode, hbytes]
  rw [layout_pushK] at hfull
  refine ⟨lockPrefixGasBound, le_rfl, ?_⟩
  intro hgas0
  have hg : 200 ≤ s.gasAvailable := by
    simpa [lockPrefixGasBound] using hgas0
  have hk0 : (UInt256.ofNat k).toNat = k :=
    YulEvmCompiler.toNat_ofNat_of_lt hk
  have hwpos : 0 < Instr.byteWidth (UInt256.ofNat k).toNat := by
    rw [hk0]; exact byteWidth_pos hpos
  have ⟨s1, st1, hf1, hpc1, hstk1, hg1, hcs1, ham1, haddr1⟩ :=
    step_pushMin_pos (pre := [])
      (post := (Instr.op .ISZERO).bytes ++
        ((Instr.op .POP).bytes ++
          ((Instr.pushMin ⟨0⟩).bytes ++
            ((Instr.op .TLOAD).bytes ++
              ((Instr.op .ISZERO).bytes ++
                ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
                  ((Instr.op .JUMPI).bytes ++
                    ((Instr.pushMin ⟨0⟩).bytes ++
                      ((Instr.pushMin ⟨0⟩).bytes ++
                        ((Instr.op .REVERT).bytes ++
                          ((Instr.op .JUMPDEST).bytes ++ restB)))))))))))
      (v := UInt256.ofNat k) hf
      (by simpa [List.append_assoc] using hfull)
      (by simpa [hpc])
      hwpos (by simp [hstack]) (by omega)
  rw [hstack] at hstk1
  have ⟨s2, st2, hf2, hpc2, hstk2, hg2, hcs2, ham2, haddr2⟩ :=
    step_iszero (pre := (Instr.pushMin (UInt256.ofNat k)).bytes)
      (post := (Instr.op .POP).bytes ++
        ((Instr.pushMin ⟨0⟩).bytes ++
          ((Instr.op .TLOAD).bytes ++
            ((Instr.op .ISZERO).bytes ++
              ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
                ((Instr.op .JUMPI).bytes ++
                  ((Instr.pushMin ⟨0⟩).bytes ++
                    ((Instr.pushMin ⟨0⟩).bytes ++
                      ((Instr.op .REVERT).bytes ++
                        ((Instr.op .JUMPDEST).bytes ++ restB))))))))))
      (a := UInt256.ofNat k) (rest := []) hf1
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc1]
        congr 1
        simp [Instr.length_bytes_pushMin]; try omega)
      hstk1 (by simp [Operation.pushArity, Operation.popArity, hstk1])
      (by omega)
  have ⟨s3, st3, hf3, hpc3, hstk3, hg3, hcs3, ham3, haddr3⟩ :=
    step_pop
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes)
      (post := (Instr.pushMin ⟨0⟩).bytes ++
        ((Instr.op .TLOAD).bytes ++
          ((Instr.op .ISZERO).bytes ++
            ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
              ((Instr.op .JUMPI).bytes ++
                ((Instr.pushMin ⟨0⟩).bytes ++
                  ((Instr.pushMin ⟨0⟩).bytes ++
                    ((Instr.op .REVERT).bytes ++
                      ((Instr.op .JUMPDEST).bytes ++ restB)))))))))
      (a := UInt256.isZero (UInt256.ofNat k)) (rest := []) hf2
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc2]
        congr 1
        simp [Instr.length_bytes_pushMin]; try omega)
      hstk2 (by simp [Operation.pushArity, Operation.popArity, hstk2])
      (by omega)
  have ⟨s4, st4, hf4, hpc4, hstk4, hg4, hcs4, ham4, haddr4⟩ :=
    step_push0
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes)
      (post := (Instr.op .TLOAD).bytes ++
        ((Instr.op .ISZERO).bytes ++
          ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
            ((Instr.op .JUMPI).bytes ++
              ((Instr.pushMin ⟨0⟩).bytes ++
                ((Instr.pushMin ⟨0⟩).bytes ++
                  ((Instr.op .REVERT).bytes ++
                    ((Instr.op .JUMPDEST).bytes ++ restB))))))))
      hf3
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc3]
        congr 1
        simp [Instr.length_bytes_pushMin]; try omega)
      (by simp [hstk3]) (by omega)
  rw [hstk3] at hstk4
  have ⟨s5, st5, hf5, hpc5, hstk5, hg5, hcs5, ham5, haddr5⟩ :=
    step_tload
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes)
      (post := (Instr.op .ISZERO).bytes ++
        ((Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
          ((Instr.op .JUMPI).bytes ++
            ((Instr.pushMin ⟨0⟩).bytes ++
              ((Instr.pushMin ⟨0⟩).bytes ++
                ((Instr.op .REVERT).bytes ++
                  ((Instr.op .JUMPDEST).bytes ++ restB)))))))
      (key := ⟨0⟩) (rest := []) hf4
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc4]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push]; try omega)
      hstk4 (by simp [Operation.pushArity, Operation.popArity, hstk4])
      (by omega)
  have hlockv :
      (s5.accountMap s5.executionEnv.address).tstorage ⟨0⟩ =
        (s.accountMap self).tstorage ⟨0⟩ := by
    rw [ham5, haddr5, ham4, haddr4, ham3, haddr3, ham2, haddr2, ham1, haddr1,
      hself]
  have ⟨s6, st6, hf6, hpc6, hstk6, hg6, hcs6, ham6, haddr6⟩ :=
    step_iszero
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes)
      (post := (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        ((Instr.op .JUMPI).bytes ++
          ((Instr.pushMin ⟨0⟩).bytes ++
            ((Instr.pushMin ⟨0⟩).bytes ++
              ((Instr.op .REVERT).bytes ++
                ((Instr.op .JUMPDEST).bytes ++ restB))))))
      (a := (s4.accountMap s4.executionEnv.address).tstorage ⟨0⟩) (rest := [])
      hf5
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc5]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push]; try omega)
      hstk5 (by simp [Operation.pushArity, Operation.popArity, hstk5])
      (by omega)
  have hwle := byteWidth_le_32_of_lt hk
  have hdestLt : dest < 2 ^ 256 := by
    rw [hdest]; omega
  have hdestW : dest < 256 ^ labelWidth := by
    rw [hdest]; simp [labelWidth]; omega
  have ⟨s7, st7, hf7, hpc7, hstk7, hg7, hcs7, ham7, haddr7⟩ :=
    step_push2
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++ (Instr.op .ISZERO).bytes)
      (post := (Instr.op .JUMPI).bytes ++
        ((Instr.pushMin ⟨0⟩).bytes ++
          ((Instr.pushMin ⟨0⟩).bytes ++
            ((Instr.op .REVERT).bytes ++
              ((Instr.op .JUMPDEST).bytes ++ restB)))))
      (dest := dest) hf6
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc6]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push]; try omega)
      hdestLt hdestW (by simp [hstk6]) (by omega)
  rw [hstk6] at hstk7
  have ⟨s8, st8, hf8, hpc8, hstk8, hg8, hcs8, ham8, haddr8⟩ :=
    step_jumpi_notTaken
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes)
      (post := (Instr.pushMin ⟨0⟩).bytes ++
        ((Instr.pushMin ⟨0⟩).bytes ++
          ((Instr.op .REVERT).bytes ++
            ((Instr.op .JUMPDEST).bytes ++ restB))))
      (dest := UInt256.ofNat dest)
      (cond := UInt256.isZero
        ((s4.accountMap s4.executionEnv.address).tstorage ⟨0⟩))
      (rest := []) hf7
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc7]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push,
          labelWidthFin_val]; try omega)
      hstk7 (by
        have hlock4 :
            (s4.accountMap s4.executionEnv.address).tstorage ⟨0⟩ =
              (s.accountMap self).tstorage ⟨0⟩ := by
          rw [ham4, haddr4, ham3, haddr3, ham2, haddr2, ham1, haddr1, hself]
        simpa [hlock4] using not_isTrue_isZero_of_ne hlock)
      (by simp [Operation.pushArity, Operation.popArity, hstk7]) (by omega)
  have ⟨s9, st9, hf9, hpc9, hstk9, hg9, hcs9, ham9, haddr9⟩ :=
    step_push0
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        (Instr.op .JUMPI).bytes)
      (post := (Instr.pushMin ⟨0⟩).bytes ++
        ((Instr.op .REVERT).bytes ++
          ((Instr.op .JUMPDEST).bytes ++ restB)))
      hf8
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc8]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push,
          labelWidthFin_val]; try omega)
      (by simp [hstk8]) (by omega)
  rw [hstk8] at hstk9
  have ⟨s10, st10, hf10, hpc10, hstk10, hg10, hcs10, ham10, haddr10⟩ :=
    step_push0
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        (Instr.op .JUMPI).bytes ++ (Instr.pushMin ⟨0⟩).bytes)
      (post := (Instr.op .REVERT).bytes ++
        ((Instr.op .JUMPDEST).bytes ++ restB))
      hf9
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc9]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push,
          labelWidthFin_val]; try omega)
      (by simp [hstk9]) (by omega)
  rw [hstk9] at hstk10
  have ⟨sR, stR, hhaltR, hretR, hcsR, hamR⟩ :=
    step_revert00
      (pre := (Instr.pushMin (UInt256.ofNat k)).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.op .POP).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.op .TLOAD).bytes ++ (Instr.op .ISZERO).bytes ++
        (Instr.push labelWidthFin (UInt256.ofNat dest)).bytes ++
        (Instr.op .JUMPI).bytes ++ (Instr.pushMin ⟨0⟩).bytes ++
        (Instr.pushMin ⟨0⟩).bytes)
      (post := (Instr.op .JUMPDEST).bytes ++ restB) (rest := []) hf10
      (by simpa [List.append_assoc] using hfull)
      (by
        rw [hpc10]
        congr 1
        simp [Instr.length_bytes_pushMin, pushMin_zero, Instr.length_bytes_push,
          labelWidthFin_val]; try omega)
      hstk10 (by simp [Operation.pushArity, Operation.popArity, hstk10])
      (by rw [revertTotal_zero]; omega)
  have hcsR' : sR.callStack = f :: rest := by
    rw [hcsR, hcs10, hcs9, hcs8, hcs7, hcs6, hcs5, hcs4, hcs3, hcs2, hcs1, hcs]
  let sP := sR.resumeRevert f rest
  refine ⟨sR, sP, ?_, hhaltR, hretR, hcsR', ?_, rfl, rfl⟩
  · exact .trans st1 <| .trans st2 <| .trans st3 <| .trans st4 <|
      .trans st5 <| .trans st6 <| .trans st7 <| .trans st8 <|
      .trans st9 <| .trans st10 <| .trans stR (.refl _)
  · exact Step.returning (StepReturn.callReturnRevert sR f rest hhaltR hcsR'
      hcreate)

end Proof

end Lsc.Compiler
