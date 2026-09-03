import Lsc.Compile.Bytecode.AbiDispatchProofs
import Lsc.Compile.IR.WordEvalLemmas
import Lsc.Lib.Math.EvmProofs

/-!
Composed `EVM.X` theorem for production `sqrtProduct` bytecode.

Split from `EvmProofs.lean` to keep the semantic layer buildable without loading the full
ABI-dispatch composition in the same elaboration unit.
-/

namespace Lsc.Math.EvmProofs

open Lsc
open Lsc.Compile
open Lsc.Compile.IR
open Lsc.Compile.IR.Builder
open Lsc.Compile.Bytecode

set_option maxHeartbeats 4000000 in
private theorem sqrtProduct_semantic_result
    (st : EvmYul.EVM.State) (nat : IRState) (a b : EvmYul.UInt256)
    (calldata : ByteArray)
    (hwf : AbiDispatch.WellFormed
      (computeSelector sqrtProductFunction).toNat [a, b] calldata)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hbaseAgree : (AbiDispatch.machineWordState st).Agrees nat)
    (hproduct : a.toNat * b.toNat < EvmYul.UInt256.size)
    (hsum : a.toNat * b.toNat + scale / 2 < EvmYul.UInt256.size)
    (hwidened :
      ((a.toNat * b.toNat + scale / 2) / scale) * scale < 2 ^ 256)
    (hsqrtNoWrap :
      let natAB := (nat.setLocal "a" a.toNat).setLocal "b" b.toNat
      StmtNoWrap { state := natAB } sqrtProductBody) :
    ∃ (returned : EvmYul.UInt256)
        (hfloor :
          returned.toNat =
              Nat.sqrt (((a.toNat * b.toNat + scale / 2) / scale) * scale) ∧
            returned.toNat * returned.toNat ≤
              ((a.toNat * b.toNat + scale / 2) / scale) * scale ∧
            ((a.toNat * b.toNat + scale / 2) / scale) * scale <
              (returned.toNat + 1) * (returned.toNat + 1)),
      ViewProgram (AbiDispatch.machineWordState st) sqrtProductProgram returned ∧
        ViewProgramReloadSafe ({} : Ctx)
          (AbiDispatch.machineWordState st) sqrtProductProgram ∧
        ViewProgramReloadSafe ctxAB wordAB sqrtProductBody := by
  let word := AbiDispatch.machineWordState st
  let wordAB := (word.setLocal "a" a).setLocal "b" b
  let natAB := (nat.setLocal "a" a.toNat).setLocal "b" b.toNat
  have haWord : word.calldata 4 = a :=
    AbiDispatch.machineWordState_argument hwf st hcalldata 0 (by simp)
  have hbWord : word.calldata 36 = b := by
    simpa using AbiDispatch.machineWordState_argument hwf st hcalldata 1 (by simp)
  have hagreeAB : wordAB.Agrees natAB := by
    apply WordState.Agrees.setLocal
    · apply WordState.Agrees.setLocal nat word hbaseAgree "a" a a.toNat
      rfl
    · rfl
  have hExprNoWrap : ExprNoWrap natAB widenedExpr := by
    have hwideSize :
        ((a.toNat * b.toNat + scale / 2) / scale) * scale < EvmYul.UInt256.size := by
      simpa [EvmYul.UInt256.size] using hwidened
    simp [ExprNoWrap, widenedExpr, roundedExpr, natAB, scale, evalExpr]
    refine And.intro (And.intro (And.intro trivial trivial hproduct)
      (And.intro (And.intro trivial trivial (And.intro trivial trivial)) hsum))
      (And.intro trivial hwideSize)
  obtain ⟨widenedWord, hwidenedEval, _⟩ :=
    evalExprWord_agrees natAB wordAB widenedExpr hagreeAB hExprNoWrap
  have hinput :=
    widenedExpr_viewValue word a b widenedWord haWord hbWord hwidenedEval
  obtain ⟨returned, hbodyView, hbodyReload⟩ :=
    sqrtProductBody_viewProgram wordAB widenedWord hinput
  have hbodyView' :
      let wordAB :=
        (word.setLocal "a" (word.calldata 4)).setLocal "b" (word.calldata 36)
      ViewProgram wordAB sqrtProductBody returned := by
    dsimp only
    simpa [wordAB, haWord, hbWord] using hbodyView
  have hbodyReload' :
      let wordAB :=
        (word.setLocal "a" (word.calldata 4)).setLocal "b" (word.calldata 36)
      ViewProgramReloadSafe ctxAB wordAB sqrtProductBody := by
    dsimp only
    simpa [wordAB, haWord, hbWord] using hbodyReload
  have hprogramSpec :=
    sqrtProductProgram_of_body word returned hbodyView' hbodyReload'
  have hfloor :=
    sqrtProductBody_floor_explicit natAB wordAB returned a.toNat b.toNat
      (by simp [natAB]) (by simp [natAB]) hagreeAB
      (by rfl) hproduct hsum hsqrtNoWrap hwidened hbodyView
  have hfloor' :
      returned.toNat =
          Nat.sqrt (((a.toNat * b.toNat + scale / 2) / scale) * scale) ∧
        returned.toNat * returned.toNat ≤
          ((a.toNat * b.toNat + scale / 2) / scale) * scale ∧
        ((a.toNat * b.toNat + scale / 2) / scale) * scale <
          (returned.toNat + 1) * (returned.toNat + 1) := by
    simpa using hfloor
  exact ⟨returned, hfloor', hprogramSpec.1, hprogramSpec.2, hbodyReload'⟩

set_option maxHeartbeats 2000000 in
private theorem sqrtProduct_production_X
    (cfg : Config) (contractDef : ContractDef)
    (instrs resolved resolvedBefore resolvedBody resolvedAfter suffix code : List Instr)
    (beforePairs afterPairs : List (Nat × Nat)) (targetPc revertPc : Nat)
    (validJumps : Array EvmYul.UInt256) (st : EvmYul.EVM.State)
    (inputCtx bodyOut : Ctx) (returned : EvmYul.UInt256)
    (a b : EvmYul.UInt256) (calldata : ByteArray)
    (hencode : Bytecode.encode instrs = .ok code)
    (hresolveFull :
      Bytecode.resolveInstrs (Bytecode.fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : Bytecode.EvmYulBridge.EncodablePlainInstrs resolved)
    (hcodeLimit : code.size + 33 < 2 ^ 64)
    (hfullDispatchShape :
      resolved =
        Bytecode.AbiDispatch.resolvedCalldataGuard revertPc ++
          (Bytecode.AbiDispatch.resolvedSelectorBranches
            (beforePairs ++
              ((computeSelector sqrtProductFunction).toNat, targetPc) :: afterPairs) ++
            suffix))
    (hbodyShape :
      resolved = resolvedBefore ++ [.op .JUMPDEST] ++ resolvedBody ++ resolvedAfter)
    (htargetPc : targetPc = (resolvedBefore.map (Bytecode.instrByteSize [])).sum)
    (hlabel :
      Bytecode.lookupLabel (Bytecode.fixpointLabels instrs) sqrtProductFunction.name =
        .ok targetPc)
    (hsafe : Bytecode.AbiDispatch.PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hwf : Bytecode.AbiDispatch.WellFormed
      (computeSelector sqrtProductFunction).toNat [a, b] calldata)
    (hwidthSelected : Bytecode.pushWidth (computeSelector sqrtProductFunction).toNat ≤ 32)
    (hwidthBefore : ∀ pair ∈ beforePairs, Bytecode.pushWidth pair.1 ≤ 32)
    (hdistinct :
      ∀ pair ∈ beforePairs,
        (EvmYul.UInt256.ofNat pair.1) ≠ EvmYul.UInt256.ofNat (computeSelector sqrtProductFunction).toNat)
    (htargetJump' : (EvmYul.UInt256.ofNat targetPc) ∈ validJumps)
    (hgen :
      Codegen.stmt (Ctx.forFunction inputCtx sqrtProductFunction.name) sqrtProductProgram =
        .ok (resolvedBody, bodyOut))
    (hprogram : ViewProgram (AbiDispatch.machineWordState st) sqrtProductProgram returned)
    (hprogramReload :
      ViewProgramReloadSafe (Ctx.forFunction inputCtx sqrtProductFunction.name)
        (AbiDispatch.machineWordState st) sqrtProductProgram) :
    ∃ (fuel : Nat) (final : EvmYul.EVM.State),
      EvmYul.EVM.X fuel validJumps st = .ok (.success final returned.toByteArray) := by
  obtain ⟨final, hX, _⟩ :=
    Bytecode.AbiDispatch.productionMatchingSelector_X_returns
      instrs resolved resolvedBefore resolvedBody resolvedAfter suffix code
      beforePairs afterPairs targetPc revertPc sqrtProductFunction.name validJumps st
      inputCtx bodyOut hencode hresolveFull hencodable hcodeLimit hfullDispatchShape
      hbodyShape htargetPc hlabel hsafe hcode hpc hstack hmemory hcalldata hwf
      hwidthSelected hwidthBefore hdistinct htargetJump' hgen hprogram hprogramReload
  exact ⟨resolvedBody.length + 2 + 8 * (beforePairs.length + 1) + 5, final, hX⟩

/-!
`EVM.X` takes the valid-jump array as an opaque input.  Consequently the final production theorem
retains membership of the selected function entry in that array; it does not claim to reconstruct
EvmYul's `D_J` computation.  All symbolic/resolved dispatcher and body shapes are nevertheless
derived internally from the successful production contract build and encoding.
-/

set_option maxHeartbeats 4000000 in
/-- End-to-end execution of the exact `sqrtProductExpr` implementation through the validated ABI
dispatcher and production bytecode encoder.

`hsqrtNoWrap` is the dynamic word/Nat agreement obligation for the shared sqrt binding trace.
The three public arithmetic bounds discharge the source product, rounding sum, and widened input;
the trace obligation records the remaining internal Newton/magnitude intermediates.

The explicit `htargetJump` premise is the `D_J` opacity boundary: callers must supply membership
of the resolved `sqrtProduct` entry in `validJumps`; this theorem does not reconstruct it. -/
theorem validatedContract_sqrtProduct_X_returns
    (cfg : Config) (contractDef : ContractDef)
    (instrs : List Instr) (code : ByteArray)
    (validJumps : Array EvmYul.UInt256) (st : EvmYul.EVM.State)
    (nat : IRState) (a b : EvmYul.UInt256) (calldata : ByteArray)
    (hvalid : Checks.validateAll contractDef = .ok contractDef)
    (hfn : sqrtProductFunction ∈
      Bytecode.Contract.dispatchedFunctions contractDef)
    (hcontract : Bytecode.Contract.contract cfg contractDef = .ok instrs)
    (hencode : Bytecode.encode instrs = .ok code)
    (hencodable :
      ∀ resolved,
        Bytecode.resolveInstrs (Bytecode.fixpointLabels instrs) instrs =
            .ok resolved →
          Bytecode.EvmYulBridge.EncodablePlainInstrs resolved)
    (hcodeLimit : code.size + 33 < 2 ^ 64)
    (hselectorWidths :
      ∀ fn ∈ Bytecode.Contract.dispatchedFunctions contractDef,
        Bytecode.pushWidth (computeSelector fn).toNat ≤ 32)
    (hwf : Bytecode.AbiDispatch.WellFormed
      (computeSelector sqrtProductFunction).toNat [a, b] calldata)
    (hsafe : Bytecode.AbiDispatch.PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code)
    (hpc : st.pc = .ofNat 0) (hstack : st.stack = [])
    (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hbaseAgree : (Bytecode.AbiDispatch.machineWordState st).Agrees nat)
    (hproduct : a.toNat * b.toNat < EvmYul.UInt256.size)
    (hsum : a.toNat * b.toNat + scale / 2 < EvmYul.UInt256.size)
    (hwidened :
      ((a.toNat * b.toNat + scale / 2) / scale) * scale < 2 ^ 256)
    (hsqrtNoWrap :
      let natAB := (nat.setLocal "a" a.toNat).setLocal "b" b.toNat
      StmtNoWrap { state := natAB } sqrtProductBody)
    (htargetJump :
      (.ofNat
        (AbiDispatch.resolvedSelectorTarget (fixpointLabels instrs)
          sqrtProductFunction) : EvmYul.UInt256) ∈ validJumps) :
    ∃ (fuel : Nat) (final : EvmYul.EVM.State) (r : EvmYul.UInt256),
      EvmYul.EVM.X fuel validJumps st =
        .ok (.success final r.toByteArray) ∧
      r.toNat = Nat.sqrt (((a.toNat * b.toNat + scale / 2) / scale) * scale) ∧
        r.toNat * r.toNat ≤ ((a.toNat * b.toNat + scale / 2) / scale) * scale ∧
        ((a.toNat * b.toNat + scale / 2) / scale) * scale <
          (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨returned, hfloor, hprogram, _hprogramReload, hbodyReload⟩ :=
    sqrtProduct_semantic_result st nat a b calldata hwf hcalldata hbaseAgree
      hproduct hsum hwidened hsqrtNoWrap
  let labels := Bytecode.fixpointLabels instrs
  obtain ⟨resolved, targetPc, dispatch, dispatchCtx, _bodiesCtx,
      beforeBody, afterBody, body, inputCtx, bodyOut, _loweredBody, program,
      resolvedBefore, resolvedBody, resolvedAfter, hlabel, htargetPc,
      hdispatch, hlower, hprogramExtract, hgen, _hemit, hinstrs,
      hresolvedBefore, hresolvedBody, hresolvedAfter, hresolved⟩ :=
    Bytecode.AbiDispatch.contract_extract_view_body_resolved cfg contractDef
      sqrtProductFunction instrs code hfn rfl hcontract hencode
  have hprogramEq : program = sqrtProductProgram := by
    have hwhole := lower_function_eq cfg
    simp only [Lower.function, hlower, bind, Except.bind] at hwhole
    injection hwhole with hloweredProgram
    rw [hprogramExtract, hloweredProgram]
  subst program
  have hdispatchResolved :
      ∃ resolvedDispatch resolvedBodiesBefore,
        Bytecode.resolveInstrs labels dispatch = .ok resolvedDispatch ∧
        Bytecode.resolveInstrs labels beforeBody = .ok resolvedBodiesBefore ∧
        resolvedBefore = resolvedDispatch ++ resolvedBodiesBefore := by
    rw [Bytecode.AbiDispatch.resolveInstrs_append] at hresolvedBefore
    cases hd : Bytecode.resolveInstrs labels dispatch with
    | error err => simp [hd, Bind.bind, Except.bind] at hresolvedBefore
    | ok resolvedDispatch =>
        cases hbdy : Bytecode.resolveInstrs labels beforeBody with
        | error err => simp [hd, hbdy, Bind.bind, Except.bind] at hresolvedBefore
        | ok resolvedBodiesBefore =>
            simp [hd, hbdy, Bind.bind, Except.bind] at hresolvedBefore
            exact ⟨resolvedDispatch, resolvedBodiesBefore,
              hd, hbdy, hresolvedBefore.symm⟩
  obtain ⟨resolvedDispatch, resolvedBodiesBefore, hresolveDispatch,
      _hresolveBodiesBefore, hresolvedBeforeEq⟩ := hdispatchResolved
  obtain ⟨revertPc, _hrevert, hdispatchShape⟩ :=
    AbiDispatch.resolveSelectorDispatch_shape cfg
      (Contract.dispatchedFunctions contractDef) {}
      dispatch dispatchCtx labels resolvedDispatch hdispatch
      (by simpa [labels] using hresolveDispatch)
  obtain ⟨beforeFns, afterFns, hfns, hdistinctFns⟩ :=
    Bytecode.AbiDispatch.validated_preceding_selector_distinct
      contractDef sqrtProductFunction hvalid hfn
  let beforePairs := Bytecode.AbiDispatch.resolvedSelectorPairs labels beforeFns
  let afterPairs := Bytecode.AbiDispatch.resolvedSelectorPairs labels afterFns
  have hpairs :
      Bytecode.AbiDispatch.resolvedSelectorPairs labels
          (Bytecode.Contract.dispatchedFunctions contractDef) =
        beforePairs ++
          ((computeSelector sqrtProductFunction).toNat, targetPc) :: afterPairs := by
    rw [hfns]
    simp [beforePairs, afterPairs, Bytecode.AbiDispatch.resolvedSelectorPairs,
      Bytecode.AbiDispatch.resolvedSelectorTarget, hlabel]
  let suffix :=
    [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++
      Bytecode.Contract.dispatchRevert cfg ++ resolvedBodiesBefore ++
      [.op .JUMPDEST] ++ resolvedBody ++ resolvedAfter
  have hfullDispatchShape :
      resolved =
        Bytecode.AbiDispatch.resolvedCalldataGuard revertPc ++
          (Bytecode.AbiDispatch.resolvedSelectorBranches
            (beforePairs ++
              ((computeSelector sqrtProductFunction).toNat, targetPc) :: afterPairs) ++
            suffix) := by
    rw [hresolved, hresolvedBeforeEq, hdispatchShape, hpairs]
    simp [suffix, List.append_assoc]
  have hbodyShape :
      resolved = resolvedBefore ++ [.op .JUMPDEST] ++ resolvedBody ++ resolvedAfter :=
    hresolved
  have htargetJump' : (EvmYul.UInt256.ofNat targetPc) ∈ validJumps := by
    simpa [Bytecode.AbiDispatch.resolvedSelectorTarget, labels, hlabel] using htargetJump
  have hwidthBefore :
      ∀ pair ∈ beforePairs, Bytecode.pushWidth pair.1 ≤ 32 :=
    Bytecode.AbiDispatch.resolvedSelectorPairs_pushWidth_le labels beforeFns
      (fun fn hfnBefore =>
        hselectorWidths fn (by rw [hfns]; exact List.mem_append_left _ hfnBefore))
  have hdistinct :
      ∀ pair ∈ beforePairs,
        (EvmYul.UInt256.ofNat pair.1) ≠ EvmYul.UInt256.ofNat (computeSelector sqrtProductFunction).toNat :=
    Bytecode.AbiDispatch.resolvedSelectorPairs_preceding_ne
      sqrtProductFunction labels beforeFns hdistinctFns
  have hresolveFull :
      Bytecode.resolveInstrs labels instrs = .ok resolved := by
    rw [hinstrs]
    rw [show
      dispatch ++ beforeBody ++ [.jumpDest sqrtProductFunction.name] ++ body ++ afterBody =
        (dispatch ++ beforeBody) ++ [.jumpDest sqrtProductFunction.name] ++
          body ++ afterBody by simp [List.append_assoc]]
    rw [Bytecode.AbiDispatch.resolveInstrs_append, hresolvedBefore]
    rw [Bytecode.AbiDispatch.resolveInstrs_append]
    simp only [Bytecode.resolveInstrs, Bytecode.resolveInstr, Bind.bind, Except.bind]
    rw [Bytecode.AbiDispatch.resolveInstrs_append, hresolvedBody, hresolvedAfter]
    simp only [Bind.bind, Except.bind]
    exact congrArg Except.ok hresolved.symm
  have hprogramReload' :=
    sqrtProductProgram_forFunction_reload inputCtx (AbiDispatch.machineWordState st) hbodyReload
  obtain ⟨fuel, final, hX⟩ :=
    sqrtProduct_production_X cfg contractDef instrs resolved resolvedBefore
      resolvedBody resolvedAfter suffix code beforePairs afterPairs targetPc revertPc
      validJumps st inputCtx bodyOut returned a b calldata hencode hresolveFull
      (hencodable resolved hresolveFull) hcodeLimit hfullDispatchShape hbodyShape htargetPc
      hlabel hsafe hcode hpc hstack hmemory hcalldata hwf
      (hselectorWidths sqrtProductFunction hfn) hwidthBefore hdistinct htargetJump'
      (by simpa [hprogramEq] using hgen) hprogram hprogramReload'
  refine ⟨fuel, final, returned, hX, ?_⟩
  simpa using hfloor

end Lsc.Math.EvmProofs
