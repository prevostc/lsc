import Lsc.Compile.Bytecode.Contract
import Lsc.Compile.Bytecode.CodegenProofs

namespace Lsc.Compile.Bytecode.AbiDispatch

open EvmYul EvmYul.EVM EvmYul.Operation
open Lsc.Compile
open Lsc.Compile.Abi
open Lsc.Compile.Bytecode
open Lsc.Compile.Bytecode.EvmYulBridge
open Lsc.Compile.Bytecode.EvmYulTrust
open Lsc.Compile.Bytecode.Contract

abbrev Word := EvmYul.UInt256

def selectorBytes (selector : Nat) : ByteArray :=
  natToBigEndianBytes selector 4

def argumentBytes : List Word → ByteArray
  | [] => ByteArray.empty
  | value :: rest => value.toByteArray ++ argumentBytes rest

def encodeCall (selector : Nat) (args : List Word) : ByteArray :=
  selectorBytes selector ++ argumentBytes args

def decodeSelector (calldata : ByteArray) : Word :=
  EvmYul.UInt256.shiftRight
    (EvmYul.uInt256OfByteArray (calldata.readBytes 0 32))
    (.ofNat 224)

def decodeArgument (calldata : ByteArray) (i : Nat) : Word :=
  EvmYul.uInt256OfByteArray (calldata.readBytes (4 + 32 * i) 32)

/-- ABI calldata as consumed by generated library views. This relation is deliberately phrased
through EvmYul's own calldata reader, so no parallel decoder semantics is introduced. -/
structure WellFormed (selector : Nat) (args : List Word) (calldata : ByteArray) : Prop where
  selector_lt : selector < 2 ^ 32
  size : calldata.size = 4 + 32 * args.length
  offsets_lt : 4 + 32 * args.length < 2 ^ 256
  selector_eq : decodeSelector calldata = .ofNat selector
  argument_eq : ∀ i (hi : i < args.length), decodeArgument calldata i = args[i]

theorem selectorBytes_size (selector : Nat) :
    (selectorBytes selector).size = 4 := by
  change (natToLittleEndianBytes selector 4).reverse.length = 4
  simp [natToLittleEndianBytes_length]

theorem argumentBytes_size (args : List Word) :
    (argumentBytes args).size = 32 * args.length := by
  induction args with
  | nil => rfl
  | cons value rest ih =>
      simp [argumentBytes, ByteArray.size_append, uint256_toByteArray_size, ih]
      omega

theorem encodeCall_size (selector : Nat) (args : List Word) :
    (encodeCall selector args).size = 4 + 32 * args.length := by
  simp [encodeCall, ByteArray.size_append, selectorBytes_size, argumentBytes_size]

theorem WellFormed.not_short {selector : Nat} {args : List Word} {calldata : ByteArray}
    (h : WellFormed selector args calldata) :
    ¬ calldata.size < 4 := by
  rw [h.size]
  omega

theorem WellFormed.argument_offset {selector : Nat} {args : List Word}
    {calldata : ByteArray} (h : WellFormed selector args calldata)
    (i : Nat) (hi : i < args.length) :
    EvmYul.State.calldataload
        ({ (default : EvmYul.State .EVM) with executionEnv.calldata := calldata })
        (.ofNat (4 + 32 * i)) =
      args[i] := by
  have hoff : 4 + 32 * i < EvmYul.UInt256.size := by
    change 4 + 32 * i < 2 ^ 256
    exact lt_of_le_of_lt (by omega) h.offsets_lt
  have htoNat :
      (EvmYul.UInt256.ofNat (4 + 32 * i)).toNat = 4 + 32 * i := by
    change (4 + 32 * i) % EvmYul.UInt256.size = 4 + 32 * i
    exact Nat.mod_eq_of_lt hoff
  simp only [EvmYul.State.calldataload]
  simp only [htoNat]
  exact h.argument_eq i hi

/-- The WordEval source state obtained directly from an EvmYul execution state. -/
def machineWordState (st : EVM.State) : IR.WordState where
  slots := fun slot => (EvmYul.State.sload st.toState (.ofNat slot)).2
  calldata := fun offset => EvmYul.State.calldataload st.toState (.ofNat offset)

theorem contextAgrees_machineWordState (st : EVM.State) (hstack : st.stack = []) :
    ContextAgrees ({} : Ctx) st (machineWordState st) := by
  apply contextAgrees_empty st (machineWordState st) hstack
  constructor <;> intro offset <;> rfl

theorem machineWordState_argument
    {selector : Nat} {args : List Word} {calldata : ByteArray}
    (h : WellFormed selector args calldata)
    (st : EVM.State) (hcalldata : st.executionEnv.calldata = calldata)
    (i : Nat) (hi : i < args.length) :
    (machineWordState st).calldata (4 + 32 * i) = args[i] := by
  simp only [machineWordState]
  have hoff : 4 + 32 * i < EvmYul.UInt256.size := by
    change 4 + 32 * i < 2 ^ 256
    exact lt_of_le_of_lt (by omega) h.offsets_lt
  have htoNat :
      (EvmYul.UInt256.ofNat (4 + 32 * i)).toNat = 4 + 32 * i := by
    change (4 + 32 * i) % EvmYul.UInt256.size = 4 + 32 * i
    exact Nat.mod_eq_of_lt hoff
  simp only [EvmYul.State.calldataload, htoNat]
  rw [hcalldata]
  exact h.argument_eq i hi

def decodeResult (bytes : ByteArray) : Option Word :=
  if bytes.size = 32 then some (EvmYul.uInt256OfByteArray bytes) else none

structure Result (value : Word) (bytes : ByteArray) : Prop where
  bytes_eq : bytes = value.toByteArray

theorem Result.size {value : Word} {bytes : ByteArray} (h : Result value bytes) :
    bytes.size = 32 := by
  rw [h.bytes_eq]
  exact uint256_toByteArray_size value

theorem selectorDispatch_shape (cfg : Config) (fns : List FunctionDef) (ctx : Ctx) :
    (selectorDispatch cfg fns ctx).1 =
      [.push 4, .op .CALLDATASIZE, .op .LT,
        .pushLabel (selectorRevertLabel ctx),
        .op .JUMPI] ++
      selectorBranches fns ++
      [.pushLabel (selectorRevertLabel ctx),
        .op .JUMP,
        .jumpDest (selectorRevertLabel ctx)] ++
      dispatchRevert cfg := by
  simp [selectorDispatch, selectorRevertLabel, Ctx.freshLabel]

theorem selectorBranches_append (first rest : List FunctionDef) :
    selectorBranches (first ++ rest) =
      selectorBranches first ++ selectorBranches rest := by
  induction first with
  | nil => rfl
  | cons fn first ih =>
      simp only [List.cons_append, selectorBranches, ih]
      simp only [List.append_assoc]

theorem selectorBranches_selected_shape
    (before after : List FunctionDef) (fn : FunctionDef) :
    selectorBranches (before ++ fn :: after) =
      selectorBranches before ++ loadSelector ++
        [.push (computeSelector fn).toNat, .op .EQ,
          .pushLabel fn.name, .op .JUMPI] ++
        selectorBranches after := by
  rw [selectorBranches_append]
  simp only [selectorBranches, List.append_assoc]

def resolvedSelectorTarget (labels : List (String × Nat)) (fn : FunctionDef) : Nat :=
  match lookupLabel labels fn.name with
  | .ok pc => pc
  | .error _ => 0

def resolvedSelectorPairs
    (labels : List (String × Nat)) (fns : List FunctionDef) : List (Nat × Nat) :=
  fns.map fun fn => ((computeSelector fn).toNat, resolvedSelectorTarget labels fn)

theorem resolvedSelectorPairs_fsts
    (labels : List (String × Nat)) (fns : List FunctionDef) :
    (resolvedSelectorPairs labels fns).map Prod.fst =
      fns.map fun fn => (computeSelector fn).toNat := by
  simp [resolvedSelectorPairs]

theorem resolvedSelectorPairs_pushWidth_le
    (labels : List (String × Nat)) (fns : List FunctionDef)
    (hwidth : ∀ fn ∈ fns, pushWidth (computeSelector fn).toNat ≤ 32) :
    ∀ pair ∈ resolvedSelectorPairs labels fns, pushWidth pair.1 ≤ 32 := by
  intro pair hpair
  have hselmem : pair.1 ∈ fns.map fun fn => (computeSelector fn).toNat := by
    rw [← resolvedSelectorPairs_fsts labels fns]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  rcases List.mem_map.mp hselmem with ⟨fn, hfn, hsel⟩
  rw [← hsel]
  exact hwidth fn hfn

theorem resolvedSelectorPairs_preceding_ne
    (fn : FunctionDef) (labels : List (String × Nat)) (beforeFns : List FunctionDef)
    (hdistinct : ∀ current ∈ beforeFns, computeSelector current ≠ computeSelector fn) :
    ∀ pair ∈ resolvedSelectorPairs labels beforeFns,
      (EvmYul.UInt256.ofNat pair.1 : Word) ≠
        EvmYul.UInt256.ofNat (computeSelector fn).toNat := by
  intro pair hpair heq
  have hselmem : pair.1 ∈ beforeFns.map fun current => (computeSelector current).toNat := by
    rw [← resolvedSelectorPairs_fsts labels beforeFns]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  rcases List.mem_map.mp hselmem with ⟨current, hcurrent, hsel⟩
  apply hdistinct current hcurrent
  apply UInt32.ext
  have hw := congrArg EvmYul.UInt256.toNat heq
  change pair.1 % EvmYul.UInt256.size =
    (computeSelector fn).toNat % EvmYul.UInt256.size at hw
  rw [← hsel] at hw
  have hcurrentLt : (computeSelector current).toNat < EvmYul.UInt256.size :=
    lt_trans (UInt32.toNat_lt (computeSelector current))
      (by norm_num [EvmYul.UInt256.size])
  have hfnLt : (computeSelector fn).toNat < EvmYul.UInt256.size :=
    lt_trans (UInt32.toNat_lt (computeSelector fn))
      (by norm_num [EvmYul.UInt256.size])
  rw [Nat.mod_eq_of_lt hcurrentLt, Nat.mod_eq_of_lt hfnLt] at hw
  exact hw

theorem validated_preceding_selector_distinct
    (contractDef : ContractDef) (fn : FunctionDef)
    (hvalid : Checks.validateAll contractDef = .ok contractDef)
    (hfn : fn ∈ dispatchedFunctions contractDef) :
    ∃ before after,
      dispatchedFunctions contractDef = before ++ fn :: after ∧
      ∀ current ∈ before, computeSelector current ≠ computeSelector fn := by
  rcases List.mem_iff_append.mp hfn with ⟨before, after, hdecomp⟩
  have hnodup :
      ((dispatchedFunctions contractDef).map computeSelector).Nodup := by
    simpa only [dispatchedFunctions] using
      Checks.validateAll_selector_nodup contractDef hvalid
  rw [hdecomp, List.map_append] at hnodup
  have hparts := List.nodup_append.mp hnodup
  refine ⟨before, after, hdecomp, ?_⟩
  intro current hcurrent heq
  exact hparts.2.2 (computeSelector current)
    (List.mem_map.mpr ⟨current, hcurrent, rfl⟩)
    (computeSelector fn) (by simp) heq

/-- A successful production contract build is exactly its generated selector dispatcher followed
by the bodies emitted from the dispatcher's output context. -/
theorem contract_exact_output
    (cfg : Config) (contractDef : ContractDef) (contractInstrs : List Instr)
    (hcontract : Contract.contract cfg contractDef = .ok contractInstrs) :
    let fns := dispatchedFunctions contractDef
    ∃ dispatch dispatchCtx bodies bodiesCtx,
      ¬ fns.isEmpty ∧
      selectorDispatch cfg fns {} = (dispatch, dispatchCtx) ∧
      emitFunctionBodies cfg fns dispatchCtx = .ok (bodies, bodiesCtx) ∧
      contractInstrs = dispatch ++ bodies := by
  simp only [Contract.contract] at hcontract ⊢
  split at hcontract
  · simp at hcontract
  · rename_i hnonempty
    cases hdispatch : selectorDispatch cfg (dispatchedFunctions contractDef) {} with
    | mk dispatch dispatchCtx =>
        cases hbodies :
            emitFunctionBodies cfg (dispatchedFunctions contractDef) dispatchCtx with
        | error err =>
            simp [hdispatch, hbodies, Bind.bind, Except.bind] at hcontract
        | ok result =>
            rcases result with ⟨bodies, bodiesCtx⟩
            simp [hdispatch, hbodies, Bind.bind, Except.bind] at hcontract
            subst contractInstrs
            exact ⟨dispatch, dispatchCtx, bodies, bodiesCtx, hnonempty,
              rfl, hbodies, rfl⟩

private theorem emitFunctionBodies_extends_from
    (cfg : Config) (fns : List FunctionDef)
    (acc emitted : List Instr) (ctx outCtx : Ctx)
    (hemit :
      fns.foldlM (init := (acc, ctx)) (emitFunctionBody cfg) =
        .ok (emitted, outCtx)) :
    ∃ suffix, emitted = acc ++ suffix := by
  induction fns generalizing acc ctx with
  | nil =>
      simp only [List.foldlM] at hemit
      injection hemit with hemitted
      rcases Prod.mk.inj hemitted with ⟨ha, _⟩
      subst emitted
      exact ⟨[], by simp⟩
  | cons current rest ih =>
      cases hlower : Lower.function cfg current with
      | error err =>
          simp [List.foldlM, emitFunctionBody, hlower, Bind.bind, Except.bind] at hemit
      | ok program =>
          cases hcodegen :
              Codegen.stmt (Ctx.forFunction ctx current.name)
                (codegenInput current program) with
          | error err =>
              simp [List.foldlM, emitFunctionBody, hlower, hcodegen,
                Bind.bind, Except.bind] at hemit
          | ok result =>
              rcases result with ⟨body, bodyOut⟩
              simp only [List.foldlM, emitFunctionBody, hlower, hcodegen,
                Bind.bind, Except.bind] at hemit
              rcases ih
                  (acc ++ [.jumpDest current.name] ++ body ++
                    (if current.kind == .view then [] else [.op .STOP]))
                  (Ctx.afterFunction bodyOut) hemit with
                ⟨suffix, hsuffix⟩
              refine ⟨[.jumpDest current.name] ++ body ++
                (if current.kind == .view then [] else [.op .STOP]) ++ suffix, ?_⟩
              simpa only [List.append_assoc] using hsuffix

private theorem emitFunctionBodies_extract_from
    (cfg : Config) (fns : List FunctionDef) (fn : FunctionDef)
    (acc emitted : List Instr) (ctx outCtx : Ctx)
    (hfn : fn ∈ fns) (hview : fn.kind = .view)
    (hemit :
      fns.foldlM (init := (acc, ctx)) (emitFunctionBody cfg) =
        .ok (emitted, outCtx)) :
    ∃ before after body inputCtx bodyOut loweredBody program,
      Lower.stmt cfg fn.body = .ok loweredBody ∧
      program = Lower.paramPrologue fn.params 4 loweredBody ∧
      Codegen.stmt (Ctx.forFunction inputCtx fn.name) program =
        .ok (body, bodyOut) ∧
      emitted =
        acc ++ before ++ [.jumpDest fn.name] ++ body ++ after := by
  induction fns generalizing acc ctx with
  | nil => simp at hfn
  | cons current rest ih =>
      simp only [List.mem_cons] at hfn
      cases hlower : Lower.function cfg current with
      | error err =>
          simp [List.foldlM, emitFunctionBody, hlower, Bind.bind, Except.bind] at hemit
      | ok program =>
          cases hcodegen :
              Codegen.stmt (Ctx.forFunction ctx current.name)
                (codegenInput current program) with
          | error err =>
              simp [List.foldlM, emitFunctionBody, hlower, hcodegen,
                Bind.bind, Except.bind] at hemit
          | ok result =>
              rcases result with ⟨body, bodyOut⟩
              simp only [List.foldlM, emitFunctionBody, hlower, hcodegen,
                Bind.bind, Except.bind] at hemit
              rcases hfn with rfl | hfn
              · cases hlowerBody : Lower.stmt cfg fn.body with
                | error err =>
                    simp [Lower.function, hlowerBody, Bind.bind, Except.bind] at hlower
                | ok loweredBody =>
                    have hlowerExact :
                        Lower.function cfg fn =
                          .ok (Lower.paramPrologue fn.params 4 loweredBody) := by
                      simp [Lower.function, hlowerBody, Bind.bind, Except.bind]
                    rw [hlowerExact] at hlower
                    injection hlower with hprogramEq
                    subst program
                    have hviewBool : fn.kind == .view := by simp [hview]
                    rcases emitFunctionBodies_extends_from cfg rest
                        (acc ++ [.jumpDest fn.name] ++ body)
                        emitted (Ctx.afterFunction bodyOut) outCtx
                        (by simpa [hviewBool] using hemit) with
                      ⟨suffix, hsuffix⟩
                    refine ⟨[], suffix, body, ctx, bodyOut, loweredBody,
                      Lower.paramPrologue fn.params 4 loweredBody,
                      rfl, rfl, ?_, ?_⟩
                    · simpa [codegenInput, hview] using hcodegen
                    · simpa only [List.nil_append, List.append_assoc] using hsuffix
              · rcases ih (acc := acc ++ [.jumpDest current.name] ++ body ++
                    (if current.kind == .view then [] else [.op .STOP]))
                    (ctx := Ctx.afterFunction bodyOut) hfn hemit with
                  ⟨before, after, selectedBody, inputCtx, selectedOut,
                    loweredBody, selectedProgram, hlowerSelected, hprogram,
                    hcodeSelected, hemitted⟩
                refine ⟨[.jumpDest current.name] ++ body ++
                    (if current.kind == .view then [] else [.op .STOP]) ++ before,
                  after, selectedBody, inputCtx, selectedOut, loweredBody,
                  selectedProgram, hlowerSelected, hprogram, hcodeSelected, ?_⟩
                simpa only [List.append_assoc] using hemitted

/-- Membership of a selected view function in the production dispatch set determines its exact
lowering, ABI calldata prologue, codegen context/output, and symbolic contract suffix. -/
theorem contract_extract_view_body
    (cfg : Config) (contractDef : ContractDef) (fn : FunctionDef)
    (contractInstrs : List Instr)
    (hfn : fn ∈ dispatchedFunctions contractDef)
    (hview : fn.kind = .view)
    (hcontract : Contract.contract cfg contractDef = .ok contractInstrs) :
    ∃ dispatch dispatchCtx bodiesCtx before after body inputCtx bodyOut loweredBody program,
      selectorDispatch cfg (dispatchedFunctions contractDef) {} =
        (dispatch, dispatchCtx) ∧
      Lower.stmt cfg fn.body = .ok loweredBody ∧
      program = Lower.paramPrologue fn.params 4 loweredBody ∧
      Codegen.stmt (Ctx.forFunction inputCtx fn.name) program =
        .ok (body, bodyOut) ∧
      emitFunctionBodies cfg (dispatchedFunctions contractDef) dispatchCtx =
        .ok (before ++ [.jumpDest fn.name] ++ body ++ after, bodiesCtx) ∧
      contractInstrs =
        dispatch ++ before ++ [.jumpDest fn.name] ++ body ++ after := by
  rcases contract_exact_output cfg contractDef contractInstrs hcontract with
    ⟨dispatch, dispatchCtx, bodies, bodiesCtx, _, hdispatch, hbodies, hcontractInstrs⟩
  rcases emitFunctionBodies_extract_from cfg (dispatchedFunctions contractDef) fn
      [] bodies dispatchCtx bodiesCtx hfn hview
      (by simpa [emitFunctionBodies] using hbodies) with
    ⟨before, after, body, inputCtx, bodyOut, loweredBody, program,
      hlower, hprogram, hcodegen, hbodiesEq⟩
  simp only [List.nil_append] at hbodiesEq
  subst bodies
  refine ⟨dispatch, dispatchCtx, bodiesCtx, before, after, body, inputCtx,
    bodyOut, loweredBody, program, hdispatch, hlower, hprogram, hcodegen,
    hbodies, ?_⟩
  simpa only [List.append_assoc] using hcontractInstrs

theorem resolveInstrs_append (labels : List (String × Nat)) (first rest : List Instr) :
    resolveInstrs labels (first ++ rest) = (do
      let resolvedFirst ← resolveInstrs labels first
      let resolvedRest ← resolveInstrs labels rest
      Except.ok (resolvedFirst ++ resolvedRest)) := by
  induction first with
  | nil =>
      cases hrest : resolveInstrs labels rest <;>
        simp [resolveInstrs, hrest, Bind.bind, Except.bind]
  | cons instr first ih =>
      simp only [List.cons_append, resolveInstrs]
      cases hhead : resolveInstr labels instr with
      | error err => simp [Bind.bind, Except.bind]
      | ok head =>
          rw [ih]
          cases resolveInstrs labels first <;>
            cases resolveInstrs labels rest <;>
            simp [Bind.bind, Except.bind, List.append_assoc]

private theorem selectorBranches_mem_pushLabel
    (fns : List FunctionDef) (fn : FunctionDef)
    (hfn : fn ∈ fns) :
    .pushLabel fn.name ∈ selectorBranches fns := by
  induction fns with
  | nil => simp at hfn
  | cons current rest ih =>
      simp only [List.mem_cons] at hfn
      rcases hfn with rfl | hfn
      · simp [selectorBranches]
      · simp only [selectorBranches, List.mem_append]
        exact Or.inr (ih hfn)

private theorem contract_mem_function_pushLabel
    (cfg : Config) (contractDef : ContractDef) (fn : FunctionDef)
    (contractInstrs : List Instr)
    (hfn : fn ∈ dispatchedFunctions contractDef)
    (hcontract : Contract.contract cfg contractDef = .ok contractInstrs) :
    .pushLabel fn.name ∈ contractInstrs := by
  rcases contract_exact_output cfg contractDef contractInstrs hcontract with
    ⟨dispatch, dispatchCtx, bodies, bodiesCtx, _, hdispatch, _, hcontractInstrs⟩
  have hshape := selectorDispatch_shape cfg (dispatchedFunctions contractDef) {}
  rw [hdispatch] at hshape
  change dispatch = _ at hshape
  have hbranch := selectorBranches_mem_pushLabel _ fn hfn
  rw [hcontractInstrs]
  apply List.mem_append_left bodies
  rw [hshape]
  simp only [List.mem_append]
  aesop

private theorem resolvable_of_encode_ok
    (instrs : List Instr) (code : ByteArray) (hencode : encode instrs = .ok code) :
    ResolvableInstrs (fixpointLabels instrs) instrs := by
  simp only [encode] at hencode
  cases hdup : checkDuplicateLabels instrs with
  | error err => simp [hdup, Bind.bind, Except.bind] at hencode
  | ok _ =>
      exact resolvable_of_emitInstrs_ok _ _ _ (by
        simpa [hdup, Bind.bind, Except.bind] using hencode)

private theorem ResolvableInstrs.lookup_of_pushLabel_mem
    (labels : List (String × Nat)) (instrs : List Instr) (label : String)
    (hresolve : ResolvableInstrs labels instrs)
    (hmem : .pushLabel label ∈ instrs) :
    ∃ targetPc, lookupLabel labels label = .ok targetPc := by
  induction instrs with
  | nil => simp at hmem
  | cons instr rest ih =>
      simp only [List.mem_cons] at hmem
      cases instr with
      | op op =>
          rcases hresolve with ⟨_, hrest⟩
          rcases hmem with h | h
          · contradiction
          · exact ih hrest h
      | push n =>
          rcases hmem with h | h
          · contradiction
          · exact ih hresolve h
      | push32 n =>
          rcases hmem with h | h
          · contradiction
          · exact ih hresolve h
      | pushLabel current =>
          rcases hresolve with ⟨⟨pc, hpc⟩, hrest⟩
          rcases hmem with h | h
          · injection h with hlabel
            subst current
            exact ⟨pc, hpc⟩
          · exact ih hrest h
      | jump current =>
          rcases hresolve with ⟨_, hrest⟩
          rcases hmem with h | h
          · contradiction
          · exact ih hrest h
      | jumpi current =>
          rcases hresolve with ⟨_, hrest⟩
          rcases hmem with h | h
          · contradiction
          · exact ih hrest h
      | jumpDest current =>
          rcases hmem with h | h
          · contradiction
          · exact ih hresolve h

/-- Full production extraction for a selected view function.

The exported `targetPc` is simultaneously the value encoded into selector jumps and the physical
byte position of the extracted `JUMPDEST` in the resolved stream. -/
theorem contract_extract_view_body_resolved
    (cfg : Config) (contractDef : ContractDef) (fn : FunctionDef)
    (contractInstrs : List Instr) (code : ByteArray)
    (hfn : fn ∈ dispatchedFunctions contractDef)
    (hview : fn.kind = .view)
    (hcontract : Contract.contract cfg contractDef = .ok contractInstrs)
    (hencode : encode contractInstrs = .ok code) :
    ∃ resolved targetPc dispatch dispatchCtx bodiesCtx before after
        body inputCtx bodyOut loweredBody program
        resolvedBefore resolvedBody resolvedAfter,
      lookupLabel (fixpointLabels contractInstrs) fn.name = .ok targetPc ∧
      targetPc = (resolvedBefore.map (instrByteSize [])).sum ∧
      selectorDispatch cfg (dispatchedFunctions contractDef) {} =
        (dispatch, dispatchCtx) ∧
      Lower.stmt cfg fn.body = .ok loweredBody ∧
      program = Lower.paramPrologue fn.params 4 loweredBody ∧
      Codegen.stmt (Ctx.forFunction inputCtx fn.name) program =
        .ok (body, bodyOut) ∧
      emitFunctionBodies cfg (dispatchedFunctions contractDef) dispatchCtx =
        .ok (before ++ [.jumpDest fn.name] ++ body ++ after, bodiesCtx) ∧
      contractInstrs =
        dispatch ++ before ++ [.jumpDest fn.name] ++ body ++ after ∧
      resolveInstrs (fixpointLabels contractInstrs) (dispatch ++ before) =
        .ok resolvedBefore ∧
      resolveInstrs (fixpointLabels contractInstrs) body = .ok resolvedBody ∧
      resolveInstrs (fixpointLabels contractInstrs) after = .ok resolvedAfter ∧
      resolved =
        resolvedBefore ++ [.op .JUMPDEST] ++ resolvedBody ++ resolvedAfter := by
  rcases contract_extract_view_body cfg contractDef fn contractInstrs hfn hview hcontract with
    ⟨dispatch, dispatchCtx, bodiesCtx, before, after, body, inputCtx, bodyOut,
      loweredBody, program, hdispatch, hlower, hprogram, hcodegen, hemit,
      hcontractInstrs⟩
  have htarget := ResolvableInstrs.lookup_of_pushLabel_mem
    (fixpointLabels contractInstrs) contractInstrs fn.name
    (resolvable_of_encode_ok contractInstrs code hencode)
    (contract_mem_function_pushLabel cfg contractDef fn contractInstrs hfn hcontract)
  rcases htarget with ⟨labelTargetPc, hlabelTarget⟩
  let labels := fixpointLabels contractInstrs
  obtain ⟨resolved, hresolve⟩ := resolveInstrs_succeeds labels contractInstrs
    (resolvable_of_encode_ok contractInstrs code hencode)
  have hresolvedNormalized :
      resolveInstrs labels
          ((dispatch ++ before) ++
            ([.jumpDest fn.name] ++ (body ++ after))) =
        .ok resolved := by
    dsimp only [labels]
    have hgroup :
        (dispatch ++ before) ++
            ([.jumpDest fn.name] ++ (body ++ after)) =
          contractInstrs := by
      rw [hcontractInstrs]
      simp only [List.append_assoc]
    rw [hgroup]
    exact hresolve
  have hsplitBefore := resolveInstrs_append labels (dispatch ++ before)
    ([.jumpDest fn.name] ++ (body ++ after))
  rw [hsplitBefore] at hresolvedNormalized
  cases hbefore : resolveInstrs labels (dispatch ++ before) with
  | error err =>
      simp [hbefore, Bind.bind, Except.bind] at hresolvedNormalized
  | ok resolvedBefore =>
      simp only [hbefore, Bind.bind, Except.bind] at hresolvedNormalized
      have hsplitEntry := resolveInstrs_append labels
        [.jumpDest fn.name] (body ++ after)
      rw [hsplitEntry] at hresolvedNormalized
      simp only [resolveInstrs, resolveInstr, Bind.bind, Except.bind] at hresolvedNormalized
      have hsplitBody := resolveInstrs_append labels body after
      rw [hsplitBody] at hresolvedNormalized
      cases hbody : resolveInstrs labels body with
      | error err =>
          simp [hbody, Bind.bind, Except.bind] at hresolvedNormalized
      | ok resolvedBody =>
          simp only [hbody, Bind.bind, Except.bind] at hresolvedNormalized
          cases hafter : resolveInstrs labels after with
          | error err =>
              simp [hafter] at hresolvedNormalized
          | ok resolvedAfter =>
              simp only [hafter] at hresolvedNormalized
              injection hresolvedNormalized with hresolvedEq
              have hcheck : checkDuplicateLabels contractInstrs = .ok () := by
                simp only [encode] at hencode
                cases hc : checkDuplicateLabels contractInstrs with
                | error err => simp [hc, Bind.bind, Except.bind] at hencode
                | ok result =>
                    have : result = () := Subsingleton.elim _ _
                    subst result
                    rfl
              have hcontractGrouped :
                  contractInstrs =
                    (dispatch ++ before) ++
                      .jumpDest fn.name :: (body ++ after) := by
                simpa only [List.append_assoc] using hcontractInstrs
              have hcheckGrouped :
                  checkDuplicateLabels
                    ((dispatch ++ before) ++
                      .jumpDest fn.name :: (body ++ after)) =
                    .ok () := by
                rw [← hcontractGrouped]
                exact hcheck
              have hphysical := lookupLabel_layoutLabels_exact
                (dispatch ++ before) (body ++ after) fn.name hcheckGrouped
              have htargetEq :
                  labelTargetPc =
                    ((dispatch ++ before).map
                      (instrByteSize (fixpointLabels contractInstrs))).sum := by
                have hlabelGrouped := hlabelTarget
                rw [hcontractGrouped] at hlabelGrouped
                simp only [fixpointLabels] at hlabelGrouped
                have htargetPlain :
                    labelTargetPc =
                      ((dispatch ++ before).map (instrByteSize [])).sum := by
                  rw [hlabelGrouped] at hphysical
                  injection hphysical
                simpa [instrByteSize] using htargetPlain
              have hsize := resolveInstrs_preserves_byteSize
                labels (dispatch ++ before) resolvedBefore hbefore
              refine ⟨resolved, labelTargetPc,
                dispatch, dispatchCtx, bodiesCtx, before, after, body, inputCtx,
                bodyOut, loweredBody, program, resolvedBefore, resolvedBody, resolvedAfter,
                hlabelTarget, ?_, hdispatch, hlower, hprogram, hcodegen, hemit,
                hcontractInstrs, ?_, ?_, ?_,
                (by simpa [List.append_assoc] using hresolvedEq.symm)⟩
              · rw [htargetEq]
                simpa only [labels] using hsize.symm
              · simpa only [labels] using hbefore
              · simpa only [labels] using hbody
              · simpa only [labels] using hafter

/-- Decoder certificate for the exact bytes emitted by the production symbolic-label encoder.
The resolved stream is only a proof view: `encode_resolves_byte_identically` proves that no
alternative encoder is involved. -/
theorem productionDecoderAlong
    (instrs resolved : List Instr) (code : ByteArray)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64) :
    DecoderAlong code 0 resolved := by
  have hplain : PlainInstrs resolved := fun instr hmem => (hencodable instr hmem).1
  have hemit : emitInstrs [] resolved = .ok code :=
    encode_resolves_byte_identically instrs resolved code hencode hresolve
  have hencodeResolved : encode resolved = .ok code := by
    rw [encode_plain resolved hplain]
    exact hemit
  exact decoderAlong_encode resolved hencodable code hencodeResolved hlimit

def dispatchRevertBytes (cfg : Config) : ByteArray :=
  match cfg.errors.errorSelector "InvalidSelector" with
  | some selector =>
      ((.ofNat (paddedSelector selector) : Word)).toByteArray.extract 0 4
  | none => ByteArray.empty

def SelectorMismatch (fns : List FunctionDef) (calldata : ByteArray) : Prop :=
  ∀ fn ∈ fns, decodeSelector calldata ≠ .ofNat (computeSelector fn).toNat

/-- States on the single non-halting EvmYul execution path from `initial`.  Every edge uses the
production decoder, EvmYul's checked-state/cost calculation, and the real `EVM.step`. -/
inductive EVMPathReach (initial : EVM.State) : EVM.State → Prop
  | initial : EVMPathReach initial initial
  | step {st next : EVM.State} {decoded : Decoded}
      (hreach : EVMPathReach initial st)
      (hdecode : EVM.decode st.executionEnv.code st.pc = some decoded)
      (hstep : EVM.step 1 (checkedCost st decoded.1) (some decoded)
        (checkedState st decoded.1) = .ok next)
      (hhalt : xHaltOutput next.toMachineState decoded.1 = none) :
      EVMPathReach initial next

def decodedByteSize : Decoded → Nat
  | (.Push _, some (_, width)) => width + 1
  | _ => 1

/-- One gas/environment hypothesis for an actual path.  Only opcode/state pairs decoded at states
reachable from `initial` must pass EvmYul's exceptional-halt precheck.  The second conjunct records
the standard code/PC frame of a successful checked step, so body alignment is available without
asking callers for individual intermediate-state equations. -/
def PathScopedXPrecheckSafe (validJumps : Array Word) (initial : EVM.State) : Prop :=
  ∀ (st : EVM.State) (decoded : Decoded),
    EVMPathReach initial st →
    EVM.decode st.executionEnv.code st.pc = some decoded →
    XPrecheckSafe validJumps decoded.1 st ∧
      ∀ next,
        EVM.step 1 (checkedCost st decoded.1) (some decoded)
          (checkedState st decoded.1) = .ok next →
        next.executionEnv.code = st.executionEnv.code ∧
          next.pc = st.pc + .ofNat (decodedByteSize decoded)

theorem decodedByteSize_plain (instr : Instr) (hpure : PureViewInstr instr) :
    decodedByteSize (decodedPlainInstr instr) = instrByteSize [] instr := by
  cases instr with
  | push n =>
      simp only [PureViewInstr] at hpure
      by_cases hn : n = 0
      · subst n
        rfl
      · generalize heq : pushWidth n = width
        have hlo : 0 < width := by simp [pushWidth, hn] at heq; omega
        have hhi : width ≤ 32 := by omega
        interval_cases width <;>
          simp_all [decodedByteSize, decodedPlainInstr, instrByteSize, pushOp]
  | op op => simp [decodedByteSize, decodedPlainInstr, instrByteSize]
  | push32 _ | pushLabel _ | jump _ | jumpi _ | jumpDest _ => contradiction

/-- Path-scoped safety constructs the body readiness certificate internally from the generated
non-return prefix and the actual `runView` execution. -/
theorem XReady_of_pathSafe_runView
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (pc : Nat) (pre : List Instr)
    (st final : EVM.State)
    (hreach : EVMPathReach initial st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hdecode : DecoderAlong code pc (pre ++ [.op .RETURN]))
    (hpure : Lsc.Compile.Bytecode.PureViewInstrs pre)
    (hrun : runView (pre ++ [.op .RETURN]) st = .ok final) :
    XReady validJumps code pc (pre ++ [.op .RETURN]) st := by
  induction pre generalizing pc st final with
  | nil =>
      simp only [List.nil_append, XReady]
      cases hdecode with
      | cons _ _ _ hdecoded _ =>
          refine ⟨hcode, hpc, ?_⟩
          exact (hsafe st (.RETURN, none) hreach
            (by simpa [hcode, hpc] using hdecoded)).1
  | cons instr rest ih =>
      simp only [List.cons_append] at hdecode hrun ⊢
      cases hdecode with
      | cons _ _ _ hdecoded hdecodeRest =>
          simp only [runView] at hrun
          cases hs : EVM.step 1 (checkedCost st (decodedPlainInstr instr).1)
              (some (decodedPlainInstr instr))
              (checkedState st (decodedPlainInstr instr).1) with
          | error err =>
              rw [hs] at hrun
              contradiction
          | ok next =>
              rw [hs] at hrun
              have hiPure : PureViewInstr instr :=
                hpure instr (by simp)
              have hiNotReturn : instr ≠ .op .RETURN := by
                intro heq
                subst instr
                simp [PureViewInstr] at hiPure
              have hdecodeAt :
                  EVM.decode st.executionEnv.code st.pc =
                    some (decodedPlainInstr instr) := by
                simpa [hcode, hpc] using hdecoded
              have hsafeAt :=
                hsafe st (decodedPlainInstr instr) hreach hdecodeAt
              have hhalt :
                  xHaltOutput next.toMachineState (decodedPlainInstr instr).1 = none :=
                pureView_xHaltOutput_none instr hiPure next.toMachineState
              have hnextReach : EVMPathReach initial next :=
                .step hreach hdecodeAt hs hhalt
              have hframe := hsafeAt.2 next hs
              have hnextPc :
                  next.pc = .ofNat (pc + instrByteSize [] instr) := by
                rw [hframe.2, hpc, decodedByteSize_plain instr hiPure, word_ofNat_add]
              cases htail : rest ++ [.op .RETURN] with
              | nil => simp at htail
              | cons nextInstr tail =>
                  simp only [XReady]
                  refine ⟨hiPure, hiNotReturn, hcode, hpc, hsafeAt.1, ?_⟩
                  rw [hs]
                  refine ⟨hhalt, ?_⟩
                  rw [← htail]
                  exact ih (pc + instrByteSize [] instr) next final
                    hnextReach (by rw [hframe.1, hcode]) hnextPc hdecodeRest
                    (fun candidate hmem => hpure candidate (by simp [hmem]))
                    hrun

/-- Direct path-scoped execution of a non-halting generated prefix ending in `REVERT`. -/
theorem X_revert_of_pathSafe_runView
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (pc : Nat) (pre : List Instr)
    (st final : EVM.State) (output : ByteArray)
    (hreach : EVMPathReach initial st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hdecode : DecoderAlong code pc (pre ++ [.op .REVERT]))
    (hpure : PureViewInstrs pre)
    (hrun : runView (pre ++ [.op .REVERT]) st = .ok final)
    (houtput : final.H_return = output) :
    EVM.X (pre.length + 2) validJumps st =
      .ok (.revert final.gasAvailable output) := by
  induction pre generalizing pc st final with
  | nil =>
      simp only [List.nil_append, List.length_nil, zero_add]
      cases hdecode with
      | cons _ _ _ hdecoded _ =>
          change runView [.op .REVERT] st = .ok final at hrun
          simp only [runView, decodedPlainInstr] at hrun
          cases hs : EVM.step 1 (checkedCost st .REVERT) (some (.REVERT, none))
              (checkedState st .REVERT) with
          | error err =>
              rw [hs] at hrun
              contradiction
          | ok next =>
              rw [hs] at hrun
              injection hrun with heq
              subst next
              rw [← houtput]
              apply X_revert_of_precheck 1 validJumps st
                (checkedState st .REVERT) final (checkedCost st .REVERT)
              · simpa [hcode, hpc] using hdecoded
              · simpa [checkedState, checkedCost] using
                  xPrecheck_ok_of_safe validJumps .REVERT st
                    (hsafe st (.REVERT, none) hreach
                      (by simpa [hcode, hpc] using hdecoded)).1
              · exact hs
  | cons instr rest ih =>
      simp only [List.cons_append, List.length_cons]
      cases hdecode with
      | cons _ _ _ hdecoded hdecodeRest =>
          change runView (instr :: (rest ++ [.op .REVERT])) st = .ok final at hrun
          simp only [runView] at hrun
          cases hs : EVM.step 1 (checkedCost st (decodedPlainInstr instr).1)
              (some (decodedPlainInstr instr))
              (checkedState st (decodedPlainInstr instr).1) with
          | error err =>
              rw [hs] at hrun
              contradiction
          | ok next =>
              rw [hs] at hrun
              have hiPure : PureViewInstr instr := hpure instr (by simp)
              have hdecodeAt :
                  EVM.decode st.executionEnv.code st.pc =
                    some (decodedPlainInstr instr) := by
                simpa [hcode, hpc] using hdecoded
              have hsafeAt :=
                hsafe st (decodedPlainInstr instr) hreach hdecodeAt
              have hhalt :=
                pureView_xHaltOutput_none instr hiPure next.toMachineState
              have hnextReach : EVMPathReach initial next :=
                .step hreach hdecodeAt hs hhalt
              have hframe := hsafeAt.2 next hs
              have hnextPc :
                  next.pc = .ofNat (pc + instrByteSize [] instr) := by
                rw [hframe.2, hpc, decodedByteSize_plain instr hiPure, word_ofNat_add]
              calc
                EVM.X (rest.length + 1 + 2) validJumps st =
                    EVM.X (rest.length + 2) validJumps next := by
                      apply X_step_of_precheck (rest.length + 2) validJumps st
                        (checkedState st (decodedPlainInstr instr).1) next
                        (decodedPlainInstr instr)
                        (checkedCost st (decodedPlainInstr instr).1) hdecodeAt
                      · simpa [checkedState, checkedCost] using
                          xPrecheck_ok_of_safe validJumps
                            (decodedPlainInstr instr).1 st (hsafeAt.1)
                      · convert
                          (pureViewStep_fuel instr hiPure (rest.length + 1)
                            (checkedCost st (decodedPlainInstr instr).1)
                            (checkedState st (decodedPlainInstr instr).1)).trans hs
                          using 1 <;> omega
                      · exact hhalt
                _ = .ok (.revert final.gasAvailable output) :=
                  ih (pc + instrByteSize [] instr) next final
                    hnextReach (by rw [hframe.1, hcode]) hnextPc hdecodeRest
                    (fun candidate hmem => hpure candidate (by simp [hmem]))
                    hrun houtput

/-! ### Direct execution of the recursive selector branches -/

def resolvedCalldataGuard (revertPc : Nat) : List Instr :=
  [.push 4, .op .CALLDATASIZE, .op .LT, .push32 revertPc, .op .JUMPI]

/-- The resolved form of one generated selector branch.  Symbolic labels are always resolved by
the production encoder to `PUSH32`, independently of the numerical target. -/
def resolvedSelectorBranch (selector targetPc : Nat) : List Instr :=
  loadSelector ++
    [.push selector, .op .EQ, .push32 targetPc, .op .JUMPI]

def resolvedSelectorBranches : List (Nat × Nat) → List Instr
  | [] => []
  | (selector, targetPc) :: rest =>
      resolvedSelectorBranch selector targetPc ++ resolvedSelectorBranches rest

/-- Resolving production selector branches produces the aligned selector/target pairs. -/
theorem resolveSelectorBranches_exists
    (labels : List (String × Nat)) (fns : List FunctionDef) (resolved : List Instr)
    (hresolve : resolveInstrs labels (selectorBranches fns) = .ok resolved) :
    resolved = resolvedSelectorBranches (resolvedSelectorPairs labels fns) := by
  induction fns generalizing resolved with
  | nil =>
      simp [selectorBranches, resolveInstrs] at hresolve
      subst resolved
      rfl
  | cons fn rest ih =>
      cases htarget : lookupLabel labels fn.name with
      | error err =>
          simp [selectorBranches, loadSelector, resolveInstrs, resolveInstr, htarget,
            Bind.bind, Except.bind] at hresolve
      | ok targetPc =>
          cases hrest : resolveInstrs labels (selectorBranches rest) with
          | error err =>
              simp [selectorBranches, loadSelector, resolveInstrs, resolveInstr, htarget,
                hrest, Bind.bind, Except.bind] at hresolve
          | ok resolvedRest =>
              simp [selectorBranches, loadSelector, resolveInstrs, resolveInstr, htarget,
                hrest, Bind.bind, Except.bind] at hresolve
              subst resolved
              rw [ih resolvedRest hrest]
              simp only [resolvedSelectorPairs, List.map_cons, resolvedSelectorTarget,
                htarget, resolvedSelectorBranches, resolvedSelectorBranch, loadSelector,
                List.cons_append, List.nil_append]

theorem resolvedSelectorBranches_append (first rest : List (Nat × Nat)) :
    resolvedSelectorBranches (first ++ rest) =
      resolvedSelectorBranches first ++ resolvedSelectorBranches rest := by
  induction first with
  | nil => rfl
  | cons pair first ih =>
      rcases pair with ⟨selector, targetPc⟩
      simp [resolvedSelectorBranches, ih, List.append_assoc]

/-- Exact resolved shape of the production ABI dispatcher. -/
theorem resolveSelectorDispatch_shape
    (cfg : Config) (fns : List FunctionDef) (ctx : Ctx)
    (dispatch : List Instr) (dispatchCtx : Ctx)
    (labels : List (String × Nat)) (resolved : List Instr)
    (hdispatch : selectorDispatch cfg fns ctx = (dispatch, dispatchCtx))
    (hresolve : resolveInstrs labels dispatch = .ok resolved) :
    ∃ revertPc,
      lookupLabel labels (selectorRevertLabel ctx) = .ok revertPc ∧
      resolved =
        resolvedCalldataGuard revertPc ++
          resolvedSelectorBranches (resolvedSelectorPairs labels fns) ++
          [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg := by
  have hshape := selectorDispatch_shape cfg fns ctx
  rw [hdispatch] at hshape
  change dispatch = _ at hshape
  subst dispatch
  cases hrevert : lookupLabel labels (selectorRevertLabel ctx) with
  | error err =>
      simp [resolveInstrs, resolveInstr, hrevert, Bind.bind, Except.bind] at hresolve
  | ok revertPc =>
      cases hbranches :
          resolveInstrs labels (selectorBranches fns) with
      | error err =>
          simp [resolveInstrs_append, resolveInstrs, resolveInstr, hrevert, hbranches,
            Bind.bind, Except.bind] at hresolve
      | ok resolvedBranches =>
          have hbranchesShape :=
            resolveSelectorBranches_exists labels fns resolvedBranches hbranches
          have hdispatchRevert :
              resolveInstrs labels (dispatchRevert cfg) = .ok (dispatchRevert cfg) := by
            unfold dispatchRevert
            split <;> rfl
          have hguard :
              resolveInstrs labels
                  [.push 4, .op .CALLDATASIZE, .op .LT,
                    .pushLabel (selectorRevertLabel ctx), .op .JUMPI] =
                .ok (resolvedCalldataGuard revertPc) := by
            simp [resolveInstrs, resolveInstr, hrevert, resolvedCalldataGuard,
              Bind.bind, Except.bind]
          have htail :
              resolveInstrs labels
                  [.pushLabel (selectorRevertLabel ctx), .op .JUMP,
                    .jumpDest (selectorRevertLabel ctx)] =
                .ok [.push32 revertPc, .op .JUMP, .op .JUMPDEST] := by
            simp [resolveInstrs, resolveInstr, hrevert, Bind.bind, Except.bind]
          rw [resolveInstrs_append] at hresolve
          rw [hdispatchRevert] at hresolve
          simp only [Bind.bind, Except.bind] at hresolve
          rw [resolveInstrs_append, resolveInstrs_append, hguard, hbranches, htail] at hresolve
          simp only [Bind.bind, Except.bind] at hresolve
          injection hresolve with hresolved
          refine ⟨revertPc, rfl, ?_⟩
          rw [hbranchesShape] at hresolved
          exact hresolved.symm

private theorem word_eq_of_toNat_eq (a b : Word) (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UInt256.toNat] at h
      simp only [UInt256.mk.injEq]
      exact Fin.eq_of_val_eq h

private theorem wordOfNat_add (a b : Nat) :
    (UInt256.ofNat a + UInt256.ofNat b : Word) = UInt256.ofNat (a + b) := by
  apply word_eq_of_toNat_eq
  change (a % UInt256.size + b % UInt256.size) % UInt256.size =
    (a + b) % UInt256.size
  exact (Nat.add_mod a b UInt256.size).symm

private def selectorPushState (n : Nat) (st : EVM.State) : EVM.State :=
  let checked := checkedState st (decodedPlainInstr (.push n)).1
  {
    checked with
    stack := .ofNat n :: st.stack
    pc := checked.pc + .ofNat (pushWidth n + 1)
    gasAvailable := checked.gasAvailable -
      .ofNat (checkedCost st (decodedPlainInstr (.push n)).1)
    execLength := checked.execLength + 1 }

private def selectorPush32State (n : Nat) (st : EVM.State) : EVM.State :=
  let checked := checkedState st .PUSH32
  {
    checked with
    stack := .ofNat n :: st.stack
    pc := checked.pc + .ofNat 33
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .PUSH32)
    execLength := checked.execLength + 1 }

private def selectorCalldataloadState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .CALLDATALOAD
  {
    checked with
    stack := EvmYul.State.calldataload checked.toState st.stack.head! :: st.stack.tail
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .CALLDATALOAD)
    execLength := checked.execLength + 1 }

private def selectorShrState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .SHR
  {
    checked with
    stack := UInt256.shiftRight st.stack.tail.head! st.stack.head! :: st.stack.tail.tail
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .SHR)
    execLength := checked.execLength + 1 }

private def selectorEqState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .EQ
  {
    checked with
    stack := UInt256.eq st.stack.head! st.stack.tail.head! :: st.stack.tail.tail
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .EQ)
    execLength := checked.execLength + 1 }

private def selectorJumpiState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .JUMPI
  {
    checked with
    stack := st.stack.tail.tail
    pc := if st.stack.tail.head! != ⟨0⟩ then st.stack.head!
      else checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .JUMPI)
    execLength := checked.execLength + 1 }

private def calldataSizeState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .CALLDATASIZE
  {
    checked with
    stack := .ofNat st.executionEnv.calldata.size :: st.stack
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .CALLDATASIZE)
    execLength := checked.execLength + 1 }

private def calldataLtState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .LT
  {
    checked with
    stack := UInt256.lt st.stack.head! st.stack.tail.head! :: st.stack.tail.tail
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .LT)
    execLength := checked.execLength + 1 }

def calldataGuardState (revertPc : Nat) (st : EVM.State) : EVM.State :=
  selectorJumpiState
    (selectorPush32State revertPc
      (calldataLtState (calldataSizeState (selectorPushState 4 st))))

/-- State after executing `loadSelector`, expressed only with EvmYul's EVM state and operations. -/
def loadSelectorState (st : EVM.State) : EVM.State :=
  selectorShrState
    (selectorPushState 0xE0 (selectorCalldataloadState (selectorPushState 0 st)))

/-- State after one resolved selector branch, including its reload. -/
def selectorBranchState (selector targetPc : Nat) (st : EVM.State) : EVM.State :=
  selectorJumpiState
    (selectorPush32State targetPc
      (selectorEqState (selectorPushState selector (loadSelectorState st))))

private theorem selectorPushState_step (n fuel : Nat) (hwidth : pushWidth n ≤ 32)
    (st : EVM.State) :
    EVM.step (fuel + 1) (checkedCost st (decodedPlainInstr (.push n)).1)
        (some (decodedPlainInstr (.push n)))
        (checkedState st (decodedPlainInstr (.push n)).1) =
      .ok (selectorPushState n st) := by
  simpa [selectorPushState, checkedState] using
    evmStep_decodedPush n fuel
      (checkedCost st (decodedPlainInstr (.push n)).1) hwidth
      (checkedState st (decodedPlainInstr (.push n)).1)

private theorem selectorPush32State_step (n fuel : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) (checkedCost st .PUSH32)
        (some (decodedPlainInstr (.push32 n))) (checkedState st .PUSH32) =
      .ok (selectorPush32State n st) := by
  rfl

private theorem selectorCalldataloadState_step (fuel : Nat) (st : EVM.State)
    (offset : Word) (tail : List Word) (hstack : st.stack = offset :: tail) :
    EVM.step (fuel + 1) (checkedCost st .CALLDATALOAD)
        (some (.CALLDATALOAD, none)) (checkedState st .CALLDATALOAD) =
      .ok (selectorCalldataloadState st) := by
  cases st
  simp only at hstack
  subst hstack
  rfl

private theorem selectorShrState_step (fuel : Nat) (st : EVM.State)
    (amount value : Word) (tail : List Word)
    (hstack : st.stack = amount :: value :: tail) :
    EVM.step (fuel + 1) (checkedCost st .SHR)
        (some (.SHR, none)) (checkedState st .SHR) =
      .ok (selectorShrState st) := by
  cases st
  simp only at hstack
  subst hstack
  rfl

private theorem selectorEqState_step (fuel : Nat) (st : EVM.State)
    (lhs rhs : Word) (tail : List Word) (hstack : st.stack = lhs :: rhs :: tail) :
    EVM.step (fuel + 1) (checkedCost st .EQ)
        (some (.EQ, none)) (checkedState st .EQ) =
      .ok (selectorEqState st) := by
  cases st
  simp only at hstack
  subst hstack
  rfl

private theorem selectorJumpiState_step (fuel : Nat) (st : EVM.State)
    (dest cond : Word) (tail : List Word) (hstack : st.stack = dest :: cond :: tail) :
    EVM.step (fuel + 1) (checkedCost st .JUMPI)
        (some (.JUMPI, none)) (checkedState st .JUMPI) =
      .ok (selectorJumpiState st) := by
  cases st
  simp only at hstack
  subst hstack
  rfl

private theorem calldataSizeState_step (fuel : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) (checkedCost st .CALLDATASIZE)
        (some (.CALLDATASIZE, none)) (checkedState st .CALLDATASIZE) =
      .ok (calldataSizeState st) := by
  rfl

private theorem calldataLtState_step (fuel : Nat) (st : EVM.State)
    (lhs rhs : Word) (tail : List Word) (hstack : st.stack = lhs :: rhs :: tail) :
    EVM.step (fuel + 1) (checkedCost st .LT)
        (some (.LT, none)) (checkedState st .LT) =
      .ok (calldataLtState st) := by
  cases st
  simp only at hstack
  subst hstack
  rfl

private theorem xHaltOutput_decodedPush_none (n : Nat) (hwidth : pushWidth n ≤ 32)
    (st : EVM.State) :
    xHaltOutput st.toMachineState (decodedPlainInstr (.push n)).1 = none := by
  generalize heq : pushWidth n = width
  have hw : width ≤ 32 := by omega
  interval_cases width <;> simp [xHaltOutput, decodedPlainInstr, heq, pushOp]

private theorem xHaltOutput_push32_none (st : EVM.State) :
    xHaltOutput st.toMachineState
      (decodedPlainInstr (.push32 0)).1 = none := by
  rfl

theorem loadSelectorState_stack (st : EVM.State) (hstack : st.stack = []) :
    (loadSelectorState st).stack =
      decodeSelector st.executionEnv.calldata :: [] := by
  have hzero : (UInt256.ofNat 0).toNat = 0 := rfl
  simp [loadSelectorState, selectorShrState, selectorPushState,
    selectorCalldataloadState, checkedState, hstack, decodeSelector,
    EvmYul.State.calldataload, hzero]

theorem selectorBranchState_stack (selector targetPc : Nat) (st : EVM.State)
    (hstack : st.stack = []) :
    (selectorBranchState selector targetPc st).stack = [] := by
  simp [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, loadSelectorState_stack st hstack,
    checkedState, hstack]

theorem selectorBranchState_executionEnv (selector targetPc : Nat) (st : EVM.State) :
    (selectorBranchState selector targetPc st).executionEnv = st.executionEnv := by
  simp [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, loadSelectorState, selectorShrState,
    selectorCalldataloadState, checkedState]

theorem selectorBranchState_memory (selector targetPc : Nat) (st : EVM.State) :
    (selectorBranchState selector targetPc st).memory = st.memory := by
  simp [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, loadSelectorState, selectorShrState,
    selectorCalldataloadState, checkedState]

theorem selectorBranchState_toState (selector targetPc : Nat) (st : EVM.State) :
    (selectorBranchState selector targetPc st).toState = st.toState := by
  simp [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, loadSelectorState, selectorShrState,
    selectorCalldataloadState, checkedState]

theorem calldataGuardState_stack (revertPc : Nat) (st : EVM.State)
    (hstack : st.stack = []) :
    (calldataGuardState revertPc st).stack = [] := by
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState, hstack]

theorem calldataGuardState_executionEnv (revertPc : Nat) (st : EVM.State) :
    (calldataGuardState revertPc st).executionEnv = st.executionEnv := by
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState]

theorem calldataGuardState_memory (revertPc : Nat) (st : EVM.State) :
    (calldataGuardState revertPc st).memory = st.memory := by
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState]

theorem calldataGuardState_toState (revertPc : Nat) (st : EVM.State) :
    (calldataGuardState revertPc st).toState = st.toState := by
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState]

theorem calldataGuardState_pc_wellFormed
    {selector : Nat} {args : List Word} {calldata : ByteArray}
    (revertPc : Nat) (st : EVM.State) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hcalldata : st.executionEnv.calldata = calldata)
    (hwf : WellFormed selector args calldata) :
    (calldataGuardState revertPc st).pc =
      .ofNat (instrsByteSize (resolvedCalldataGuard revertPc)) := by
  have hnotShort : ¬ st.executionEnv.calldata.size < 4 := by
    rw [hcalldata]
    exact hwf.not_short
  have hsizeLt : st.executionEnv.calldata.size < UInt256.size := by
    rw [hcalldata, hwf.size]
    change 4 + 32 * args.length < 2 ^ 256
    exact hwf.offsets_lt
  have hwordNotShort :
      ¬ (UInt256.ofNat st.executionEnv.calldata.size : Word) < .ofNat 4 := by
    intro h
    change st.executionEnv.calldata.size % UInt256.size <
      4 % UInt256.size at h
    rw [Nat.mod_eq_of_lt hsizeLt, Nat.mod_eq_of_lt (by decide)] at h
    exact hnotShort h
  have hcond :
      UInt256.lt (.ofNat st.executionEnv.calldata.size) (.ofNat 4) = .ofNat 0 := by
    simp [UInt256.lt, hwordNotShort]
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState, hstack,
    hpc, hcond, resolvedCalldataGuard, instrsByteSize, instrByteSize, pushWidth,
    wordOfNat_add]
  congr 1

theorem calldataGuardState_pc_fallthrough
    (revertPc : Nat) (st : EVM.State) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = [])
    (hnotShort : ¬ st.executionEnv.calldata.size < 4)
    (hsizeLt : st.executionEnv.calldata.size < UInt256.size) :
    (calldataGuardState revertPc st).pc =
      .ofNat (instrsByteSize (resolvedCalldataGuard revertPc)) := by
  have hwordNotShort :
      ¬ (UInt256.ofNat st.executionEnv.calldata.size : Word) < .ofNat 4 := by
    intro h
    change st.executionEnv.calldata.size % UInt256.size <
      4 % UInt256.size at h
    rw [Nat.mod_eq_of_lt hsizeLt, Nat.mod_eq_of_lt (by decide)] at h
    exact hnotShort h
  have hcond :
      UInt256.lt (.ofNat st.executionEnv.calldata.size) (.ofNat 4) = .ofNat 0 := by
    simp [UInt256.lt, hwordNotShort]
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState, hstack,
    hpc, hcond, resolvedCalldataGuard, instrsByteSize, instrByteSize, pushWidth,
    wordOfNat_add]
  congr 1

theorem selectorBranchState_pc_match (selector targetPc : Nat) (st : EVM.State)
    (hstack : st.stack = [])
    (hselector : decodeSelector st.executionEnv.calldata = .ofNat selector) :
    (selectorBranchState selector targetPc st).pc = .ofNat targetPc := by
  have hone : ((UInt256.ofNat 1 != (⟨0⟩ : Word)) = true) := by decide
  simp [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, loadSelectorState_stack st hstack,
    checkedState, hselector, UInt256.eq, hone]

theorem selectorBranchState_pc_mismatch (pc selector targetPc selected : Nat)
    (st : EVM.State) (hpc : st.pc = .ofNat pc) (hstack : st.stack = [])
    (hselector : decodeSelector st.executionEnv.calldata = .ofNat selected)
    (hne : (.ofNat selector : Word) ≠ .ofNat selected) :
    (selectorBranchState selector targetPc st).pc =
      .ofNat (pc + instrsByteSize (resolvedSelectorBranch selector targetPc)) := by
  have hload := loadSelectorState_stack st hstack
  simp only [selectorBranchState, selectorJumpiState, selectorPush32State,
    selectorEqState, selectorPushState, checkedState]
  simp [hload, hselector, UInt256.eq, hne]
  have hzeroBool : ((UInt256.ofNat 0 != (⟨0⟩ : Word)) = false) := by decide
  simp [loadSelectorState, selectorShrState, selectorCalldataloadState,
    selectorPushState, checkedState,
    resolvedSelectorBranch, loadSelector, instrsByteSize, instrByteSize,
    hpc, pushWidth, hzeroBool, wordOfNat_add]
  congr 1
  omega

theorem calldataGuardState_pc_short
    (revertPc : Nat) (st : EVM.State) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hshort : st.executionEnv.calldata.size < 4) :
    (calldataGuardState revertPc st).pc = .ofNat revertPc := by
  have hsizeLt : st.executionEnv.calldata.size < UInt256.size := by
    exact lt_trans hshort (by norm_num [UInt256.size])
  have hfour : 4 < UInt256.size := by norm_num [UInt256.size]
  have hfin :
      (UInt256.ofNat st.executionEnv.calldata.size).val <
        (UInt256.ofNat 4).val := by
    change st.executionEnv.calldata.size % UInt256.size < 4 % UInt256.size
    rw [Nat.mod_eq_of_lt hsizeLt, Nat.mod_eq_of_lt hfour]
    exact hshort
  have hcomp :
      UInt256.ofNat st.executionEnv.calldata.size < UInt256.ofNat 4 := hfin
  have hlt :
      UInt256.lt (.ofNat st.executionEnv.calldata.size) (.ofNat 4) =
        (.ofNat 1 : Word) := by
    simp [UInt256.lt, hcomp]
  have hone : (((.ofNat 1 : Word) != (⟨0⟩ : Word)) = true) := by decide
  simp [calldataGuardState, selectorJumpiState, selectorPush32State,
    calldataLtState, calldataSizeState, selectorPushState, checkedState,
    hpc, hstack, hlt, hone]

theorem X_step_of_pathPrecheck
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (fuel : Nat) (st next : EVM.State) (decoded : Decoded)
    (hreach : EVMPathReach initial st)
    (hdecode : EVM.decode st.executionEnv.code st.pc = some decoded)
    (hstep : EVM.step fuel (checkedCost st decoded.1) (some decoded)
      (checkedState st decoded.1) = .ok next)
    (hhalt : xHaltOutput next.toMachineState decoded.1 = none) :
    EVM.X (fuel + 1) validJumps st = EVM.X fuel validJumps next := by
  apply X_step_of_precheck fuel validJumps st (checkedState st decoded.1) next
    decoded (checkedCost st decoded.1) hdecode
  · exact xPrecheck_ok_of_safe validJumps decoded.1 st
      (hsafe st decoded hreach hdecode).1
  · exact hstep
  · exact hhalt

/-- The production calldata-size guard executes directly; its `JUMPI` successor is determined by
the actual calldata size in `calldataGuardState`. -/
theorem resolvedCalldataGuard_X
    (validJumps : Array Word) (code : ByteArray) (revertPc suffixFuel : Nat)
    (rest : List Instr) (st : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hdecoder : DecoderAlong code 0 (resolvedCalldataGuard revertPc ++ rest))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hsuffix : 0 < suffixFuel) :
    EVM.X (suffixFuel + 5) validJumps st =
        EVM.X suffixFuel validJumps (calldataGuardState revertPc st) ∧
      EVMPathReach st (calldataGuardState revertPc st) := by
  let s₁ := selectorPushState 4 st
  let s₂ := calldataSizeState s₁
  let s₃ := calldataLtState s₂
  let s₄ := selectorPush32State revertPc s₃
  let s₅ := selectorJumpiState s₄
  change DecoderAlong code 0
    ([.push 4, .op .CALLDATASIZE, .op .LT, .push32 revertPc, .op .JUMPI] ++ rest)
      at hdecoder
  cases hdecoder with
  | cons _ _ _ hd₁ hr₁ =>
    cases hr₁ with
    | cons _ _ _ hd₂ hr₂ =>
      cases hr₂ with
      | cons _ _ _ hd₃ hr₃ =>
        cases hr₃ with
        | cons _ _ _ hd₄ hr₄ =>
          cases hr₄ with
          | cons _ _ _ hd₅ hr₅ =>
            have hs₁ : s₁.stack = [.ofNat 4] := by
              simp [s₁, selectorPushState, checkedState, hstack]
            have hs₂ :
                s₂.stack = .ofNat st.executionEnv.calldata.size :: .ofNat 4 :: [] := by
              simp [s₂, calldataSizeState, checkedState, hs₁, s₁,
                selectorPushState, hstack]
            have hs₃ :
                s₃.stack =
                  UInt256.lt (.ofNat st.executionEnv.calldata.size) (.ofNat 4) :: [] := by
              simp [s₃, calldataLtState, checkedState, hs₂]
            have hs₄ : s₄.stack = .ofNat revertPc :: s₃.stack := by
              simp [s₄, selectorPush32State, checkedState]
            have hp₁ : s₁.pc = .ofNat 2 := by
              simp [s₁, selectorPushState, checkedState, hpc, pushWidth,
                wordOfNat_add]
              congr 1
            have hp₂ : s₂.pc = .ofNat 3 := by
              simp [s₂, calldataSizeState, checkedState, hp₁, wordOfNat_add]
            have hp₃ : s₃.pc = .ofNat 4 := by
              simp [s₃, calldataLtState, checkedState, hp₂, wordOfNat_add]
            have hp₄ : s₄.pc = .ofNat 37 := by
              simp [s₄, selectorPush32State, checkedState, hp₃, wordOfNat_add]
            have henv₁ : s₁.executionEnv.code = code := by
              simp [s₁, selectorPushState, checkedState, hcode]
            have henv₂ : s₂.executionEnv.code = code := by
              simp [s₂, calldataSizeState, checkedState, henv₁]
            have henv₃ : s₃.executionEnv.code = code := by
              simp [s₃, calldataLtState, checkedState, henv₂]
            have henv₄ : s₄.executionEnv.code = code := by
              simp [s₄, selectorPush32State, checkedState, henv₃]
            have hdec₁ :
                EVM.decode st.executionEnv.code st.pc =
                  some (decodedPlainInstr (.push 4)) := by
              simpa [hcode, hpc] using hd₁
            have hdec₂ :
                EVM.decode s₁.executionEnv.code s₁.pc = some (.CALLDATASIZE, none) := by
              rw [henv₁, hp₁]
              simpa [instrByteSize, pushWidth] using hd₂
            have hdec₃ :
                EVM.decode s₂.executionEnv.code s₂.pc = some (.LT, none) := by
              rw [henv₂, hp₂]
              simpa [instrByteSize, pushWidth] using hd₃
            have hdec₄ :
                EVM.decode s₃.executionEnv.code s₃.pc =
                  some (decodedPlainInstr (.push32 revertPc)) := by
              rw [henv₃, hp₃]
              simpa [instrByteSize, pushWidth] using hd₄
            have hdec₅ :
                EVM.decode s₄.executionEnv.code s₄.pc = some (.JUMPI, none) := by
              rw [henv₄, hp₄]
              simpa [instrByteSize, pushWidth] using hd₅
            have hr₁ : EVMPathReach st s₁ :=
              .step .initial hdec₁
                (by simpa [s₁] using selectorPushState_step 4 0 (by decide) st)
                (xHaltOutput_decodedPush_none 4 (by decide) s₁)
            have hr₂ : EVMPathReach st s₂ :=
              .step hr₁ hdec₂
                (by simpa [s₂] using calldataSizeState_step 0 s₁)
                (by simp [xHaltOutput])
            have hr₃ : EVMPathReach st s₃ :=
              .step hr₂ hdec₃
                (by simpa [s₃] using (calldataLtState_step 0 s₂
                  (.ofNat st.executionEnv.calldata.size) (.ofNat 4) [] hs₂))
                (by simp [xHaltOutput])
            have hr₄ : EVMPathReach st s₄ :=
              .step hr₃ hdec₄
                (by simpa [s₄] using selectorPush32State_step revertPc 0 s₃)
                (by simpa using xHaltOutput_push32_none s₄)
            have hr₅ : EVMPathReach st s₅ :=
              .step hr₄ hdec₅
                (by simpa [s₅] using (selectorJumpiState_step 0 s₄
                  (.ofNat revertPc) s₃.stack.head! [] (by simpa [hs₃] using hs₄)))
                (by simp [xHaltOutput])
            obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsuffix)
            constructor
            · calc
              EVM.X (k + 1 + 5) validJumps st =
                  EVM.X (k + 5) validJumps s₁ := by
                rw [show k + 1 + 5 = (k + 5) + 1 by omega]
                apply X_step_of_pathPrecheck validJumps st hsafe
                  (k + 5) st s₁ (decodedPlainInstr (.push 4)) .initial hdec₁
                · simpa [s₁] using selectorPushState_step 4 (k + 4) (by decide) st
                · exact xHaltOutput_decodedPush_none 4 (by decide) s₁
              _ = EVM.X (k + 4) validJumps s₂ := by
                rw [show k + 5 = (k + 4) + 1 by omega]
                apply X_step_of_pathPrecheck validJumps st hsafe
                  (k + 4) s₁ s₂ (.CALLDATASIZE, none) hr₁ hdec₂
                · simpa [s₂] using calldataSizeState_step (k + 3) s₁
                · simp [xHaltOutput]
              _ = EVM.X (k + 3) validJumps s₃ := by
                rw [show k + 4 = (k + 3) + 1 by omega]
                apply X_step_of_pathPrecheck validJumps st hsafe
                  (k + 3) s₂ s₃ (.LT, none) hr₂ hdec₃
                · simpa [s₃] using calldataLtState_step (k + 2) s₂
                    (.ofNat st.executionEnv.calldata.size) (.ofNat 4) [] hs₂
                · simp [xHaltOutput]
              _ = EVM.X (k + 2) validJumps s₄ := by
                rw [show k + 3 = (k + 2) + 1 by omega]
                apply X_step_of_pathPrecheck validJumps st hsafe
                  (k + 2) s₃ s₄ (decodedPlainInstr (.push32 revertPc)) hr₃ hdec₄
                · simpa [s₄] using selectorPush32State_step revertPc (k + 1) s₃
                · simpa using xHaltOutput_push32_none s₄
              _ = EVM.X (k + 1) validJumps s₅ := by
                rw [show k + 2 = (k + 1) + 1 by omega]
                apply X_step_of_pathPrecheck validJumps st hsafe
                  (k + 1) s₄ s₅ (.JUMPI, none) hr₄ hdec₅
                · simpa [s₅] using selectorJumpiState_step k s₄
                    (.ofNat revertPc) s₃.stack.head! [] (by simpa [hs₃] using hs₄)
                · simp [xHaltOutput]
              _ = EVM.X (k + 1) validJumps (calldataGuardState revertPc st) := by
                rfl
            · exact hr₅

/-- Direct EvmYul execution of one resolved branch.  No readiness or execution certificate is an
input: the successor is the explicit `selectorBranchState`. -/
theorem resolvedSelectorBranch_X
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (pc selector targetPc suffixFuel : Nat)
    (rest : List Instr) (st : EVM.State)
    (hreach : EVMPathReach initial st)
    (hdecoder :
      DecoderAlong code pc (resolvedSelectorBranch selector targetPc ++ rest))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hstack : st.stack = []) (hwidth : pushWidth selector ≤ 32)
    (hsuffix : 0 < suffixFuel) :
    EVM.X (suffixFuel + 8) validJumps st =
        EVM.X suffixFuel validJumps (selectorBranchState selector targetPc st) ∧
      EVMPathReach initial (selectorBranchState selector targetPc st) := by
  let s₁ := selectorPushState 0 st
  let s₂ := selectorCalldataloadState s₁
  let s₃ := selectorPushState 0xE0 s₂
  let s₄ := selectorShrState s₃
  let s₅ := selectorPushState selector s₄
  let s₆ := selectorEqState s₅
  let s₇ := selectorPush32State targetPc s₆
  let s₈ := selectorJumpiState s₇
  change DecoderAlong code pc
    ([.push 0, .op .CALLDATALOAD, .push 0xE0, .op .SHR,
      .push selector, .op .EQ, .push32 targetPc, .op .JUMPI] ++ rest) at hdecoder
  cases hdecoder with
  | cons _ _ _ hd₁ hr₁ =>
    cases hr₁ with
    | cons _ _ _ hd₂ hr₂ =>
      cases hr₂ with
      | cons _ _ _ hd₃ hr₃ =>
        cases hr₃ with
        | cons _ _ _ hd₄ hr₄ =>
          cases hr₄ with
          | cons _ _ _ hd₅ hr₅ =>
            cases hr₅ with
            | cons _ _ _ hd₆ hr₆ =>
              cases hr₆ with
              | cons _ _ _ hd₇ hr₇ =>
                cases hr₇ with
                | cons _ _ _ hd₈ hr₈ =>
                  have hs₁ : s₁.stack = [.ofNat 0] := by
                    simp [s₁, selectorPushState, checkedState, hstack]
                  have hs₂ :
                      s₂.stack =
                        [EvmYul.State.calldataload s₂.toState (.ofNat 0)] := by
                    simp [s₂, selectorCalldataloadState, checkedState, hs₁]
                  have hs₃ :
                      s₃.stack = .ofNat 0xE0 ::
                        EvmYul.State.calldataload s₂.toState (.ofNat 0) :: [] := by
                    simp [s₃, selectorPushState, checkedState, hs₂]
                  have hs₄ : s₄.stack =
                      UInt256.shiftRight
                        (EvmYul.State.calldataload s₂.toState (.ofNat 0))
                        (.ofNat 0xE0) :: [] := by
                    simp [s₄, selectorShrState, checkedState, hs₃]
                  have hs₅ : s₅.stack = .ofNat selector :: s₄.stack := by
                    simp [s₅, selectorPushState, checkedState]
                  have hs₆ : s₆.stack =
                      UInt256.eq (.ofNat selector) s₄.stack.head! :: [] := by
                    simp [s₆, selectorEqState, checkedState, hs₅, hs₄]
                  have hs₇ : s₇.stack = .ofNat targetPc :: s₆.stack := by
                    simp [s₇, selectorPush32State, checkedState]
                  have hs₈ : s₈ = selectorBranchState selector targetPc st := by
                    rfl
                  have hp₁ : s₁.pc = .ofNat (pc + 1) := by
                    simp [s₁, selectorPushState, checkedState, hpc, pushWidth,
                      wordOfNat_add]
                  have hp₂ : s₂.pc = .ofNat (pc + 2) := by
                    simp [s₂, selectorCalldataloadState, checkedState, hp₁,
                      wordOfNat_add]
                  have hp₃ : s₃.pc = .ofNat (pc + 4) := by
                    simp [s₃, selectorPushState, checkedState, hp₂, pushWidth,
                      wordOfNat_add]
                    congr 1 <;> omega
                  have hp₄ : s₄.pc = .ofNat (pc + 5) := by
                    simp [s₄, selectorShrState, checkedState, hp₃, wordOfNat_add]
                  have hp₅ :
                      s₅.pc = .ofNat (pc + 6 + pushWidth selector) := by
                    simp [s₅, selectorPushState, checkedState, hp₄, wordOfNat_add]
                    congr 1 <;> omega
                  have hp₆ :
                      s₆.pc = .ofNat (pc + 7 + pushWidth selector) := by
                    simp [s₆, selectorEqState, checkedState, hp₅, wordOfNat_add]
                    congr 1 <;> omega
                  have hp₇ :
                      s₇.pc = .ofNat (pc + 40 + pushWidth selector) := by
                    simp [s₇, selectorPush32State, checkedState, hp₆, wordOfNat_add]
                    congr 1 <;> omega
                  have henv₁ : s₁.executionEnv.code = code := by
                    simp [s₁, selectorPushState, checkedState, hcode]
                  have henv₂ : s₂.executionEnv.code = code := by
                    simp [s₂, selectorCalldataloadState, checkedState, henv₁]
                  have henv₃ : s₃.executionEnv.code = code := by
                    simp [s₃, selectorPushState, checkedState, henv₂]
                  have henv₄ : s₄.executionEnv.code = code := by
                    simp [s₄, selectorShrState, checkedState, henv₃]
                  have henv₅ : s₅.executionEnv.code = code := by
                    simp [s₅, selectorPushState, checkedState, henv₄]
                  have henv₆ : s₆.executionEnv.code = code := by
                    simp [s₆, selectorEqState, checkedState, henv₅]
                  have henv₇ : s₇.executionEnv.code = code := by
                    simp [s₇, selectorPush32State, checkedState, henv₆]
                  have hw0 : pushWidth 0 = 0 := rfl
                  have hw224 : pushWidth 0xE0 = 1 := by decide
                  have hdec₁ :
                      EVM.decode st.executionEnv.code st.pc =
                        some (decodedPlainInstr (.push 0)) := by
                    simpa [hcode, hpc] using hd₁
                  have hdec₂ :
                      EVM.decode s₁.executionEnv.code s₁.pc =
                        some (.CALLDATALOAD, none) := by
                    rw [henv₁, hp₁]
                    simpa [instrByteSize, pushWidth] using hd₂
                  have hdec₃ :
                      EVM.decode s₂.executionEnv.code s₂.pc =
                        some (decodedPlainInstr (.push 0xE0)) := by
                    rw [henv₂, hp₂]
                    simpa [instrByteSize, pushWidth] using hd₃
                  have hdec₄ :
                      EVM.decode s₃.executionEnv.code s₃.pc =
                        some (.SHR, none) := by
                    rw [henv₃, hp₃]
                    simpa [instrByteSize, pushWidth] using hd₄
                  have hdec₅ :
                      EVM.decode s₄.executionEnv.code s₄.pc =
                        some (decodedPlainInstr (.push selector)) := by
                    rw [henv₄, hp₄]
                    simpa [instrByteSize, pushWidth] using hd₅
                  have hdec₆ :
                      EVM.decode s₅.executionEnv.code s₅.pc =
                        some (.EQ, none) := by
                    rw [henv₅, hp₅]
                    convert hd₆ using 1 <;>
                      simp [instrByteSize, hw0, hw224] <;> congr 2 <;> omega
                  have hdec₇ :
                      EVM.decode s₆.executionEnv.code s₆.pc =
                        some (decodedPlainInstr (.push32 targetPc)) := by
                    rw [henv₆, hp₆]
                    convert hd₇ using 1 <;>
                      simp [instrByteSize, hw0, hw224] <;> congr 2 <;> omega
                  have hdec₈ :
                      EVM.decode s₇.executionEnv.code s₇.pc =
                        some (.JUMPI, none) := by
                    rw [henv₇, hp₇]
                    convert hd₈ using 1 <;>
                      simp [instrByteSize, hw0, hw224] <;> congr 2 <;> omega
                  have hr₁ : EVMPathReach initial s₁ :=
                    .step hreach hdec₁
                      (by simpa [s₁] using selectorPushState_step 0 0 (by decide) st)
                      (xHaltOutput_decodedPush_none 0 (by decide) s₁)
                  have hr₂ : EVMPathReach initial s₂ :=
                    .step hr₁ hdec₂
                      (by simpa [s₂] using
                        selectorCalldataloadState_step 0 s₁ (.ofNat 0) [] hs₁)
                      (by simp [xHaltOutput])
                  have hr₃ : EVMPathReach initial s₃ :=
                    .step hr₂ hdec₃
                      (by simpa [s₃] using
                        selectorPushState_step 0xE0 0 (by decide) s₂)
                      (xHaltOutput_decodedPush_none 0xE0 (by decide) s₃)
                  have hr₄ : EVMPathReach initial s₄ :=
                    .step hr₃ hdec₄
                      (by simpa [s₄] using (selectorShrState_step 0 s₃
                        (.ofNat 0xE0)
                        (EvmYul.State.calldataload s₂.toState (.ofNat 0)) [] hs₃))
                      (by simp [xHaltOutput])
                  have hr₅ : EVMPathReach initial s₅ :=
                    .step hr₄ hdec₅
                      (by simpa [s₅] using
                        selectorPushState_step selector 0 hwidth s₄)
                      (xHaltOutput_decodedPush_none selector hwidth s₅)
                  have hr₆ : EVMPathReach initial s₆ :=
                    .step hr₅ hdec₆
                      (by simpa [s₆] using (selectorEqState_step 0 s₅
                        (.ofNat selector) s₄.stack.head! []
                        (by simpa [hs₄] using hs₅)))
                      (by simp [xHaltOutput])
                  have hr₇ : EVMPathReach initial s₇ :=
                    .step hr₆ hdec₇
                      (by simpa [s₇] using selectorPush32State_step targetPc 0 s₆)
                      (by simpa using xHaltOutput_push32_none s₇)
                  have hr₈ : EVMPathReach initial s₈ :=
                    .step hr₇ hdec₈
                      (by simpa [s₈] using (selectorJumpiState_step 0 s₇
                        (.ofNat targetPc) s₆.stack.head! []
                        (by simpa [hs₆] using hs₇)))
                      (by simp [xHaltOutput])
                  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
                    (Nat.ne_of_gt hsuffix)
                  constructor
                  · calc
                    EVM.X (k + 1 + 8) validJumps st =
                        EVM.X (k + 8) validJumps s₁ := by
                      rw [show k + 1 + 8 = (k + 8) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 8) st s₁ (decodedPlainInstr (.push 0)) hreach hdec₁
                      · simpa [s₁] using selectorPushState_step 0 (k + 7) (by decide) st
                      · exact xHaltOutput_decodedPush_none 0 (by decide) s₁
                    _ = EVM.X (k + 7) validJumps s₂ := by
                      rw [show k + 8 = (k + 7) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 7) s₁ s₂ (.CALLDATALOAD, none) hr₁ hdec₂
                      · simpa [s₂] using
                          selectorCalldataloadState_step (k + 6) s₁ (.ofNat 0) [] hs₁
                      · simp [xHaltOutput, s₂]
                    _ = EVM.X (k + 6) validJumps s₃ := by
                      rw [show k + 7 = (k + 6) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 6) s₂ s₃ (decodedPlainInstr (.push 0xE0)) hr₂ hdec₃
                      · simpa [s₃] using
                          selectorPushState_step 0xE0 (k + 5) (by decide) s₂
                      · exact xHaltOutput_decodedPush_none 0xE0 (by decide) s₃
                    _ = EVM.X (k + 5) validJumps s₄ := by
                      rw [show k + 6 = (k + 5) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 5) s₃ s₄ (.SHR, none) hr₃ hdec₄
                      · simpa [s₄] using selectorShrState_step (k + 4) s₃
                          (.ofNat 0xE0)
                          (EvmYul.State.calldataload s₂.toState (.ofNat 0)) [] hs₃
                      · simp [xHaltOutput, s₄]
                    _ = EVM.X (k + 4) validJumps s₅ := by
                      rw [show k + 5 = (k + 4) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 4) s₄ s₅ (decodedPlainInstr (.push selector)) hr₄ hdec₅
                      · simpa [s₅] using
                          selectorPushState_step selector (k + 3) hwidth s₄
                      · exact xHaltOutput_decodedPush_none selector hwidth s₅
                    _ = EVM.X (k + 3) validJumps s₆ := by
                      rw [show k + 4 = (k + 3) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 3) s₅ s₆ (.EQ, none) hr₅ hdec₆
                      · simpa [s₆] using selectorEqState_step (k + 2) s₅
                          (.ofNat selector) s₄.stack.head! [] (by simpa [hs₄] using hs₅)
                      · simp [xHaltOutput, s₆]
                    _ = EVM.X (k + 2) validJumps s₇ := by
                      rw [show k + 3 = (k + 2) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 2) s₆ s₇ (decodedPlainInstr (.push32 targetPc)) hr₆ hdec₇
                      · simpa [s₇] using selectorPush32State_step targetPc (k + 1) s₆
                      · simpa using xHaltOutput_push32_none s₇
                    _ = EVM.X (k + 1) validJumps s₈ := by
                      rw [show k + 2 = (k + 1) + 1 by omega]
                      apply X_step_of_pathPrecheck validJumps initial hsafe
                        (k + 1) s₇ s₈ (.JUMPI, none) hr₇ hdec₈
                      · simpa [s₈] using selectorJumpiState_step k s₇
                          (.ofNat targetPc) s₆.stack.head! [] (by simpa [hs₆] using hs₇)
                      · simp [xHaltOutput, s₈]
                    _ = EVM.X (k + 1) validJumps
                        (selectorBranchState selector targetPc st) := by rw [hs₈]
                  · simpa [hs₈] using hr₈

/-- Direct execution skips every preceding non-matching branch and takes the selected branch.
The existential state is constructed by the recursive proof; only the suffix `X` remains opaque. -/
theorem resolvedSelectorBranches_X_reaches
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (before after : List (Nat × Nat))
    (selected targetPc pc suffixFuel : Nat) (rest : List Instr) (st : EVM.State)
    (hreach : EVMPathReach initial st)
    (hdecoder : DecoderAlong code pc
      (resolvedSelectorBranches
        (before ++ (selected, targetPc) :: after) ++ rest))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hstack : st.stack = [])
    (hselector : decodeSelector st.executionEnv.calldata = .ofNat selected)
    (hwidthSelected : pushWidth selected ≤ 32)
    (hwidthBefore : ∀ pair ∈ before, pushWidth pair.1 ≤ 32)
    (hdistinct : ∀ pair ∈ before,
      (.ofNat pair.1 : Word) ≠ .ofNat selected)
    (hsuffix : 0 < suffixFuel) :
    ∃ bodyState,
      bodyState.stack = [] ∧
      bodyState.pc = .ofNat targetPc ∧
      bodyState.executionEnv = st.executionEnv ∧
      bodyState.memory = st.memory ∧
      bodyState.toState = st.toState ∧
      EVMPathReach initial bodyState ∧
      EVM.X (suffixFuel + 8 * (before.length + 1)) validJumps st =
        EVM.X suffixFuel validJumps bodyState := by
  induction before generalizing pc st with
  | nil =>
      have hbranch :
          DecoderAlong code pc
            (resolvedSelectorBranch selected targetPc ++
              (resolvedSelectorBranches after ++ rest)) := by
        simpa [resolvedSelectorBranches, List.append_assoc] using hdecoder
      let bodyState := selectorBranchState selected targetPc st
      refine ⟨bodyState, selectorBranchState_stack selected targetPc st hstack,
        selectorBranchState_pc_match selected targetPc st hstack hselector,
        selectorBranchState_executionEnv selected targetPc st,
        selectorBranchState_memory selected targetPc st,
        selectorBranchState_toState selected targetPc st,
        (resolvedSelectorBranch_X validJumps initial hsafe code pc selected targetPc
          1 (resolvedSelectorBranches after ++ rest) st hreach hbranch hcode hpc
          hstack hwidthSelected (by decide)).2, ?_⟩
      simpa [bodyState] using
        (resolvedSelectorBranch_X validJumps initial hsafe code pc selected targetPc
          suffixFuel (resolvedSelectorBranches after ++ rest) st hreach hbranch hcode
          hpc hstack hwidthSelected hsuffix).1
  | cons pair before ih =>
      rcases pair with ⟨current, currentTarget⟩
      have hbranch :
          DecoderAlong code pc
            (resolvedSelectorBranch current currentTarget ++
              (resolvedSelectorBranches
                (before ++ (selected, targetPc) :: after) ++ rest)) := by
        simpa [resolvedSelectorBranches, List.append_assoc] using hdecoder
      let next := selectorBranchState current currentTarget st
      have hnextReach : EVMPathReach initial next := by
        exact (resolvedSelectorBranch_X validJumps initial hsafe code pc current
          currentTarget 1
          (resolvedSelectorBranches
            (before ++ (selected, targetPc) :: after) ++ rest)
          st hreach hbranch hcode hpc hstack
          (hwidthBefore (current, currentTarget) (by simp)) (by decide)).2
      have hnextStack : next.stack = [] :=
        selectorBranchState_stack current currentTarget st hstack
      have hcurrentWidth : pushWidth current ≤ 32 :=
        hwidthBefore (current, currentTarget) (by simp)
      have hcurrentNe : (.ofNat current : Word) ≠ .ofNat selected :=
        hdistinct (current, currentTarget) (by simp)
      have hnextPc :
          next.pc =
            .ofNat (pc + instrsByteSize
              (resolvedSelectorBranch current currentTarget)) := by
        exact selectorBranchState_pc_mismatch pc current currentTarget selected st
          hpc hstack hselector hcurrentNe
      have hnextCode : next.executionEnv.code = code := by
        rw [selectorBranchState_executionEnv]
        exact hcode
      have hnextSelector :
          decodeSelector next.executionEnv.calldata = .ofNat selected := by
        rw [selectorBranchState_executionEnv]
        exact hselector
      have hrestDecoder :
          DecoderAlong code
            (pc + instrsByteSize (resolvedSelectorBranch current currentTarget))
            (resolvedSelectorBranches
              (before ++ (selected, targetPc) :: after) ++ rest) := by
        have := DecoderAlong.dropPrefix
          (resolvedSelectorBranch current currentTarget)
          (resolvedSelectorBranches
            (before ++ (selected, targetPc) :: after) ++ rest) hbranch
        simpa [instrsByteSize] using this
      obtain ⟨bodyState, hbodyStack, hbodyPc, hbodyEnv, hbodyMemory, hbodyToState,
          hbodyReach, htail⟩ :=
        ih (pc := pc + instrsByteSize
          (resolvedSelectorBranch current currentTarget))
          (st := next) hnextReach hrestDecoder hnextCode hnextPc hnextStack
          hnextSelector
          (fun p hp => hwidthBefore p (by simp [hp]))
          (fun p hp => hdistinct p (by simp [hp]))
      refine ⟨bodyState, hbodyStack, hbodyPc, ?_, ?_, ?_, hbodyReach, ?_⟩
      · rw [hbodyEnv, selectorBranchState_executionEnv]
      · rw [hbodyMemory, selectorBranchState_memory]
      · rw [hbodyToState, selectorBranchState_toState]
      have hhead := (resolvedSelectorBranch_X validJumps initial hsafe code pc current
        currentTarget
        (suffixFuel + 8 * (before.length + 1))
        (resolvedSelectorBranches
          (before ++ (selected, targetPc) :: after) ++ rest)
        st hreach hbranch hcode hpc hstack hcurrentWidth (by omega)).1
      calc
        EVM.X (suffixFuel + 8 * ((current, currentTarget) :: before).length.succ)
            validJumps st =
            EVM.X ((suffixFuel + 8 * (before.length + 1)) + 8)
              validJumps st := by
                congr 1
        _ = EVM.X (suffixFuel + 8 * (before.length + 1)) validJumps next := hhead
        _ = EVM.X suffixFuel validJumps bodyState := htail

/-- Every recursively generated selector branch falls through when the calldata selector differs
from all branch selectors. -/
theorem resolvedSelectorBranches_X_miss
    (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (pairs : List (Nat × Nat)) (selected pc suffixFuel : Nat)
    (rest : List Instr) (st : EVM.State)
    (hreach : EVMPathReach initial st)
    (hdecoder : DecoderAlong code pc (resolvedSelectorBranches pairs ++ rest))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hstack : st.stack = [])
    (hselector : decodeSelector st.executionEnv.calldata = .ofNat selected)
    (hwidth : ∀ pair ∈ pairs, pushWidth pair.1 ≤ 32)
    (hdistinct : ∀ pair ∈ pairs, (.ofNat pair.1 : Word) ≠ .ofNat selected)
    (hsuffix : 0 < suffixFuel) :
    ∃ endState,
      endState.stack = [] ∧
      endState.pc =
        .ofNat (pc + instrsByteSize (resolvedSelectorBranches pairs)) ∧
      endState.executionEnv = st.executionEnv ∧
      endState.memory = st.memory ∧
      endState.toState = st.toState ∧
      EVMPathReach initial endState ∧
      EVM.X (suffixFuel + 8 * pairs.length) validJumps st =
        EVM.X suffixFuel validJumps endState := by
  induction pairs generalizing pc st with
  | nil =>
      refine ⟨st, hstack, ?_, rfl, rfl, rfl, hreach, ?_⟩
      · simp [resolvedSelectorBranches, instrsByteSize, hpc]
      · simp
  | cons pair pairs ih =>
      rcases pair with ⟨selector, targetPc⟩
      have hbranch :
          DecoderAlong code pc
            (resolvedSelectorBranch selector targetPc ++
              (resolvedSelectorBranches pairs ++ rest)) := by
        simpa [resolvedSelectorBranches, List.append_assoc] using hdecoder
      let next := selectorBranchState selector targetPc st
      have hnextReach : EVMPathReach initial next :=
        (resolvedSelectorBranch_X validJumps initial hsafe code pc selector targetPc
          1 (resolvedSelectorBranches pairs ++ rest) st hreach hbranch hcode hpc
          hstack (hwidth (selector, targetPc) (by simp)) (by decide)).2
      have hnextPc :
          next.pc = .ofNat (pc + instrsByteSize
            (resolvedSelectorBranch selector targetPc)) :=
        selectorBranchState_pc_mismatch pc selector targetPc selected st hpc hstack
          hselector (hdistinct (selector, targetPc) (by simp))
      have hrestDecoder :
          DecoderAlong code
            (pc + instrsByteSize (resolvedSelectorBranch selector targetPc))
            (resolvedSelectorBranches pairs ++ rest) := by
        have := DecoderAlong.dropPrefix (resolvedSelectorBranch selector targetPc)
          (resolvedSelectorBranches pairs ++ rest) hbranch
        simpa [instrsByteSize] using this
      obtain ⟨endState, hendStack, hendPc, hendEnv, hendMemory, hendToState,
          hendReach, htail⟩ :=
        ih (pc := pc + instrsByteSize (resolvedSelectorBranch selector targetPc))
          (st := next) hnextReach hrestDecoder
          (by rw [selectorBranchState_executionEnv, hcode]) hnextPc
          (selectorBranchState_stack selector targetPc st hstack)
          (by rw [selectorBranchState_executionEnv]; exact hselector)
          (fun p hp => hwidth p (by simp [hp]))
          (fun p hp => hdistinct p (by simp [hp]))
      refine ⟨endState, hendStack, ?_, ?_, ?_, ?_, hendReach, ?_⟩
      · rw [hendPc]
        simp [resolvedSelectorBranches, instrsByteSize]
        congr 1
        omega
      · rw [hendEnv, selectorBranchState_executionEnv]
      · rw [hendMemory, selectorBranchState_memory]
      · rw [hendToState, selectorBranchState_toState]
      · have hhead := (resolvedSelectorBranch_X validJumps initial hsafe code pc
          selector targetPc (suffixFuel + 8 * pairs.length)
          (resolvedSelectorBranches pairs ++ rest) st hreach hbranch hcode hpc
          hstack (hwidth (selector, targetPc) (by simp)) (by omega)).1
        calc
          EVM.X (suffixFuel + 8 * ((selector, targetPc) :: pairs).length)
              validJumps st =
              EVM.X ((suffixFuel + 8 * pairs.length) + 8) validJumps st := by
                congr 1
          _ = EVM.X (suffixFuel + 8 * pairs.length) validJumps next := hhead
          _ = EVM.X suffixFuel validJumps endState := htail

/-- Production-code specialization.  `productionDecoderAlong` supplies every decoder equation from
`Encode.encode`; the label lookup retained in the result is the deterministic production target. -/
theorem productionSelectorBranches_X_reaches
    (instrs resolved pre suffix : List Instr) (code : ByteArray)
    (before after : List (Nat × Nat)) (selected targetPc suffixFuel : Nat)
    (selectedLabel : String) (validJumps : Array Word) (st : EVM.State)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64)
    (hresolvedShape :
      resolved =
        pre ++
          (resolvedSelectorBranches
            (before ++ (selected, targetPc) :: after) ++ suffix))
    (hlabel :
      lookupLabel (fixpointLabels instrs) selectedLabel = .ok targetPc)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code)
    (hpc :
      st.pc = .ofNat (pre.map (instrByteSize [])).sum)
    (hstack : st.stack = [])
    (hselector : decodeSelector st.executionEnv.calldata = .ofNat selected)
    (hwidthSelected : pushWidth selected ≤ 32)
    (hwidthBefore : ∀ pair ∈ before, pushWidth pair.1 ≤ 32)
    (hdistinct : ∀ pair ∈ before,
      (.ofNat pair.1 : Word) ≠ .ofNat selected)
    (hsuffix : 0 < suffixFuel) :
    ∃ bodyState,
      lookupLabel (fixpointLabels instrs) selectedLabel = .ok targetPc ∧
      bodyState.stack = [] ∧
      bodyState.pc = .ofNat targetPc ∧
      EVM.X (suffixFuel + 8 * (before.length + 1)) validJumps st =
        EVM.X suffixFuel validJumps bodyState := by
  have hall : DecoderAlong code 0 resolved :=
    productionDecoderAlong instrs resolved code hencode hresolve hencodable hlimit
  have hgrouped :
      DecoderAlong code 0
        (pre ++
          (resolvedSelectorBranches
            (before ++ (selected, targetPc) :: after) ++ suffix)) := by
    simpa [hresolvedShape] using hall
  have hdispatch := DecoderAlong.dropPrefix pre
    (resolvedSelectorBranches
      (before ++ (selected, targetPc) :: after) ++ suffix) hgrouped
  have hdispatch' :
      DecoderAlong code (pre.map (instrByteSize [])).sum
        (resolvedSelectorBranches
          (before ++ (selected, targetPc) :: after) ++ suffix) := by
    simpa using hdispatch
  obtain ⟨bodyState, hbodyStack, hbodyPc, _, _, _, _, hx⟩ :=
    resolvedSelectorBranches_X_reaches validJumps st hsafe code before after selected
      targetPc (pre.map (instrByteSize [])).sum suffixFuel suffix st
      .initial hdispatch' hcode hpc hstack hselector hwidthSelected hwidthBefore
      hdistinct hsuffix
  exact ⟨bodyState, hlabel, hbodyStack, hbodyPc, hx⟩

/-- Production guard followed by the recursive selector search, starting at actual PC zero. -/
theorem productionGuardSelector_X_reaches
    {abiSelector : Nat} {args : List Word} {calldata : ByteArray}
    (instrs resolved suffix : List Instr) (code : ByteArray)
    (before after : List (Nat × Nat)) (targetPc revertPc suffixFuel : Nat)
    (selectedLabel : String) (validJumps : Array Word) (st : EVM.State)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64)
    (hresolvedShape :
      resolved =
        resolvedCalldataGuard revertPc ++
          (resolvedSelectorBranches
            (before ++ (abiSelector, targetPc) :: after) ++ suffix))
    (hlabel :
      lookupLabel (fixpointLabels instrs) selectedLabel = .ok targetPc)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hwf : WellFormed abiSelector args calldata)
    (hwidthSelected : pushWidth abiSelector ≤ 32)
    (hwidthBefore : ∀ pair ∈ before, pushWidth pair.1 ≤ 32)
    (hdistinct : ∀ pair ∈ before,
      (.ofNat pair.1 : Word) ≠ .ofNat abiSelector)
    (hsuffix : 0 < suffixFuel) :
    ∃ bodyState,
      lookupLabel (fixpointLabels instrs) selectedLabel = .ok targetPc ∧
      bodyState.stack = [] ∧
      bodyState.memory = ByteArray.empty ∧
      bodyState.executionEnv = st.executionEnv ∧
      bodyState.toState = st.toState ∧
      bodyState.pc = .ofNat targetPc ∧
      EVMPathReach st bodyState ∧
      EVM.X (suffixFuel + 8 * (before.length + 1) + 5) validJumps st =
        EVM.X suffixFuel validJumps bodyState := by
  have hall : DecoderAlong code 0 resolved :=
    productionDecoderAlong instrs resolved code hencode hresolve hencodable hlimit
  have hfull :
      DecoderAlong code 0
        (resolvedCalldataGuard revertPc ++
          (resolvedSelectorBranches
            (before ++ (abiSelector, targetPc) :: after) ++ suffix)) := by
    simpa [hresolvedShape] using hall
  have hguardDecoder := DecoderAlong.takePrefix
    (resolvedCalldataGuard revertPc)
    (resolvedSelectorBranches
      (before ++ (abiSelector, targetPc) :: after) ++ suffix) hfull
  have hbranchDecoder₀ := DecoderAlong.dropPrefix
    (resolvedCalldataGuard revertPc)
    (resolvedSelectorBranches
      (before ++ (abiSelector, targetPc) :: after) ++ suffix) hfull
  have hguardPc :
      (calldataGuardState revertPc st).pc =
        .ofNat (resolvedCalldataGuard revertPc |>.map (instrByteSize []) |>.sum) := by
    simpa [instrsByteSize] using
      calldataGuardState_pc_wellFormed revertPc st hpc hstack hcalldata hwf
  have hguardStack : (calldataGuardState revertPc st).stack = [] :=
    calldataGuardState_stack revertPc st hstack
  have hguardEnv :
      (calldataGuardState revertPc st).executionEnv = st.executionEnv :=
    calldataGuardState_executionEnv revertPc st
  have hguardCode :
      (calldataGuardState revertPc st).executionEnv.code = code := by
    rw [hguardEnv]
    exact hcode
  have hguardSelector :
      decodeSelector (calldataGuardState revertPc st).executionEnv.calldata =
        .ofNat abiSelector := by
    rw [hguardEnv, hcalldata]
    exact hwf.selector_eq
  obtain ⟨bodyState, hbodyStack, hbodyPc, hbodyGuardEnv, hbodyGuardMemory,
      hbodyGuardToState, hbodyReach, hbranches⟩ :=
    resolvedSelectorBranches_X_reaches validJumps st hsafe code before after abiSelector
      targetPc (resolvedCalldataGuard revertPc |>.map (instrByteSize []) |>.sum)
      suffixFuel suffix (calldataGuardState revertPc st)
      ((resolvedCalldataGuard_X validJumps code revertPc 1
        (resolvedSelectorBranches
          (before ++ (abiSelector, targetPc) :: after) ++ suffix)
        st hsafe (by simpa using hfull) hcode hpc hstack (by decide)).2)
      (by simpa using hbranchDecoder₀) hguardCode hguardPc hguardStack hguardSelector
      hwidthSelected hwidthBefore hdistinct hsuffix
  have hguardX := (resolvedCalldataGuard_X validJumps code revertPc
    (suffixFuel + 8 * (before.length + 1))
    (resolvedSelectorBranches
      (before ++ (abiSelector, targetPc) :: after) ++ suffix)
    st hsafe (by simpa using hfull) hcode hpc hstack (by omega)).1
  have hbodyEnv : bodyState.executionEnv = st.executionEnv := by
    rw [hbodyGuardEnv, hguardEnv]
  have hbodyMemory : bodyState.memory = ByteArray.empty := by
    rw [hbodyGuardMemory, calldataGuardState_memory, hmemory]
  have hbodyToState : bodyState.toState = st.toState := by
    rw [hbodyGuardToState, calldataGuardState_toState]
  refine ⟨bodyState, hlabel, hbodyStack, hbodyMemory, hbodyEnv, hbodyToState,
    hbodyPc, hbodyReach, ?_⟩
  calc
    EVM.X (suffixFuel + 8 * (before.length + 1) + 5) validJumps st =
        EVM.X (suffixFuel + 8 * (before.length + 1))
          validJumps (calldataGuardState revertPc st) := hguardX
    _ = EVM.X suffixFuel validJumps bodyState := hbranches

private def jumpdestState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .JUMPDEST
  { checked with
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable -
      .ofNat (checkedCost st .JUMPDEST)
    execLength := checked.execLength + 1 }

private theorem jumpdestState_step (st : EVM.State) :
    EVM.step 1 (checkedCost st .JUMPDEST) (some (.JUMPDEST, none))
        (checkedState st .JUMPDEST) =
      .ok (jumpdestState st) := by
  simpa [jumpdestState] using
    evmStep_jumpdest 0 (checkedCost st .JUMPDEST) (checkedState st .JUMPDEST)

private def mstoreZeroState (value : Word) (st : EVM.State) : EVM.State :=
  let checked := checkedState st .MSTORE
  { checked with
    stack := []
    toMachineState := EvmYul.MachineState.mstore
      { checked.toMachineState with
        gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .MSTORE) }
      (.ofNat 0) value
    pc := checked.pc + .ofNat 1
    execLength := checked.execLength + 1 }

private theorem mstoreZeroState_step (value : Word) (st : EVM.State)
    (hstack : st.stack = .ofNat 0 :: value :: []) :
    EVM.step 1 (checkedCost st .MSTORE) (some (.MSTORE, none))
        (checkedState st .MSTORE) =
      .ok (mstoreZeroState value st) := by
  have hcstack :
      (checkedState st .MSTORE).stack = .ofNat 0 :: value :: [] := by
    simp [checkedState, hstack]
  rw [state_setStack (checkedState st .MSTORE) _ hcstack]
  simpa [mstoreZeroState] using
    evmStep_mstore 0 (checkedCost st .MSTORE) (checkedState st .MSTORE)
      (.ofNat 0) value []

private def revertState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .REVERT
  { checked with
    stack := []
    toMachineState := EvmYul.MachineState.evmRevert
      { checked.toMachineState with
        gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .REVERT) }
      (.ofNat 0) st.stack[1]!
    pc := checked.pc + .ofNat 1
    execLength := checked.execLength + 1 }

private theorem revertState_step (size : Word) (st : EVM.State)
    (hstack : st.stack = .ofNat 0 :: size :: []) :
    EVM.step 1 (checkedCost st .REVERT) (some (.REVERT, none))
        (checkedState st .REVERT) =
      .ok (revertState st) := by
  have hcstack :
      (checkedState st .REVERT).stack = .ofNat 0 :: size :: [] := by
    simp [checkedState, hstack]
  rw [state_setStack (checkedState st .REVERT) _ hcstack]
  simpa [revertState, hstack] using
    evmStep_revert 0 (checkedCost st .REVERT) (checkedState st .REVERT)
      (.ofNat 0) size []

private theorem dispatchRevert_runView
    (cfg : Config) (st : EVM.State)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hwidth : ∀ selector,
      cfg.errors.errorSelector "InvalidSelector" = some selector →
        pushWidth (paddedSelector selector) ≤ 32) :
    ∃ pre final,
      dispatchRevert cfg = pre ++ [.op .REVERT] ∧
      PureViewInstrs pre ∧
      runView (pre ++ [.op .REVERT]) st = .ok final ∧
      final.H_return = dispatchRevertBytes cfg := by
  cases hselector : cfg.errors.errorSelector "InvalidSelector" with
  | none =>
      let s₁ := selectorPushState 0 st
      let s₂ := selectorPushState 0 s₁
      let final := revertState s₂
      have hs₁ : s₁.stack = [.ofNat 0] := by
        simp [s₁, selectorPushState, checkedState, hstack]
      have hs₂ : s₂.stack = [.ofNat 0, .ofNat 0] := by
        simp [s₂, selectorPushState, checkedState, hs₁]
      have h₁ := selectorPushState_step 0 0 (by decide : pushWidth 0 ≤ 32) st
      have h₂ := selectorPushState_step 0 0 (by decide : pushWidth 0 ≤ 32) s₁
      have h₃ := revertState_step (.ofNat 0) s₂ hs₂
      refine ⟨[.push 0, .push 0], final, ?_, ?_, ?_, ?_⟩
      · simp [dispatchRevert, hselector]
      · intro instr hmem
        simp at hmem
        rcases hmem with rfl | rfl
        all_goals simp only [PureViewInstr]
        all_goals decide
      ·
        change (do
          let a ← EVM.step 1 (checkedCost st (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState st (decodedPlainInstr (.push 0)).1)
          let b ← EVM.step 1 (checkedCost a (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState a (decodedPlainInstr (.push 0)).1)
          EVM.step 1 (checkedCost b .REVERT) (some (.REVERT, none))
            (checkedState b .REVERT)) = .ok final
        rw [show EVM.step 1 (checkedCost st (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState st (decodedPlainInstr (.push 0)).1) = .ok s₁ by
          simpa [s₁] using h₁]
        simp only [Bind.bind, Except.bind]
        rw [show EVM.step 1 (checkedCost s₁ (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState s₁ (decodedPlainInstr (.push 0)).1) = .ok s₂ by
          simpa [s₂] using h₂]
        simp only [Bind.bind, Except.bind]
        simpa [final] using h₃
      · simp [final, revertState, checkedState, EvmYul.MachineState.evmRevert,
          EvmYul.MachineState.evmReturn, s₂, selectorPushState, s₁, hstack,
          hmemory, hs₂, dispatchRevertBytes, hselector]
        change ByteArray.empty.readWithPadding 0 0 = ByteArray.empty
        simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding,
          zeroes_eq_replicate]
        rfl
  | some selector =>
      let value : Word := .ofNat (paddedSelector selector)
      let s₁ := selectorPushState (paddedSelector selector) st
      let s₂ := selectorPushState 0 s₁
      let s₃ := mstoreZeroState value s₂
      let s₄ := selectorPushState 4 s₃
      let s₅ := selectorPushState 0 s₄
      let final := revertState s₅
      have hw := hwidth selector hselector
      have hs₁ : s₁.stack = [value] := by
        simp [s₁, value, selectorPushState, checkedState, hstack]
      have hs₂ : s₂.stack = [.ofNat 0, value] := by
        simp [s₂, selectorPushState, checkedState, hs₁]
      have hs₃ : s₃.stack = [] := by
        simp [s₃, mstoreZeroState, checkedState]
      have hs₄ : s₄.stack = [.ofNat 4] := by
        simp [s₄, selectorPushState, checkedState, hs₃]
      have hs₅ : s₅.stack = [.ofNat 0, .ofNat 4] := by
        simp [s₅, selectorPushState, checkedState, hs₄]
      have h₁ := selectorPushState_step (paddedSelector selector) 0 hw st
      have h₂ := selectorPushState_step 0 0 (by decide : pushWidth 0 ≤ 32) s₁
      have h₃ := mstoreZeroState_step value s₂ hs₂
      have h₄ := selectorPushState_step 4 0 (by decide : pushWidth 4 ≤ 32) s₃
      have h₅ := selectorPushState_step 0 0 (by decide : pushWidth 0 ≤ 32) s₄
      have h₆ := revertState_step (.ofNat 4) s₅ hs₅
      refine ⟨[.push (paddedSelector selector), .push 0, .op .MSTORE,
          .push 4, .push 0], final, ?_, ?_, ?_, ?_⟩
      · simp [dispatchRevert, hselector]
      · intro instr hmem
        simp at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl
        all_goals simp only [PureViewInstr]
        · exact hw
        all_goals decide
      ·
        change (do
          let a ← EVM.step 1 (checkedCost st (decodedPlainInstr
              (.push (paddedSelector selector))).1)
            (some (decodedPlainInstr (.push (paddedSelector selector))))
            (checkedState st (decodedPlainInstr (.push (paddedSelector selector))).1)
          let b ← EVM.step 1 (checkedCost a (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState a (decodedPlainInstr (.push 0)).1)
          let c ← EVM.step 1 (checkedCost b .MSTORE) (some (.MSTORE, none))
            (checkedState b .MSTORE)
          let d ← EVM.step 1 (checkedCost c (decodedPlainInstr (.push 4)).1)
            (some (decodedPlainInstr (.push 4)))
            (checkedState c (decodedPlainInstr (.push 4)).1)
          let e ← EVM.step 1 (checkedCost d (decodedPlainInstr (.push 0)).1)
            (some (decodedPlainInstr (.push 0)))
            (checkedState d (decodedPlainInstr (.push 0)).1)
          EVM.step 1 (checkedCost e .REVERT) (some (.REVERT, none))
            (checkedState e .REVERT)) = .ok final
        rw [show EVM.step 1 _ _ _ = .ok s₁ by simpa [s₁] using h₁]
        simp only [Bind.bind, Except.bind]
        rw [show EVM.step 1 _ _ _ = .ok s₂ by simpa [s₂] using h₂]
        simp only [Bind.bind, Except.bind]
        rw [show EVM.step 1 _ _ _ = .ok s₃ by simpa [s₃] using h₃]
        simp only [Bind.bind, Except.bind]
        rw [show EVM.step 1 _ _ _ = .ok s₄ by simpa [s₄] using h₄]
        simp only [Bind.bind, Except.bind]
        rw [show EVM.step 1 _ _ _ = .ok s₅ by simpa [s₅] using h₅]
        simp only [Bind.bind, Except.bind]
        simpa [final] using h₆
      · have hs₃memory :
            s₃.memory =
              ((.ofNat (paddedSelector selector) : Word)).toByteArray.write
                0 ByteArray.empty 0 32 := by
          simp [s₃, mstoreZeroState, checkedState, s₂, selectorPushState,
            s₁, value, EvmYul.MachineState.mstore,
            EvmYul.MachineState.writeWord, EvmYul.writeBytes, hmemory]
          rfl
        have hs₅memory : s₅.memory = s₃.memory := by
          simp [s₅, selectorPushState, checkedState, s₄]
        simp only [final, revertState, checkedState,
          EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn, hs₅,
          dispatchRevertBytes, hselector, EvmYul.UInt256.toNat]
        rw [hs₅memory, hs₃memory]
        exact write_readWithPadding_4_empty
          ((.ofNat (paddedSelector selector) : Word)).toByteArray
          (uint256_toByteArray_size _)

private def jumpState (st : EVM.State) : EVM.State :=
  let checked := checkedState st .JUMP
  { checked with
    stack := []
    pc := st.stack.head!
    gasAvailable := checked.gasAvailable - .ofNat (checkedCost st .JUMP)
    execLength := checked.execLength + 1 }

private theorem jumpState_step (dest : Word) (st : EVM.State)
    (hstack : st.stack = [dest]) :
    EVM.step 1 (checkedCost st .JUMP) (some (.JUMP, none))
        (checkedState st .JUMP) = .ok (jumpState st) := by
  have hcstack : (checkedState st .JUMP).stack = dest :: [] := by
    simp [checkedState, hstack]
  rw [state_setStack (checkedState st .JUMP) _ hcstack]
  simpa [jumpState, hstack] using
    evmStep_jump 0 (checkedCost st .JUMP) (checkedState st .JUMP) dest []

private theorem resolvedRevertTail_X
    (cfg : Config) (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (pc revertPc : Nat) (st : EVM.State)
    (hreach : EVMPathReach initial st)
    (hdecoder : DecoderAlong code pc
      ([.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat pc)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hrevertPc : revertPc = pc + 34)
    (hrevertJump : (.ofNat revertPc : Word) ∈ validJumps)
    (hwidth : ∀ selector,
      cfg.errors.errorSelector "InvalidSelector" = some selector →
        pushWidth (paddedSelector selector) ≤ 32) :
    ∃ final : EVM.State,
      EVM.X ((dispatchRevert cfg).length + 4) validJumps st =
        .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := by
  have _ := hrevertJump
  obtain ⟨pre, final, hrevertShape, hpure, hrun, houtput⟩ :=
    dispatchRevert_runView cfg
      (jumpdestState (jumpState (selectorPush32State revertPc st)))
      (by simp [jumpdestState, jumpState, selectorPush32State, checkedState, hstack])
      (by simp [jumpdestState, jumpState, selectorPush32State, checkedState, hmemory])
      hwidth
  cases hdecoder with
  | cons _ _ _ hd₁ hr₁ =>
    cases hr₁ with
    | cons _ _ _ hd₂ hr₂ =>
      cases hr₂ with
      | cons _ _ _ hd₃ hdispatch =>
        let pushed := selectorPush32State revertPc st
        let jumped := jumpState pushed
        let entry := jumpdestState jumped
        have hpushedStack : pushed.stack = [.ofNat revertPc] := by
          simp [pushed, selectorPush32State, checkedState, hstack]
        have hpushedPc : pushed.pc = .ofNat (pc + 33) := by
          simp [pushed, selectorPush32State, checkedState, hpc, word_ofNat_add]
        have hpushedCode : pushed.executionEnv.code = code := by
          simp [pushed, selectorPush32State, checkedState, hcode]
        have hdecode₁ :
            EVM.decode st.executionEnv.code st.pc =
              some (decodedPlainInstr (.push32 revertPc)) := by
          simpa [hcode, hpc] using hd₁
        have hdecode₂ :
            EVM.decode pushed.executionEnv.code pushed.pc = some (.JUMP, none) := by
          rw [hpushedCode, hpushedPc]
          simpa [instrByteSize] using hd₂
        have hjumpedPc : jumped.pc = .ofNat revertPc := by
          simp [jumped, jumpState, checkedState, hpushedStack]
        have hjumpedCode : jumped.executionEnv.code = code := by
          simp [jumped, jumpState, checkedState, hpushedCode]
        have hdecode₃ :
            EVM.decode jumped.executionEnv.code jumped.pc =
              some (.JUMPDEST, none) := by
          rw [hjumpedCode, hjumpedPc, hrevertPc]
          simpa [instrByteSize] using hd₃
        have hrPushed : EVMPathReach initial pushed :=
          .step hreach hdecode₁
            (by simpa [pushed] using selectorPush32State_step revertPc 0 st)
            (by simpa using xHaltOutput_push32_none pushed)
        have hrJumped : EVMPathReach initial jumped :=
          .step hrPushed hdecode₂
            (by simpa [jumped] using jumpState_step (.ofNat revertPc) pushed hpushedStack)
            (by simp [xHaltOutput])
        have hrEntry : EVMPathReach initial entry :=
          .step hrJumped hdecode₃
            (by simpa [entry] using jumpdestState_step jumped)
            (by rfl)
        have hentryCode : entry.executionEnv.code = code := by
          simp [entry, jumpdestState, checkedState, hjumpedCode]
        have hentryPc : entry.pc = .ofNat (revertPc + 1) := by
          simp [entry, jumpdestState, checkedState, hjumpedPc, word_ofNat_add]
        have hdispatch' :
            DecoderAlong code (revertPc + 1) (pre ++ [.op .REVERT]) := by
          rw [hrevertShape] at hdispatch
          simpa [hrevertPc, instrByteSize] using hdispatch
        have hepilogue := X_revert_of_pathSafe_runView validJumps initial hsafe
          code (revertPc + 1) pre entry final (dispatchRevertBytes cfg)
          hrEntry hentryCode hentryPc hdispatch' hpure hrun houtput
        refine ⟨final, ?_⟩
        rw [hrevertShape]
        simp only [List.length_append, List.length_singleton]
        calc
          EVM.X (pre.length + 1 + 4) validJumps st =
              EVM.X (pre.length + 4) validJumps pushed := by
                apply X_step_of_pathPrecheck validJumps initial hsafe
                  (pre.length + 4) st pushed (decodedPlainInstr (.push32 revertPc))
                  hreach hdecode₁
                · simpa [pushed] using
                    selectorPush32State_step revertPc (pre.length + 3) st
                · simpa using xHaltOutput_push32_none pushed
          _ = EVM.X (pre.length + 3) validJumps jumped := by
                apply X_step_of_pathPrecheck validJumps initial hsafe
                  (pre.length + 3) pushed jumped (.JUMP, none) hrPushed hdecode₂
                · simpa [jumped, jumpState, checkedState, hpushedStack] using
                    evmStep_jump (pre.length + 2) (checkedCost pushed .JUMP)
                      (checkedState pushed .JUMP) (.ofNat revertPc) []
                · simp [xHaltOutput]
          _ = EVM.X (pre.length + 2) validJumps entry := by
                apply X_step_of_pathPrecheck validJumps initial hsafe
                  (pre.length + 2) jumped entry (.JUMPDEST, none) hrJumped hdecode₃
                · simpa [entry] using
                    evmStep_jumpdest (pre.length + 1)
                      (checkedCost jumped .JUMPDEST) (checkedState jumped .JUMPDEST)
                · rfl
          _ = .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := hepilogue

private theorem resolvedRevertEntry_X
    (cfg : Config) (validJumps : Array Word) (initial : EVM.State)
    (hsafe : PathScopedXPrecheckSafe validJumps initial)
    (code : ByteArray) (revertPc : Nat) (st : EVM.State)
    (hreach : EVMPathReach initial st)
    (hdecoder : DecoderAlong code revertPc
      ([.op .JUMPDEST] ++ dispatchRevert cfg))
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat revertPc)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hwidth : ∀ selector,
      cfg.errors.errorSelector "InvalidSelector" = some selector →
        pushWidth (paddedSelector selector) ≤ 32) :
    ∃ final : EVM.State,
      EVM.X ((dispatchRevert cfg).length + 2) validJumps st =
        .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := by
  let entry := jumpdestState st
  obtain ⟨pre, final, hrevertShape, hpure, hrun, houtput⟩ :=
    dispatchRevert_runView cfg entry
      (by simp [entry, jumpdestState, checkedState, hstack])
      (by simp [entry, jumpdestState, checkedState, hmemory]) hwidth
  cases hdecoder with
  | cons _ _ _ hd hdispatch =>
    have hdecode :
        EVM.decode st.executionEnv.code st.pc = some (.JUMPDEST, none) := by
      simpa [hcode, hpc] using hd
    have hentryReach : EVMPathReach initial entry :=
      .step hreach hdecode (by simpa [entry] using jumpdestState_step st) (by rfl)
    have hframe := (hsafe st (.JUMPDEST, none) hreach hdecode).2 entry
      (by simpa [entry] using jumpdestState_step st)
    have hentryCode : entry.executionEnv.code = code := by
      rw [hframe.1, hcode]
    have hentryPc : entry.pc = .ofNat (revertPc + 1) := by
      rw [hframe.2, hpc]
      simp [decodedByteSize, word_ofNat_add]
    have hdispatch' :
        DecoderAlong code (revertPc + 1) (pre ++ [.op .REVERT]) := by
      rw [hrevertShape] at hdispatch
      simpa [instrByteSize] using hdispatch
    have hepilogue := X_revert_of_pathSafe_runView validJumps initial hsafe
      code (revertPc + 1) pre entry final (dispatchRevertBytes cfg)
      hentryReach hentryCode hentryPc hdispatch' hpure hrun houtput
    refine ⟨final, ?_⟩
    rw [hrevertShape]
    simp only [List.length_append, List.length_singleton]
    calc
      EVM.X (pre.length + 1 + 2) validJumps st =
          EVM.X (pre.length + 2) validJumps entry := by
            apply X_step_of_pathPrecheck validJumps initial hsafe
              (pre.length + 2) st entry (.JUMPDEST, none) hreach hdecode
            · simpa [entry] using
                evmStep_jumpdest (pre.length + 1) (checkedCost st .JUMPDEST)
                  (checkedState st .JUMPDEST)
            · rfl
      _ = .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := hepilogue

/-- Production short-calldata dispatch follows the initial size guard directly to the resolved
revert label and returns the generated empty/custom-error bytes. -/
theorem productionShortCalldata_X_reverts
    (cfg : Config) (contractDef : ContractDef)
    (instrs resolved : List Instr) (code : ByteArray)
    (pairs : List (Nat × Nat)) (revertPc : Nat)
    (validJumps : Array Word) (st : EVM.State)
    (hvalid : Checks.validateAll contractDef = .ok contractDef)
    (hcontract : Contract.contract cfg contractDef = .ok instrs)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64)
    (hshape :
      resolved =
        resolvedCalldataGuard revertPc ++
          resolvedSelectorBranches pairs ++
          [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
    (hrevertPc :
      revertPc =
        instrsByteSize
          (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs) + 34)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hshort : st.executionEnv.calldata.size < 4)
    (hrevertJump : (.ofNat revertPc : Word) ∈ validJumps)
    (hwidthError : ∀ selector,
      cfg.errors.errorSelector "InvalidSelector" = some selector →
        pushWidth (paddedSelector selector) ≤ 32) :
    ∃ final : EVM.State,
      EVM.X ((dispatchRevert cfg).length + 7) validJumps st =
        .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := by
  have _ := hvalid
  have _ := hcontract
  have _ := hrevertJump
  have hall := productionDecoderAlong instrs resolved code hencode hresolve
    hencodable hlimit
  have hfull :
      DecoderAlong code 0
        (resolvedCalldataGuard revertPc ++
          resolvedSelectorBranches pairs ++
          [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg) := by
    simpa [hshape, List.append_assoc] using hall
  have hguardDecoder :
      DecoderAlong code 0
        (resolvedCalldataGuard revertPc ++
          (resolvedSelectorBranches pairs ++
            [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)) := by
    simpa [List.append_assoc] using hfull
  let guardState := calldataGuardState revertPc st
  have hguardReach :=
    (resolvedCalldataGuard_X validJumps code revertPc 1
      (resolvedSelectorBranches pairs ++
        [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
      st hsafe hguardDecoder hcode hpc hstack (by decide)).2
  have hentryDecoder₀ := DecoderAlong.dropPrefix
    (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs ++
      [.push32 revertPc, .op .JUMP])
    ([.op .JUMPDEST] ++ dispatchRevert cfg)
    (by simpa [List.append_assoc] using hfull)
  have hentryDecoder :
      DecoderAlong code revertPc ([.op .JUMPDEST] ++ dispatchRevert cfg) := by
    have hprefix :
        ((resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs ++
          ([Instr.push32 revertPc, Instr.op .JUMP] : List Instr)).map
            (instrByteSize [])).sum =
          revertPc := by
      calc
        _ = instrsByteSize
              (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs) +
              34 := by
                simp [instrsByteSize, List.map_append, List.sum_append, instrByteSize]
                omega
        _ = revertPc := hrevertPc.symm
    rw [← hprefix]
    simpa using hentryDecoder₀
  obtain ⟨final, hentryX⟩ := resolvedRevertEntry_X cfg validJumps st hsafe code
    revertPc guardState hguardReach hentryDecoder
    (by simp [guardState, calldataGuardState_executionEnv, hcode])
    (calldataGuardState_pc_short revertPc st hpc hstack hshort)
    (calldataGuardState_stack revertPc st hstack)
    (by simp [guardState, calldataGuardState_memory, hmemory]) hwidthError
  refine ⟨final, ?_⟩
  have hguardX :=
    (resolvedCalldataGuard_X validJumps code revertPc
      ((dispatchRevert cfg).length + 2)
      (resolvedSelectorBranches pairs ++
        [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
      st hsafe hguardDecoder hcode hpc hstack (by omega)).1
  calc
    EVM.X ((dispatchRevert cfg).length + 7) validJumps st =
        EVM.X ((dispatchRevert cfg).length + 2) validJumps guardState := by
          simpa [guardState] using hguardX
    _ = .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := hentryX

/-- Production selector mismatch falls through every recursive branch, executes the resolved
revert jump, and returns the generated empty/custom-error bytes. -/
theorem productionSelectorMismatch_X_reverts
    (cfg : Config) (contractDef : ContractDef)
    (instrs resolved : List Instr) (code calldata : ByteArray)
    (pairs : List (Nat × Nat)) (revertPc : Nat)
    (validJumps : Array Word) (st : EVM.State)
    (hvalid : Checks.validateAll contractDef = .ok contractDef)
    (hcontract : Contract.contract cfg contractDef = .ok instrs)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64)
    (hshape :
      resolved =
        resolvedCalldataGuard revertPc ++
          resolvedSelectorBranches pairs ++
          [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
    (hrevertPc :
      revertPc =
        instrsByteSize
          (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs) + 34)
    (hpairs : ∀ pair ∈ pairs,
      ∃ fn ∈ dispatchedFunctions contractDef,
        pair.1 = (computeSelector fn).toNat)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hnotShort : ¬ calldata.size < 4)
    (hsizeLt : calldata.size < UInt256.size)
    (hmismatch : SelectorMismatch (dispatchedFunctions contractDef) calldata)
    (hwidthPairs : ∀ pair ∈ pairs, pushWidth pair.1 ≤ 32)
    (hrevertJump : (.ofNat revertPc : Word) ∈ validJumps)
    (hwidthError : ∀ selector,
      cfg.errors.errorSelector "InvalidSelector" = some selector →
        pushWidth (paddedSelector selector) ≤ 32) :
    ∃ final : EVM.State,
      EVM.X ((dispatchRevert cfg).length + 9 + 8 * pairs.length)
          validJumps st =
        .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := by
  have _ := hvalid
  have _ := hcontract
  have hall := productionDecoderAlong instrs resolved code hencode hresolve
    hencodable hlimit
  have hfull :
      DecoderAlong code 0
        (resolvedCalldataGuard revertPc ++
          resolvedSelectorBranches pairs ++
          [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg) := by
    simpa [hshape, List.append_assoc] using hall
  have hguardDecoder :
      DecoderAlong code 0
        (resolvedCalldataGuard revertPc ++
          (resolvedSelectorBranches pairs ++
            [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)) := by
    simpa [List.append_assoc] using hfull
  let guardState := calldataGuardState revertPc st
  have hguardReach :=
    (resolvedCalldataGuard_X validJumps code revertPc 1
      (resolvedSelectorBranches pairs ++
        [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
      st hsafe hguardDecoder hcode hpc hstack (by decide)).2
  have hbranchDecoder₀ := DecoderAlong.dropPrefix (resolvedCalldataGuard revertPc)
    (resolvedSelectorBranches pairs ++
      [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
    hguardDecoder
  have hbranchPc :
      guardState.pc =
        .ofNat (instrsByteSize (resolvedCalldataGuard revertPc)) := by
    apply calldataGuardState_pc_fallthrough revertPc st hpc hstack
    · simpa [hcalldata] using hnotShort
    · simpa [hcalldata] using hsizeLt
  have hselectorRoundtrip :
      (.ofNat (decodeSelector calldata).toNat : Word) = decodeSelector calldata := by
    generalize hw : decodeSelector calldata = word
    rcases word with ⟨value⟩
    apply word_eq_of_toNat_eq
    change (value.val : Nat) % UInt256.size = value.val
    exact Nat.mod_eq_of_lt value.isLt
  have hdistinct : ∀ pair ∈ pairs,
      (.ofNat pair.1 : Word) ≠ .ofNat (decodeSelector calldata).toNat := by
    intro pair hpair heq
    obtain ⟨fn, hfn, hpairSelector⟩ := hpairs pair hpair
    apply hmismatch fn hfn
    calc
      decodeSelector calldata =
          (.ofNat (decodeSelector calldata).toNat : Word) := hselectorRoundtrip.symm
      _ = .ofNat pair.1 := heq.symm
      _ = .ofNat (computeSelector fn).toNat := by rw [hpairSelector]
  obtain ⟨tailState, htailStack, htailPc, htailEnv, htailMemory, _,
      htailReach, hbranchesX⟩ :=
    resolvedSelectorBranches_X_miss validJumps st hsafe code pairs
      (decodeSelector calldata).toNat
      (instrsByteSize (resolvedCalldataGuard revertPc))
      ((dispatchRevert cfg).length + 4)
      ([.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
      guardState hguardReach (by simpa using hbranchDecoder₀)
      (by simp [guardState, calldataGuardState_executionEnv, hcode])
      hbranchPc (calldataGuardState_stack revertPc st hstack)
      (by rw [calldataGuardState_executionEnv, hcalldata, hselectorRoundtrip])
      hwidthPairs hdistinct (by omega)
  have htailDecoder₀ := DecoderAlong.dropPrefix
    (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs)
    ([.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
    (by simpa [List.append_assoc] using hfull)
  have htailDecoder :
      DecoderAlong code
        (instrsByteSize
          (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs))
        ([.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg) := by
    simpa [instrsByteSize] using htailDecoder₀
  obtain ⟨final, htailX⟩ := resolvedRevertTail_X cfg validJumps st hsafe code
    (instrsByteSize
      (resolvedCalldataGuard revertPc ++ resolvedSelectorBranches pairs))
    revertPc tailState htailReach htailDecoder
    (by rw [htailEnv, calldataGuardState_executionEnv, hcode])
    (by
      simpa [instrsByteSize, List.map_append, List.sum_append] using htailPc)
    htailStack
    (by rw [htailMemory, calldataGuardState_memory, hmemory])
    hrevertPc hrevertJump hwidthError
  refine ⟨final, ?_⟩
  have hguardX :=
    (resolvedCalldataGuard_X validJumps code revertPc
      ((dispatchRevert cfg).length + 4 + 8 * pairs.length)
      (resolvedSelectorBranches pairs ++
        [.push32 revertPc, .op .JUMP, .op .JUMPDEST] ++ dispatchRevert cfg)
      st hsafe hguardDecoder hcode hpc hstack (by omega)).1
  calc
    EVM.X ((dispatchRevert cfg).length + 9 + 8 * pairs.length)
        validJumps st =
        EVM.X (((dispatchRevert cfg).length + 4 + 8 * pairs.length) + 5)
          validJumps st := by
            congr 1
            omega
    _ =
        EVM.X ((dispatchRevert cfg).length + 4 + 8 * pairs.length)
          validJumps guardState := by
            simpa [guardState] using hguardX
    _ = EVM.X ((dispatchRevert cfg).length + 4) validJumps tailState := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbranchesX
    _ = .ok (.revert final.gasAvailable (dispatchRevertBytes cfg)) := htailX

/-- Generic production matching-selector execution.  Dispatcher and body intermediate states,
including `XReady`, are constructed internally. -/
theorem productionMatchingSelector_X_returns
    {abiSelector : Nat} {args : List Word} {calldata : ByteArray}
    {program : IR.Stmt} {value : Word}
    (instrs resolved preBody body afterBody suffix : List Instr) (code : ByteArray)
    (before after : List (Nat × Nat)) (targetPc revertPc : Nat)
    (selectedLabel : String) (validJumps : Array Word) (st : EVM.State)
    (inputCtx bodyOut : Ctx)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved)
    (hencodable : EncodablePlainInstrs resolved)
    (hlimit : code.size + 33 < 2 ^ 64)
    (hdispatchShape :
      resolved =
        resolvedCalldataGuard revertPc ++
          (resolvedSelectorBranches
            (before ++ (abiSelector, targetPc) :: after) ++ suffix))
    (hbodyShape :
      resolved = preBody ++ [.op .JUMPDEST] ++ body ++ afterBody)
    (htargetPc : targetPc = (preBody.map (instrByteSize [])).sum)
    (hlabel :
      lookupLabel (fixpointLabels instrs) selectedLabel = .ok targetPc)
    (hsafe : PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code) (hpc : st.pc = .ofNat 0)
    (hstack : st.stack = []) (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hwf : WellFormed abiSelector args calldata)
    (hwidthSelected : pushWidth abiSelector ≤ 32)
    (hwidthBefore : ∀ pair ∈ before, pushWidth pair.1 ≤ 32)
    (hdistinct : ∀ pair ∈ before,
      (.ofNat pair.1 : Word) ≠ .ofNat abiSelector)
    (htargetJump : (.ofNat targetPc : Word) ∈ validJumps)
    (hgen :
      Codegen.stmt (Ctx.forFunction inputCtx selectedLabel) program =
        .ok (body, bodyOut))
    (hprogram :
      ViewProgram (machineWordState st) program value)
    (hreloadSafe :
      ViewProgramReloadSafe (Ctx.forFunction inputCtx selectedLabel)
        (machineWordState st) program) :
    ∃ final,
      EVM.X (body.length + 2 + 8 * (before.length + 1) + 5)
          validJumps st =
        .ok (.success final value.toByteArray) ∧
      ∀ i (hi : i < args.length),
        (machineWordState st).calldata (4 + 32 * i) = args[i] := by
  have hall : DecoderAlong code 0 resolved :=
    productionDecoderAlong instrs resolved code hencode hresolve hencodable hlimit
  have hbodyGrouped :
      DecoderAlong code 0 (preBody ++ [.op .JUMPDEST] ++ body ++ afterBody) := by
    simpa [hbodyShape] using hall
  have hfromTarget :=
    DecoderAlong.dropPrefix preBody ([.op .JUMPDEST] ++ body ++ afterBody)
      (by simpa [List.append_assoc] using hbodyGrouped)
  have hfromTarget' :
      DecoderAlong code targetPc ([.op .JUMPDEST] ++ body ++ afterBody) := by
    simpa [htargetPc] using hfromTarget
  have hbodyAndAfter :=
    DecoderAlong.dropPrefix [.op .JUMPDEST] (body ++ afterBody) hfromTarget'
  have hbodyDecoder :
      DecoderAlong code (targetPc + 1) body := by
    simpa [instrByteSize] using
      DecoderAlong.takePrefix body afterBody hbodyAndAfter
  obtain ⟨bodyState, _, hbodyStack, hbodyMemory, hbodyEnv, hbodyToState,
      hbodyPc, hbodyReach, hdispatchX⟩ :=
    productionGuardSelector_X_reaches instrs resolved suffix code before after targetPc
      revertPc (body.length + 2) selectedLabel validJumps st hencode hresolve
      hencodable hlimit hdispatchShape hlabel hsafe hcode hpc hstack hmemory
      hcalldata hwf hwidthSelected hwidthBefore hdistinct (by omega)
  let entry := jumpdestState bodyState
  have hjumpDecode :
      EVM.decode bodyState.executionEnv.code bodyState.pc =
        some (.JUMPDEST, none) := by
    simpa [hbodyEnv, hcode, hbodyPc] using
      (show EVM.decode code (.ofNat targetPc) =
          some (decodedPlainInstr (.op .JUMPDEST)) from
        (by
          cases hfromTarget' with
          | cons _ _ _ hdecoded _ => exact hdecoded))
  have hjumpSafe := hsafe bodyState (.JUMPDEST, none) hbodyReach hjumpDecode
  have hentryReach : EVMPathReach st entry :=
    .step hbodyReach hjumpDecode (by simpa [entry] using jumpdestState_step bodyState)
      (by rfl)
  have hentryFrame := hjumpSafe.2 entry
    (by simpa [entry] using jumpdestState_step bodyState)
  have hentryCode : entry.executionEnv.code = code := by
    rw [hentryFrame.1, hbodyEnv, hcode]
  have hentryPc : entry.pc = .ofNat (targetPc + 1) := by
    rw [hentryFrame.2, hbodyPc]
    simp [decodedByteSize, word_ofNat_add]
  have hentryStack : entry.stack = [] := by
    simp [entry, jumpdestState, checkedState, hbodyStack]
  have hentryMemory : entry.memory = ByteArray.empty := by
    simp [entry, jumpdestState, checkedState, hbodyMemory]
  have hentryToState : entry.toState = st.toState := by
    simp [entry, jumpdestState, checkedState, hbodyToState]
  have hentryWord : machineWordState entry = machineWordState st := by
    simp only [machineWordState]
    rw [hentryToState]
  have hctx :
      ContextAgrees (Ctx.forFunction inputCtx selectedLabel) entry
        (machineWordState entry) := by
    have hbase := contextAgrees_machineWordState entry hentryStack
    constructor
    · simp [Ctx.forFunction, hentryStack]
    · intro name binding hlookup
      simp [Ctx.forFunction, Ctx.lookupBinding] at hlookup
    · intro name binding source hlookup
      simp [Ctx.forFunction, Ctx.lookupBinding] at hlookup
    · intro name binding source hlookup
      simp [Ctx.forFunction, Ctx.lookupBinding] at hlookup
    · exact hbase.sources
  have hprogramEntry :
      ViewProgram (machineWordState entry) program value := by
    simpa [hentryWord] using hprogram
  have hreloadSafeEntry :
      ViewProgramReloadSafe (Ctx.forFunction inputCtx selectedLabel)
        (machineWordState entry) program := by
    simpa [hentryWord] using hreloadSafe
  obtain ⟨final, hrun, hreturn, _⟩ :=
    codegenViewProgram_runView_correct hprogramEntry
      (Ctx.forFunction inputCtx selectedLabel) hreloadSafeEntry entry hctx hentryMemory
      body bodyOut hgen
  obtain ⟨pre, hbodyGenerated, hpure⟩ :=
    codegenViewProgram_pure hprogramEntry
      (Ctx.forFunction inputCtx selectedLabel) hreloadSafeEntry entry hctx
      body bodyOut hgen
  have hready : XReady validJumps code (targetPc + 1) body entry := by
    rw [hbodyGenerated] at hbodyDecoder hrun ⊢
    exact XReady_of_pathSafe_runView validJumps st hsafe code (targetPc + 1)
      pre entry final hentryReach hentryCode hentryPc hbodyDecoder hpure hrun
  obtain ⟨bodyFinal, hbodyX⟩ :=
    codegenViewProgram_X_returns hprogramEntry
      (Ctx.forFunction inputCtx selectedLabel) hreloadSafeEntry entry hctx hentryMemory
      body bodyOut hgen code (targetPc + 1) hbodyDecoder validJumps hready
  refine ⟨bodyFinal, ?_, ?_⟩
  · calc
      EVM.X (body.length + 2 + 8 * (before.length + 1) + 5) validJumps st =
          EVM.X (body.length + 2) validJumps bodyState := by
            simpa [Nat.add_assoc] using hdispatchX
      _ = EVM.X (body.length + 1) validJumps entry := by
            apply X_step_of_pathPrecheck validJumps st hsafe
              (body.length + 1) bodyState entry (.JUMPDEST, none)
              hbodyReach hjumpDecode
            · simpa using
                (evmStep_jumpdest body.length (checkedCost bodyState .JUMPDEST)
                  (checkedState bodyState .JUMPDEST))
            · rfl
      _ = .ok (.success bodyFinal value.toByteArray) := hbodyX
  · exact fun i hi => machineWordState_argument hwf st hcalldata i hi

end Lsc.Compile.Bytecode.AbiDispatch
