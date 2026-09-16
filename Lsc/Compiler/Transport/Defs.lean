import Lsc.Compiler.EndToEndExt
import Lsc.Compiler.ExtOracleTheorems
import Lsc.Security.Wealth
import Lsc.Security.WealthTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Transport structures, ABI decode/encode, and `CallsWF`.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

/-- Typed ABI codec: `FnDef` ↔ `C.Fn`, words ↔ `C.Args`. -/
structure TransportCodec {S X E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S X E ε) (C : Spec S X E ε) where
  fnDef : C.Fn → FnDef
  encode : (fn : C.Fn) → C.Args fn → List Nat
  decodeFn : FnDef → Option C.Fn
  decode : (fn : C.Fn) → List Nat → C.Args fn
  mem : ∀ fn, fnDef fn ∈ c.functions
  encode_length : ∀ fn args, (encode fn args).length = (fnDef fn).params.length
  decodeFn_fnDef : ∀ fn, decodeFn (fnDef fn) = some fn
  decodeFn_of_mem :
    ∀ f, f ∈ c.functions → ∃ fn, decodeFn f = some fn ∧ f = fnDef fn
  encode_decode :
    ∀ fn ns, ns.length = (fnDef fn).params.length → encode fn (decode fn ns) = ns
  decode_encode : ∀ fn args, decode fn (encode fn args) = args
  core_exec :
    ∀ fn args ctx w,
      worldAfter (Core.denote Γ (fnDef fn).core (encode fn args).reverse) ctx w =
      worldAfter (C.exec fn args) ctx w
  /-- Language `Spec.payable` agrees with the compiled `FnDef` flag. -/
  payable_eq : ∀ fn, C.payable fn = (fnDef fn).payable

/-- Contract-parametric compile + codec hypotheses. Call-free vs S2 is extra. -/
structure TransportSetup (S X E ε : Type) where
  c : ContractDef
  Γ : ContractSchema S X E ε
  spec : Spec S X E ε
  codec : TransportCodec c Γ spec
  lawful : Γ.st.Lawful c.fields
  hκ : KeccakSep c evmKeccak
  hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor
  hlen : c.fields.length < wordBound
  hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound
  rt : YBlock
  hrt : runtimeBlock c = some rt
  is : List Instr
  hcomp : compileBlock rt = some is

/-- S2 package: the memory-blind CALL oracle and the call-carrying fragment.
There is no per-interface `BindEnv` / `RX` layer; `Oracle.ofExt` is the
only Core bridge. `NoReentry` is a lemma about `toCall`, not a field. -/
structure TransportBindings (S E ε : Type)
    (T : TransportSetup S ExtState E ε) where
  oracle : ExtOracle
  hCalls : CallsRealized (toCalls oracle)
  hS2 : ∀ f ∈ T.c.functions, S2Frag f.core

abbrev TransportBindings.extCalls {S E ε : Type}
    {T : TransportSetup S ExtState E ε} (X : TransportBindings S E ε T) :
    ExternalCalls :=
  toCalls X.oracle

theorem TransportBindings.htot {S E ε : Type}
    {T : TransportSetup S ExtState E ε} (X : TransportBindings S E ε T) :
    CallsTotal X.extCalls :=
  toCalls_total X.oracle

/-- Start a call from the same skeleton `EvmTraceRunExtAll` uses: executing
storage `σ`, foreign persistent storage `ξ`, and `Oracle.ofExt`. Callee-visible
agreement with that skeleton is then definitional. -/
def reframeExt {S E : Type} (o : ExtOracle) (w : World S ExtState E)
    (cd : List UInt8) (σ : U256 → U256) (ξ : Foreign) (ctx : Ctx) :
    World S ExtState E :=
  { w with
    ext := ExtView.ofState (mkEvmStateExt cd σ ξ evmKeccak ctx)
    oracle := Oracle.ofExt o }

@[simp] theorem reframeExt_self {S E : Type} (o : ExtOracle)
    (w : World S ExtState E) (cd σ ξ ctx) :
    (reframeExt o w cd σ ξ ctx).self = w.self := rfl

@[simp] theorem reframeExt_log {S E : Type} (o : ExtOracle)
    (w : World S ExtState E) (cd σ ξ ctx) :
    (reframeExt o w cd σ ξ ctx).log = w.log := rfl

@[simp] theorem reframeExt_oracle {S E : Type} (o : ExtOracle)
    (w : World S ExtState E) (cd σ ξ ctx) :
    (reframeExt o w cd σ ξ ctx).oracle = Oracle.ofExt o := rfl

theorem ExtAgree_reframeExt {S E : Type} (o : ExtOracle)
    (w : World S ExtState E) (cd σ ξ ctx) :
    ExtAgree ctx.self (reframeExt o w cd σ ξ ctx).ext
      (mkEvmStateExt cd σ ξ evmKeccak ctx) := by
  unfold ExtAgree agreeExceptSelf reframeExt ExtView.ofState
  rfl

/-- `Inv` survives the `mkEvmStateExt` reframe that `EvmTraceRunExtAll`
already does between calls. Replaces the old `hInvF` (fault-bit
irrelevance). If `Inv` depends only on `self`, this is immediate. -/
def InvReframe {S E : Type} (Inv : World S ExtState E → Prop)
    (o : ExtOracle) : Prop :=
  ∀ (w : World S ExtState E) (cd : List UInt8) (σ : U256 → U256)
    (ξ : Foreign) (ctx : Ctx),
    Inv w → Inv (reframeExt o w cd σ ξ ctx)

variable {S X E ε : Type}

theorem TransportSetup.nodup (T : TransportSetup S X E ε) :
    selectorsNodup T.c = true := (runtimeBlock_inv T.hrt).1

/-- `none` = dispatcher reject (EVM revert, no state change). -/
def decodeCall (T : TransportSetup S X E ε) (ctx : Ctx) (cd : List UInt8) :
    Option (Call T.spec) :=
  match dispatchedFn T.c cd ctx.value with
  | none => none
  | some f =>
    match T.codec.decodeFn f with
    | none => none
    | some fn => some (Call.ofCtx ctx fn (T.codec.decode fn (decodeArgs f cd)))

theorem decodeCall_ctx (T : TransportSetup S X E ε) {ctx : Ctx} {cd : List UInt8}
    {c : Call T.spec} (h : decodeCall T ctx cd = some c) :
    c.target = ctx.self ∧ c.sender = ctx.sender := by
  unfold decodeCall at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h
      subst h
      exact ⟨rfl, rfl⟩

def decodeTrace (T : TransportSetup S X E ε) : List EvmCall → List (Step T.spec)
  | [] => []
  | call :: rest =>
    match decodeCall T call.ctx call.calldata with
    | none => decodeTrace T rest
    | some c => .call c :: decodeTrace T rest

def encodeCall (T : TransportSetup S X E ε) (c : Call T.spec) : EvmCall :=
  ⟨c.toCtx, fnCalldata (T.codec.fnDef c.fn) (T.codec.encode c.fn c.args)⟩

def encodeCalls (T : TransportSetup S X E ε) : List (Step T.spec) → List EvmCall
  | [] => []
  | .call c :: tr => encodeCall T c :: encodeCalls T tr
  | .env _ :: tr => encodeCalls T tr

/-- Per-call well-formedness: `ctx.self = self`, `sender ≠ self`, `CtxWF`,
bounded calldata. -/
def CallsWF (T : TransportSetup S X E ε) (self : Address) (calls : List EvmCall) :
    Prop :=
  ∀ call ∈ calls,
    call.ctx.self = self ∧ call.ctx.sender ≠ self ∧
    CtxWF call.ctx ∧ call.calldata.length < wordBound

def EncodeBounded (T : TransportSetup S X E ε) : List (Step T.spec) → Prop
  | [] => True
  | .call c :: tr =>
    CtxWF c.toCtx ∧ (∀ n ∈ T.codec.encode c.fn c.args, n < wordBound) ∧
      valueOk (T.codec.fnDef c.fn) c.toCtx.value ∧
      EncodeBounded T tr
  | .env _ :: tr => EncodeBounded T tr

/-- `EncodeBounded` plus the codec payable table imply every encoded call has
value 0 (transport is the non-payable fragment). -/
theorem encodeBounded_value_zero (T : TransportSetup S X E ε)
    {tr : List (Step T.spec)} (hb : EncodeBounded T tr)
    {c : Call T.spec} (hc : Step.call c ∈ tr) : c.value = 0 := by
  induction tr with
  | nil => cases hc
  | cons s rest ih =>
    match s with
    | .env _ =>
      exact ih hb (by simpa using hc)
    | .call c' =>
      rcases hb with ⟨_, _, hvo, htlB⟩
      simp only [List.mem_cons] at hc
      rcases hc with hhere | htl
      · cases hhere
        have hpF : (T.codec.fnDef c.fn).payable = false := by
          rw [← T.codec.payable_eq]
          rfl
        simp [valueOk, hpF, Call.toCtx] at hvo
        exact of_decide_eq_true hvo
      · exact ih htlB htl

def callsOf {C : Spec S X E ε} : List (Step C) → List (Step C)
  | [] => []
  | .call c :: tr => .call c :: callsOf tr
  | .env _ :: tr => callsOf tr

theorem core_exec_cd (T : TransportSetup S X E ε) {f : FnDef} {fn : T.spec.Fn}
    (heq : f = T.codec.fnDef fn) (ctx : Ctx) (w : World S X E) (cd : List UInt8) :
    worldAfter (Core.denote T.Γ f.core (decodeArgs f cd).reverse) ctx w =
    worldAfter (T.spec.exec fn (T.codec.decode fn (decodeArgs f cd))) ctx w := by
  subst heq
  set ns := decodeArgs (T.codec.fnDef fn) cd
  have hlen : ns.length = (T.codec.fnDef fn).params.length := decodeArgs_length _ _
  have hgoal := T.codec.core_exec fn (T.codec.decode fn ns) ctx w
  rw [T.codec.encode_decode fn ns hlen] at hgoal
  exact hgoal

theorem wf_decodeTrace [HasCreditValue X] {T : TransportSetup S X E ε}
    [HasPayable T.spec] [HasSelfBalance X]
    (self : Address)
    (calls : List EvmCall) (w : World S X E) (h : CallsWF T self calls)
    (hlt : ∀ (w : World S X E), HasSelfBalance.get w.ext < wordBound)
    (hnp : ∀ fn, T.spec.payable fn = false := by intro fn; cases fn <;> rfl) :
    Wf self (decodeTrace T calls) w := by
  induction calls generalizing w with
  | nil => trivial
  | cons call rest ih =>
    have ⟨ht, hs, _, _⟩ := h call (List.mem_cons.mpr (Or.inl rfl))
    have hrest : CallsWF T self rest := fun c hc =>
      h c (List.mem_cons_of_mem _ hc)
    cases hsel : dispatchedFn T.c call.calldata call.ctx.value with
    | none =>
      simp [decodeTrace, decodeCall, hsel]
      exact ih (w := w) hrest
    | some f =>
      obtain ⟨fn, hfn, heq⟩ := T.codec.decodeFn_of_mem f (dispatchedFn_mem hsel)
      have hv : call.ctx.value = 0 := by
        have hvoF := dispatchedFn_valueOk hsel
        subst heq
        have hpF : (T.codec.fnDef fn).payable = false := by
          rw [← T.codec.payable_eq]
          rfl
        simp [valueOk, hpF] at hvoF
        exact hvoF
      have hb : HasSelfBalance.get w.ext +
          (Call.ofCtx call.ctx fn (T.codec.decode fn (decodeArgs f call.calldata))).value <
            wordBound := by
        simp [Call.ofCtx, hv, hlt w]
      simp [decodeTrace, decodeCall, hsel, hfn, Call.ofCtx]
      refine ⟨ht, hs, hb, ?_⟩
      exact ih (w := step (.call (Call.ofCtx call.ctx fn
          (T.codec.decode fn (decodeArgs f call.calldata)))) w) hrest

/-- S1 only: post-`.self` ignores `log` (Token `exec` does not read `log`).
Call-free contracts have no payable function, so `creditValue w 0 = w`. -/
theorem post_congr_run [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    (hpc : ∀ (fn : C.Fn) (args : C.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (C.exec fn args) ctx w).self =
          (worldAfter (C.exec fn args) ctx w').self ∧
        (worldAfter (C.exec fn args) ctx w).ext =
          (worldAfter (C.exec fn args) ctx w').ext)
    (tr : List (Step C)) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    (run tr w).self = (run tr w').self := by
  induction tr generalizing w w' with
  | nil => simpa [run] using hs
  | cons s rest ih =>
    match s with
    | .env x =>
      simpa [run, step] using
        ih (w := { w with ext := x }) (w' := { w' with ext := x }) hs rfl
    | .call c =>
      have hp : C.payable c.fn = false := hnp c.fn
      rw [run_cons, run_cons]
      by_cases hv : c.value = 0
      · rw [step_eq_worldAfter_of_not_payable c w hp hv,
          step_eq_worldAfter_of_not_payable c w' hp hv]
        obtain ⟨hs1, he1⟩ := hpc c.fn c.args c.toCtx w w' hs he
        exact ih _ _ hs1 he1
      · rw [step_reject_value (c := c) (w := w) hp hv,
          step_reject_value (c := c) (w := w') hp hv]
        exact ih w w' hs he

theorem step_ofCtx [HasCreditValue X] (T : TransportSetup S X E ε)
    [HasPayable T.spec]
    (ctx : Ctx)
    (fn : T.spec.Fn)
    (args : T.spec.Args fn) (w : World S X E)
    (hvo : T.spec.valueOk fn ctx.value = true) :
    step (.call (Call.ofCtx ctx fn args)) w =
      match T.spec.exec fn args ctx (World.creditValue w ctx.value) with
      | .ok (_, w') => w'
      | .error _ => w := by
  simp only [step, stepCall]
  rw [Call.toCtx_ofCtx]
  dsimp only [Call.ofCtx]
  refine (if_pos hvo).trans ?_
  cases hrun : T.spec.exec fn args ctx (World.creditValue w ctx.value) <;> rfl

theorem valueOk_spec_fnDef (T : TransportSetup S X E ε) (fn : T.spec.Fn)
    (v : Nat) : T.spec.valueOk fn v = valueOk (T.codec.fnDef fn) v := by
  simp [Spec.valueOk, valueOk, T.codec.payable_eq]

theorem encodeCall_decode (T : TransportSetup S X E ε) (c : Call T.spec)
    (hW : ∀ n ∈ T.codec.encode c.fn c.args, n < wordBound)
    (hvo : valueOk (T.codec.fnDef c.fn) c.toCtx.value) :
    decodeCall T c.toCtx (encodeCall T c).calldata = some c := by
  have hf := T.codec.mem c.fn
  have hk := T.hctor _ hf
  have hlenA := T.codec.encode_length c.fn c.args
  have hsel := dispatchedFn_fnCalldata T.c (T.codec.fnDef c.fn)
    (T.codec.encode c.fn c.args) c.toCtx.value hf T.nodup hlenA hvo
  have hdec := decodeArgs_fnCalldata (T.codec.fnDef c.fn)
    (T.codec.encode c.fn c.args) hk hlenA hW
  have hfn := T.codec.decodeFn_fnDef c.fn
  simp [decodeCall, encodeCall, hsel, hfn, hdec, T.codec.decode_encode,
    Call.ofCtx_toCtx]

theorem decodeTrace_encodeCalls (T : TransportSetup S X E ε)
    (tr : List (Step T.spec)) (hb : EncodeBounded T tr) :
    decodeTrace T (encodeCalls T tr) = callsOf tr := by
  induction tr with
  | nil => rfl
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls, callsOf] using ih (by simpa [EncodeBounded] using hb)
    | .call c =>
      rcases hb with ⟨_, hWargs, hvo, htlB⟩
      have hdec := encodeCall_decode T c hWargs hvo
      simp [encodeCall] at hdec
      simp [decodeTrace, encodeCalls, encodeCall, hdec, callsOf]
      exact ih htlB

theorem CallsWF.tail {T : TransportSetup S X E ε} {self call rest}
    (h : CallsWF T self (call :: rest)) : CallsWF T self rest :=
  fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem CallsWF.head {T : TransportSetup S X E ε} {self call rest}
    (h : CallsWF T self (call :: rest)) :
    call.ctx.self = self ∧ call.ctx.sender ≠ self ∧
    CtxWF call.ctx ∧ call.calldata.length < wordBound :=
  h call (List.mem_cons.mpr (Or.inl rfl))

theorem encodeCalls_WF [HasCreditValue X] [HasSelfBalance X]
    (T : TransportSetup S X E ε) [HasPayable T.spec]
    (self : Address)
    (tr : List (Step T.spec)) (w : World S X E)
    (hW : Wf self tr w) (hb : EncodeBounded T tr) :
    CallsWF T self (encodeCalls T tr) := by
  induction tr generalizing w with
  | nil => intro call h; cases h
  | cons s rest ih =>
    match s with
    | .env x' =>
      exact ih (w := { w with ext := x' }) hW
        (by simpa [EncodeBounded] using hb)
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, hvo, htlB⟩
      rcases hW with ⟨htgt, hne, _, hWtl⟩
      intro call hmem
      simp [encodeCalls] at hmem
      rcases hmem with hhere | htl
      · subst hhere
        refine ⟨?_, ?_, hctxWF, ?_⟩
        · simpa [encodeCall, Call.toCtx] using htgt
        · simpa [encodeCall, Call.toCtx] using hne
        · have hf := T.codec.mem c.fn
          have hlenA := T.codec.encode_length c.fn c.args
          simp [encodeCall]
          rw [length_fnCalldata, hlenA]
          exact T.hbound _ hf
      · exact ih (w := step (.call c) w) hWtl htlB call htl

theorem wf_callsOf [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    [HasSelfBalance X]
    (self : Address) (tr : List (Step C)) (w : World S X E)
    (h : Wf self tr w)
    (henv : ∀ s ∈ tr, ∃ c, s = Step.call c) :
    Wf self (callsOf tr) w := by
  induction tr generalizing w with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env _ =>
      obtain ⟨c, hne⟩ := henv _ (List.mem_cons_self)
      cases hne
    | .call c =>
      rcases h with ⟨ht, hs, hb, htl⟩
      exact ⟨ht, hs, hb,
        ih (w := step (.call c) w) htl
          (fun t ht => henv t (List.mem_cons_of_mem _ ht))⟩

theorem relyAlong_calls {C : Spec S X E ε} {rely : X → X → Prop}
    (tr : List (Step C)) (w : World S X E)
    (h : ∀ s ∈ tr, ∃ c, s = Step.call c) : RelyAlong rely tr w := by
  induction tr generalizing w with
  | nil => trivial
  | cons s rest ih =>
    obtain ⟨c, rfl⟩ := h s (List.mem_cons.mpr (Or.inl rfl))
    exact ih (w := step (.call c) w)
      (fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem decodeTrace_are_calls (T : TransportSetup S X E ε) (calls : List EvmCall) :
    ∀ s ∈ decodeTrace T calls, ∃ c, s = Step.call c := by
  induction calls with
  | nil => intro s h; cases h
  | cons call rest ih =>
    intro s hs
    cases hdec : decodeCall T call.ctx call.calldata with
    | none =>
      simp [decodeTrace, hdec] at hs
      exact ih s hs
    | some c =>
      simp [decodeTrace, hdec] at hs
      rcases hs with rfl | htl
      · exact ⟨c, rfl⟩
      · exact ih s htl

theorem callsOf_are_calls {C : Spec S X E ε} (tr : List (Step C)) :
    ∀ s ∈ callsOf tr, ∃ c, s = Step.call c := by
  induction tr with
  | nil => intro s h; cases h
  | cons s rest ih =>
    match s with
    | .env _ => exact ih
    | .call c =>
      intro s hs
      simp [callsOf] at hs
      rcases hs with rfl | htl
      · exact ⟨c, rfl⟩
      · exact ih s htl

def dummyCtx (self : Address) : Ctx where
  sender := 0
  self := self

end Lsc.Compiler
