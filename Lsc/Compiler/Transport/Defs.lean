import Lsc.Compiler.EndToEndExt
import Lsc.Compiler.ExtOracle
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

/-- S2 binding family. One-binding contracts instantiate `bs := [⟨α, bind⟩]`.
The CALL oracle is memory-blind by construction (`ExtOracle`): other
contracts cannot see this contract's private memory, which is true of
the EVM. -/
structure TransportBindings (S X E ε : Type) (I : Interface)
    (T : TransportSetup S X E ε) where
  bs : List (BindEnv I S X)
  oracle : ExtOracle
  hCalls : CallsRealized (toCalls oracle)
  hS2 : ∀ f ∈ T.c.functions, S2Frag f.core
  hign : BindEnvs.ignoresLocal bs
  hF : BindEnvs.ofState_foreign bs
  hsame : BindEnvs.sameAbs bs
  horth : BindEnvs.orthogonal bs
  hBind : BindEnvs.lookupWF T.c T.Γ bs
  hslot : ∀ f ∈ T.c.functions, BindEnvs.avoids T.Γ T.c bs f.core
  bindAddr_stable :
    ∀ e ∈ bs, ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w : World S X E),
      e.bind.addr (worldAfter (T.spec.exec fn args) ctx w).self = e.bind.addr w.self

abbrev TransportBindings.extCalls {S X E ε : Type} {I : Interface}
    {T : TransportSetup S X E ε} (X : TransportBindings S X E ε I T) :
    ExternalCalls :=
  toCalls X.oracle

theorem TransportBindings.htot {S X E ε : Type} {I : Interface}
    {T : TransportSetup S X E ε} (X : TransportBindings S X E ε I T) :
    CallsTotal X.extCalls :=
  toCalls_total X.oracle

variable {S X E ε : Type}

theorem TransportSetup.nodup (T : TransportSetup S X E ε) :
    selectorsNodup T.c = true := (runtimeBlock_inv T.hrt).1

/-- `none` = dispatcher reject (EVM revert, no state change). -/
def decodeCall (T : TransportSetup S X E ε) (ctx : Ctx) (cd : List UInt8) :
    Option (Call T.spec) :=
  match selectedFn T.c cd with
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
      EncodeBounded T tr
  | .env _ :: tr => EncodeBounded T tr

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

theorem wf_decodeTrace (T : TransportSetup S X E ε) (self : Address)
    (calls : List EvmCall) (h : CallsWF T self calls) :
    Wf self (decodeTrace T calls) := by
  induction calls with
  | nil => trivial
  | cons call rest ih =>
    have ⟨ht, hs, _, _⟩ := h call (List.mem_cons.mpr (Or.inl rfl))
    have hrest : CallsWF T self rest := fun c hc =>
      h c (List.mem_cons_of_mem _ hc)
    cases hsel : selectedFn T.c call.calldata with
    | none =>
      simp [decodeTrace, decodeCall, hsel]
      exact ih hrest
    | some f =>
      obtain ⟨fn, hfn, _⟩ := T.codec.decodeFn_of_mem f (selectedFn_mem hsel)
      simp [decodeTrace, decodeCall, hsel, hfn, Call.ofCtx]
      exact ⟨ht, hs, ih hrest⟩

/-- S1 only: post-`.self` ignores `log` (Token `exec` does not read `log`). -/
theorem post_congr_run {C : Spec S X E ε}
    (hpc : ∀ (fn : C.Fn) (args : C.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (C.exec fn args) ctx w).self =
          (worldAfter (C.exec fn args) ctx w').self ∧
        (worldAfter (C.exec fn args) ctx w).ext =
          (worldAfter (C.exec fn args) ctx w').ext)
    (tr : List (Step C)) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    (run tr w).self = (run tr w').self := by
  induction tr generalizing w w' with
  | nil => simpa [run] using hs
  | cons s rest ih =>
    match s with
    | .env x =>
      simpa [run, step] using
        ih (w := { w with ext := x }) (w' := { w' with ext := x }) hs rfl
    | .call c =>
      obtain ⟨hs1, he1⟩ := hpc c.fn c.args c.toCtx w w' hs he
      simpa [run, step] using ih (step (.call c) w) (step (.call c) w') hs1 he1

theorem step_ofCtx (T : TransportSetup S X E ε) (ctx : Ctx) (fn : T.spec.Fn)
    (args : T.spec.Args fn) (w : World S X E) :
    step (.call (Call.ofCtx ctx fn args)) w =
      worldAfter (T.spec.exec fn args) ctx w := rfl

theorem encodeCall_decode (T : TransportSetup S X E ε) (c : Call T.spec)
    (hW : ∀ n ∈ T.codec.encode c.fn c.args, n < wordBound) :
    decodeCall T c.toCtx (encodeCall T c).calldata = some c := by
  have hf := T.codec.mem c.fn
  have hk := T.hctor _ hf
  have hlenA := T.codec.encode_length c.fn c.args
  have hsel := selectedFn_fnCalldata T.c (T.codec.fnDef c.fn)
    (T.codec.encode c.fn c.args) hf T.nodup hlenA
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
      rcases hb with ⟨_, hWargs, htlB⟩
      have hdec := encodeCall_decode T c hWargs
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

theorem encodeCalls_WF (T : TransportSetup S X E ε) (self : Address)
    (tr : List (Step T.spec)) (hW : Wf self tr) (hb : EncodeBounded T tr) :
    CallsWF T self (encodeCalls T tr) := by
  induction tr with
  | nil => intro call h; cases h
  | cons s rest ih =>
    match s with
    | .env _ =>
      exact ih hW (by simpa [EncodeBounded] using hb)
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
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
      · exact ih hWtl htlB call htl

theorem wf_callsOf {C : Spec S X E ε} (self : Address) (tr : List (Step C))
    (h : Wf self tr) : Wf self (callsOf tr) := by
  induction tr with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env _ => exact ih h
    | .call c =>
      rcases h with ⟨ht, hs, htl⟩
      exact ⟨ht, hs, ih htl⟩

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

theorem RX_irrel_log_faults {I : Interface} {α : Abs I.Ghost}
    {bind : Binding I S X} {w : World S X E} {st : EvmState}
    (log' : List E) (fo : Nat → Bool) (h : RX α bind w st) :
    RX α bind { w with log := log', faults := fo } st := h

def dummyCtx (self : Address) : Ctx where
  sender := 0
  self := self

end Lsc.Compiler
