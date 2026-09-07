import Lsc.Compiler.EndToEndExt
import Lsc.Security.Wealth

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Generic bytecode ↔ Security transport. An arbitrary halted EVM call list
decodes to a well-formed Security trace (dispatcher rejects dropped). S1 is
`transport_*`; S2 threads bindings/`ξ` as `transport_*_ext`. Worlds are
log-cleared (`w.log = []`): Yul `mkEvmState*` starts empty, and Security
`Inv`/`claim` on Token/Vault ignore `log`.
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
  hcomp : compile rt = some is

/-- S2 binding family. One-binding contracts instantiate `bs := [⟨α, bind⟩]`. -/
structure TransportBindings (S X E ε : Type) (I : Interface)
    (T : TransportSetup S X E ε) where
  bs : List (BindEnv I S X)
  extCalls : ExternalCalls
  hCalls : CallsRealized extCalls
  htot : CallsTotal extCalls
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

theorem transport_step (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (ctx : Ctx) (cd : List UInt8) (w : World S X E) (σ : U256 → U256)
    (hctxWF : CtxWF ctx) (hcd : cd.length < wordBound)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w) :
    let yst0 := mkEvmState cd σ evmKeccak ctx
    ∃ σ', EvmCallRun T.is yst0 σ' ∧
      match decodeCall T ctx cd with
      | none => σ' = σ
      | some c =>
          let w' := { step (.call c) w with log := [] }
          storageRel T.c T.Γ evmKeccak w'.self σ' ∧ WorldWF T.c T.Γ w' := by
  intro yst0
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmState _ _ _ _ hctxWF hcd
  have hR : R T.c T.Γ evmKeccak w yst0 :=
    R_mkEvmState evmKeccak w cd σ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmState_immutable _ _ _ _ k
  obtain ⟨σ', hRun, hpost⟩ :=
    evmCallRun_of_correct T.c T.Γ T.lawful T.hκ hcf T.hctor T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR himm0
  refine ⟨σ', hRun, ?_⟩
  rw [mkEvmState_calldata] at hpost
  cases hsel : selectedFn T.c cd with
  | none =>
    have hdec : decodeCall T ctx cd = none := by simp [decodeCall, hsel]
    simp only [hsel] at hpost
    simp [hdec]
    simpa [yst0, mkEvmState_storage] using hpost
  | some f =>
    obtain ⟨fn, hfn, heq⟩ := T.codec.decodeFn_of_mem f (selectedFn_mem hsel)
    have hdec : decodeCall T ctx cd =
        some (Call.ofCtx ctx fn (T.codec.decode fn (decodeArgs f cd))) := by
      simp [decodeCall, hsel, hfn]
    simp only [hsel] at hpost
    simp only [hdec]
    rw [step_ofCtx]
    have hwa := core_exec_cd T heq ctx w cd
    rw [← hwa]
    cases htx : Tx.run (Core.denote T.Γ f.core (decodeArgs f cd).reverse) ctx w with
    | ok prod =>
      rcases prod with ⟨_, w'⟩
      simp only [htx] at hpost
      simp [worldAfter, htx]
      exact ⟨hpost.1, WorldWF_log [] hpost.2⟩
    | error e =>
      simp only [htx] at hpost
      simp [worldAfter, htx]
      refine ⟨?_, WorldWF_log [] hwf⟩
      simpa [yst0, mkEvmState_storage, hpost] using hs

/-- Universal S1: every halted EVM run of an arbitrary calldata list is
`storageRel` of `Security.run` of the decoded trace (dispatcher rejects
dropped). Requires `w.log = []`. -/
theorem transport_trace (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hE : EvmTraceRunAll T.is calls σ σ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      storageRel T.c T.Γ evmKeccak (run tr w).self σ' ∧
      WorldWF T.c T.Γ { run tr w with log := [] } := by
  refine ⟨wf_decodeTrace T self calls hWF, ?_⟩
  induction calls generalizing w σ σ' with
  | nil =>
    cases hE
    refine ⟨?_, ?_⟩
    · simpa [decodeTrace, run] using hs
    · simpa [decodeTrace, run] using WorldWF_log [] hwf
  | cons call rest ih =>
    have ⟨hctxWF, hcd⟩ := (CallsWF.head hWF).2.2
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      obtain ⟨σ₁, hRun, hpost⟩ :=
        transport_step T hcf call.ctx call.calldata w σ hctxWF hcd hs hlog hwf
      have heq := evmCallRun_eq_of_start h1 hRun hstart
      rw [heq] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        have htl' : EvmTraceRunAll T.is rest σ σ' := by simpa [hpost] using htl
        simpa [decodeTrace, hdec] using
          ih (w := w) (σ := σ) (σ' := σ') hs hlog hwf hWFtl htl'
      | some c =>
        simp only [hdec] at hpost
        let w1 : World S X E := { step (.call c) w with log := [] }
        have ⟨hs', hwf'⟩ :=
          ih (w := w1) (σ := σ₁) (σ' := σ') hpost.1 rfl hpost.2 hWFtl htl
        have hself : (run (.call c :: decodeTrace T rest) w).self =
            (run (decodeTrace T rest) w1).self :=
          post_congr_run hpc (decodeTrace T rest) (step (.call c) w) w1 rfl rfl
        refine ⟨?_, ?_⟩
        · simp only [decodeTrace, hdec]
          rwa [hself]
        · simp only [decodeTrace, hdec]
          exact WorldWF_of_self (w := { run (decodeTrace T rest) w1 with log := [] })
            hself.symm hwf'

theorem transport_exists (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (tr : List (Step T.spec)) (w : World S X E) (σ : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) :
    ∃ σ', EvmTraceRun T.is (encodeCalls T tr) σ σ' ∧
      storageRel T.c T.Γ evmKeccak
        (run (decodeTrace T (encodeCalls T tr)) { w with log := [] }).self σ' ∧
      WorldWF T.c T.Γ
        { run (decodeTrace T (encodeCalls T tr)) { w with log := [] } with log := [] } := by
  induction tr generalizing w σ with
  | nil =>
    refine ⟨σ, EvmTraceRun.nil σ, ?_, ?_⟩
    · simpa [encodeCalls, decodeTrace, run] using hs
    · simpa [encodeCalls, decodeTrace, run] using WorldWF_log [] hwf
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls] using
        ih (w := w) (σ := σ) hs hwf (by simpa [EncodeBounded] using hb)
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      have hf := T.codec.mem c.fn
      have hk := T.hctor _ hf
      have hlenA := T.codec.encode_length c.fn c.args
      have hcd : (fnCalldata (T.codec.fnDef c.fn)
          (T.codec.encode c.fn c.args)).length < wordBound := by
        rw [length_fnCalldata, hlenA]
        exact T.hbound _ hf
      obtain ⟨σ₁, h1, hpost⟩ :=
        evmCallRun_fnCalldata T.c T.Γ T.lawful T.hκ hcf T.hctor T.hlen T.hbound
          T.nodup T.rt T.hrt T.is T.hcomp c.toCtx (T.codec.fnDef c.fn)
          (T.codec.encode c.fn c.args) { w with log := [] } σ hf hk hlenA hWargs
          hctxWF (by simpa using hs) rfl (WorldWF_log [] hwf) hcd
      have hdecC := encodeCall_decode T c hWargs
      have hwa := T.codec.core_exec c.fn c.args c.toCtx { w with log := [] }
      let w1 : World S X E :=
        { worldAfter (T.spec.exec c.fn c.args) c.toCtx { w with log := [] }
          with log := [] }
      have hs1 : storageRel T.c T.Γ evmKeccak w1.self σ₁ := by
        cases htx : Tx.run
            (Core.denote T.Γ (T.codec.fnDef c.fn).core
              (T.codec.encode c.fn c.args).reverse)
            c.toCtx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_ok htx]
          exact hpost.1
        | error e =>
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_error htx]
          simpa [hpost] using hs
      have hwf1 : WorldWF T.c T.Γ w1 := by
        cases htx : Tx.run
            (Core.denote T.Γ (T.codec.fnDef c.fn).core
              (T.codec.encode c.fn c.args).reverse)
            c.toCtx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp only [htx] at hpost
          simp only [w1]
          rw [← hwa, worldAfter_ok htx]
          exact WorldWF_log [] hpost.2
        | error e =>
          simp only [w1]
          rw [← hwa, worldAfter_error htx]
          exact WorldWF_log [] hwf
      obtain ⟨σ', htl, hs', hwf'⟩ := ih w1 σ₁ hs1 hwf1 htlB
      have hdt : decodeTrace T (encodeCall T c :: encodeCalls T rest) =
          .call c :: decodeTrace T (encodeCalls T rest) := by
        simp [encodeCall] at hdecC
        simp [decodeTrace, encodeCall, hdecC]
      have hself := post_congr_run hpc (decodeTrace T (encodeCalls T rest))
          (step (.call c) { w with log := [] }) w1 rfl rfl
      refine ⟨σ',
        EvmTraceRun.cons (call := encodeCall T c) (tr := encodeCalls T rest)
          (yst0 := mkEvmState (encodeCall T c).calldata σ evmKeccak c.toCtx)
          (mkEvmState_calldata _ _ _ _) (mkEvmState_storage _ _ _ _) h1 htl, ?_, ?_⟩
      · simp only [encodeCalls, hdt, run_cons]
        rwa [hself]
      · simp only [encodeCalls, hdt, run_cons]
        exact WorldWF_of_self (w := { run (decodeTrace T (encodeCalls T rest)) w1
            with log := [] }) hself.symm hwf'

/-! ## S2 (bindings / foreign storage) -/

variable {I : Interface}

theorem transport_step_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (ctx : Ctx) (cd : List UInt8) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hctxWF : CtxWF ctx) (hcd : cd.length < wordBound)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hRX : RXs Xpkg.bs w (mkEvmStateExt cd σ ξ evmKeccak ctx))
    (hBindNe : BindEnvs.neSelf Xpkg.bs ctx.self w.self)
    (hconf : BindEnvs.conforms Xpkg.bs ctx.self w.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    let yst0 := mkEvmStateExt cd σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ T.is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match decodeCall T ctx cd with
        | none => σ' = σ ∧ ξ' = evmForeign yst0
        | some c =>
            let wfo : World S X E := { w with faults := fo }
            let w' : World S X E := { step (.call c) wfo with log := [] }
            storageRel T.c T.Γ evmKeccak w'.self σ' ∧ WorldWF T.c T.Γ w' ∧
              ∃ stObs : EvmState,
                stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                  RXs Xpkg.bs w' stObs := by
  intro yst0
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R T.c T.Γ evmKeccak w yst0 :=
    R_mkEvmStateExt evmKeccak w cd σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 :=
    fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  obtain ⟨σ', ξ', hRun, fo, hpost⟩ :=
    evmCallRun_of_correct_ext (I := I) Xpkg.bs T.c T.Γ T.lawful T.hκ
      Xpkg.extCalls Xpkg.hCalls Xpkg.htot T.hctor Xpkg.hS2 T.hlen T.hbound
      T.rt T.hrt T.is T.hcomp ctx w yst0 hctx hR hRX Xpkg.hign hBindNe hconf
      Xpkg.hsame Xpkg.horth hinj Xpkg.hBind Xpkg.hslot himm0
  refine ⟨σ', ξ', hRun, fo, ?_⟩
  rw [mkEvmStateExt_calldata] at hpost
  cases hsel : selectedFn T.c cd with
  | none =>
    have hdec : decodeCall T ctx cd = none := by simp [decodeCall, hsel]
    simp only [hsel] at hpost
    simp [hdec]
    simpa [yst0, mkEvmStateExt_storage] using hpost
  | some f =>
    obtain ⟨fn, hfn, heq⟩ := T.codec.decodeFn_of_mem f (selectedFn_mem hsel)
    have hdec : decodeCall T ctx cd =
        some (Call.ofCtx ctx fn (T.codec.decode fn (decodeArgs f cd))) := by
      simp [decodeCall, hsel, hfn]
    simp only [hsel] at hpost
    simp only [hdec]
    rw [step_ofCtx]
    let wfo : World S X E := { w with faults := fo }
    have hwa := core_exec_cd T heq ctx wfo cd
    rw [← hwa]
    cases htx : Tx.run (Core.denote T.Γ f.core (decodeArgs f cd).reverse)
        ctx wfo with
    | ok prod =>
      rcases prod with ⟨_, w'⟩
      rw [htx] at hpost
      rw [worldAfter_ok htx]
      rcases hpost with ⟨hs', hwf', stObs, hσ, hξ, hRX'⟩
      exact ⟨hs', WorldWF_log [] hwf', stObs, hσ, hξ, hRX'⟩
    | error e =>
      rw [htx] at hpost
      rw [worldAfter_error htx]
      refine ⟨?_, WorldWF_of_self (w := w) rfl hwf, yst0, ?_, ?_, ?_⟩
      · simpa [yst0, mkEvmStateExt_storage, hpost] using hs
      · simpa [hpost, yst0, mkEvmStateExt_storage]
      · simpa [hpost]
      · exact RXs_irrel_log_faults (fo := fo) ([] : List E) hRX

theorem RXs_dummy_of_ξ {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    (hF : BindEnvs.ofState_foreign bs)
    (self : Address) (w : World S X E)
    (σ ξ σ₁ ξ₁ : _) (κ : List UInt8 → U256)
    (hne : BindEnvs.neSelf bs self w.self)
    (hξ : ∀ e ∈ bs,
      ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
      ξ (BitVec.ofNat 256 (e.bind.addr w.self)))
    (hRX : RXs bs w (mkEvmStateExt ([] : List UInt8) σ ξ κ (dummyCtx self))) :
    RXs bs w (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ κ (dummyCtx self)) := by
  refine RXs_of_foreign hF ?_ hRX
  intro e he k
  have hne' := hne e he
  have hloc :
      evmForeign (mkEvmStateExt ([] : List UInt8) σ ξ κ (dummyCtx self))
        (BitVec.ofNat 256 (e.bind.addr w.self)) k =
      ξ (BitVec.ofNat 256 (e.bind.addr w.self)) k := by
    simp [dummyCtx, mkEvmStateExt_foreign, hne']
  have hloc' :
      evmForeign (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ κ (dummyCtx self))
        (BitVec.ofNat 256 (e.bind.addr w.self)) k =
      ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) k := by
    simp [dummyCtx, mkEvmStateExt_foreign, hne']
  simp [hloc, hloc', hξ e he]

/-- Universal S2: every halted EVM run of an arbitrary calldata list yields a
decoded well-formed Security trace and a post-world `w'` with `R`/`RX`.
`w'` is the fo-adjusted fold (Core revert keeps storage); it need not equal
`run tr w` when the EVM-chosen `fo` differs from `w.faults`. -/
theorem transport_trace_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (Inv : World S X E → Prop)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      ∃ w' : World S X E,
        storageRel T.c T.Γ evmKeccak w'.self σ' ∧
        WorldWF T.c T.Γ w' ∧
        RXs Xpkg.bs w'
          (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
        Inv w' ∧
        (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) := by
  refine ⟨wf_decodeTrace T self calls hWF, ?_⟩
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    exact ⟨{ w with log := [] }, hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, fun _ _ => rfl⟩
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      have hRXcall : RXs Xpkg.bs w
          (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx] using htgt.symm) hRX
      have hBindNe' : BindEnvs.neSelf Xpkg.bs call.ctx.self w.self := by
        simpa [htgt] using hBindNe
      have hconfCall : BindEnvs.conforms Xpkg.bs call.ctx.self w.self Xpkg.extCalls := by
        simpa [htgt] using hconf w
      obtain ⟨σ₁, ξ₁, hRun, fo, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata w σ ξ hctxWF hcd
          hs hlog hwf hRXcall hBindNe' hconfCall hinj
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        have hξeq : ∀ e ∈ Xpkg.bs,
            ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
            ξ (BitVec.ofNat 256 (e.bind.addr w.self)) := by
          intro e he
          rw [hξ]
          exact mkEvmStateExt_foreign_ne _ _ _ _ _ _ (hBindNe' e he)
        have hRX1 : RXs Xpkg.bs w
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_dummy_of_ξ Xpkg.hF self w σ ξ σ₁ ξ₁ evmKeccak hBindNe hξeq hRX
        simpa [decodeTrace, hdec] using
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl hRX1 hBindNe hinj hw htl
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
        let wfo : World S X E := { w with faults := fo }
        let w1 : World S X E := { step (.call c) wfo with log := [] }
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wfo (htgtc.trans htgt) (by simpa [hsend] using hne) (hInvF w fo hw))
        have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
          intro e he
          simpa [w1, wfo, step] using
            Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
        have hRXw1 : RXs Xpkg.bs w1
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
            (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
        have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
          BindEnvs.neSelf_of_addr hBindNe haddr
        have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
          BindEnvs.addrInj_of_addr hinj haddr
        have ⟨w', hs', hwf', hRX', hInv', haddr'⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl hRXw1 hBindNe1 hinj1 hw1 htl
        exact ⟨w', hs', hwf', hRX', hInv', fun e he => (haddr' e he).trans (haddr e he)⟩

/-- S2 claim transport: `NoUnauthorizedDecrease` along the fo-adjusted fold
(`w'` from `transport_trace_ext`), when `Auth`/`Inv` ignore log and faults. -/
theorem transport_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self : Address) (a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (hA : NoAuthAlong Auth a (decodeTrace T calls) w)
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    ∃ w' : World S X E,
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self := by
  induction calls generalizing w σ ξ σ' ξ' with
  | nil =>
    cases hE
    exact ⟨{ w with log := [] }, hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, Nat.le_refl _⟩
  | cons call rest ih =>
    have ⟨htgt, hne, hctxWF, hcd⟩ := CallsWF.head hWF
    have hWFtl := CallsWF.tail hWF
    cases hE with
    | cons hstart h1 htl =>
      have hRXcall : RXs Xpkg.bs w
          (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx] using htgt.symm) hRX
      have hBindNe' : BindEnvs.neSelf Xpkg.bs call.ctx.self w.self := by
        simpa [htgt] using hBindNe
      have hconfCall : BindEnvs.conforms Xpkg.bs call.ctx.self w.self Xpkg.extCalls := by
        simpa [htgt] using hconf w
      obtain ⟨σ₁, ξ₁, hRun, fo, hpost⟩ :=
        transport_step_ext T Xpkg call.ctx call.calldata w σ ξ hctxWF hcd
          hs hlog hwf hRXcall hBindNe' hconfCall hinj
      have heq := evmCallRunξ_eq_of_start h1 hRun hstart
      rw [heq.1, heq.2] at htl
      cases hdec : decodeCall T call.ctx call.calldata with
      | none =>
        simp only [hdec] at hpost
        obtain ⟨hσeq, hξ⟩ := hpost
        have hsσ : storageRel T.c T.Γ evmKeccak w.self σ₁ := by
          rw [hσeq]; exact hs
        have hξeq : ∀ e ∈ Xpkg.bs,
            ξ₁ (BitVec.ofNat 256 (e.bind.addr w.self)) =
            ξ (BitVec.ofNat 256 (e.bind.addr w.self)) := by
          intro e he
          rw [hξ]
          exact mkEvmStateExt_foreign_ne _ _ _ _ _ _ (hBindNe' e he)
        have hRX1 : RXs Xpkg.bs w
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_dummy_of_ξ Xpkg.hF self w σ ξ σ₁ ξ₁ evmKeccak hBindNe hξeq hRX
        have ⟨w', hs', hwf', hRX', hInv', hle⟩ :=
          ih (w := w) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hsσ hlog hwf hWFtl hRX1 hBindNe hinj
            (by simpa [decodeTrace, hdec] using hA) hw htl
        exact ⟨w', hs', hwf', hRX', hInv', hle⟩
      | some c =>
        simp only [hdec] at hpost
        rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
        let wfo : World S X E := { w with faults := fo }
        let w1 : World S X E := { step (.call c) wfo with log := [] }
        have hwfo : Inv wfo := hInvF w fo hw
        have ⟨hna, hAtl⟩ : ¬ Auth a c w.self ∧
            NoAuthAlong Auth a (decodeTrace T rest) (step (.call c) w) := by
          simpa [decodeTrace, hdec, NoAuthAlong] using hA
        have hle1 : claim a w.self ≤ claim a w1.self := by
          have hna' : ¬ Auth a c wfo.self := by simpa [wfo] using hna
          have hnot : ¬ claim a w1.self < claim a w.self := by
            intro hlt
            have hlt' : claim a (step (.call c) wfo).self < claim a wfo.self := by
              simpa [w1, wfo] using hlt
            exact hna' (hN c wfo a hwfo hlt')
          exact Nat.le_of_not_lt hnot
        have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
          intro e he
          simpa [w1, wfo, step] using
            Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
        have hRXw1 : RXs Xpkg.bs w1
            (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
          RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
            (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
        have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
          BindEnvs.neSelf_of_addr hBindNe haddr
        have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
          BindEnvs.addrInj_of_addr hinj haddr
        have ⟨htgtc, hsend⟩ := decodeCall_ctx T hdec
        have hw1 : Inv w1 :=
          hInvL _ [] (hP c wfo (htgtc.trans htgt) (by simpa [hsend] using hne) hwfo)
        have ⟨w', hs', hwf', hRX', hInv', hle⟩ :=
          ih (w := w1) (σ := σ₁) (ξ := ξ₁) (σ' := σ') (ξ' := ξ')
            hs1 rfl hwf1 hWFtl hRXw1 hBindNe1 hinj1
            ((hAirr (decodeTrace T rest) (step (.call c) w) w1).mp hAtl) hw1 htl
        exact ⟨w', hs', hwf', hRX', hInv', Nat.le_trans hle1 hle⟩

theorem transport_exists_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop)
    (self : Address)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) := by
  induction tr generalizing w σ ξ with
  | nil =>
    exact ⟨σ, ξ, { w with log := [] }, EvmTraceRunExt.nil σ ξ,
      hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, fun _ _ => rfl⟩
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw hRX hBindNe hinj
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      have hRXcall :
          RXs Xpkg.bs { w with log := ([] : List E) }
            (mkEvmStateExt (encodeCall T c).calldata σ ξ evmKeccak c.toCtx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx, Call.toCtx] using htgt.symm) hRX
      obtain ⟨σ₁, ξ₁, h1, fo, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          { w with log := ([] : List E) } σ ξ hctxWF hcd
          (by simpa using hs) rfl (WorldWF_log [] hwf) hRXcall
          (by simpa [Call.toCtx, htgt] using hBindNe)
          (by simpa [Call.toCtx, htgt] using hconf { w with log := ([] : List E) })
          hinj
      simp only [hdecC] at hpost
      let wfo : World S X E :=
        { { w with log := ([] : List E) } with faults := fo }
      let w1 : World S X E := { step (.call c) wfo with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
      have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
        intro e he
        simpa [w1, wfo, step] using Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
      have hRXw1 : RXs Xpkg.bs w1
          (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
        RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
          (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
      have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
        BindEnvs.neSelf_of_addr hBindNe haddr
      have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
        BindEnvs.addrInj_of_addr hinj haddr
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wfo (by simpa [wfo] using htgt)
          (by simpa [wfo] using hne) (hInvF _ fo (hInvL w [] hw)))
      obtain ⟨σ', ξ', w', htl, hs', hwf', hRX', hInv', haddr'⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1 hRXw1 hBindNe1 hinj1
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hRX', hInv',
        fun e he => (haddr' e he).trans (haddr e he)⟩

/-- Forward S2 with claim monotonicity along the fo-fold of `encodeCalls`. -/
theorem transport_exists_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hA : NoAuthAlong Auth a (callsOf tr) w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self := by
  induction tr generalizing w σ ξ with
  | nil =>
    exact ⟨σ, ξ, { w with log := [] }, EvmTraceRunExt.nil σ ξ,
      hs, WorldWF_log [] hwf, hRX, hInvL w [] hw, Nat.le_refl _⟩
  | cons s rest ih =>
    match s with
    | .env _ =>
      simpa [encodeCalls, callsOf] using
        ih (w := w) (σ := σ) (ξ := ξ) hs hwf
          (by simpa [EncodeBounded] using hb) hW hw hA hRX hBindNe hinj
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      rcases hA with ⟨hna, hAtl⟩
      have hdecC := encodeCall_decode T c hWargs
      have hcd : (encodeCall T c).calldata.length < wordBound := by
        simp only [encodeCall]
        rw [length_fnCalldata, T.codec.encode_length]
        exact T.hbound _ (T.codec.mem _)
      have hRXcall :
          RXs Xpkg.bs { w with log := ([] : List E) }
            (mkEvmStateExt (encodeCall T c).calldata σ ξ evmKeccak c.toCtx) :=
        RXs_mkEvmStateExt_ctx Xpkg.hF
          (by simpa [dummyCtx, Call.toCtx] using htgt.symm) hRX
      obtain ⟨σ₁, ξ₁, h1, fo, hpost⟩ :=
        transport_step_ext T Xpkg c.toCtx (encodeCall T c).calldata
          { w with log := ([] : List E) } σ ξ hctxWF hcd
          (by simpa using hs) rfl (WorldWF_log [] hwf) hRXcall
          (by simpa [Call.toCtx, htgt] using hBindNe)
          (by simpa [Call.toCtx, htgt] using hconf { w with log := ([] : List E) })
          hinj
      simp only [hdecC] at hpost
      let wfo : World S X E :=
        { { w with log := ([] : List E) } with faults := fo }
      let w1 : World S X E := { step (.call c) wfo with log := [] }
      rcases hpost with ⟨hs1, hwf1, stObs, hσ, hξobs, hRXobs⟩
      have hwfo : Inv wfo := hInvF _ fo (hInvL w [] hw)
      have hle1 : claim a w.self ≤ claim a w1.self := by
        have hna' : ¬ Auth a c wfo.self := by simpa [wfo] using hna
        have hnot : ¬ claim a w1.self < claim a w.self := by
          intro hlt
          have hlt' : claim a (step (.call c) wfo).self < claim a wfo.self := by
            simpa [w1, wfo] using hlt
          exact hna' (hN c wfo a hwfo hlt')
        exact Nat.le_of_not_lt hnot
      have haddr : ∀ e ∈ Xpkg.bs, e.bind.addr w1.self = e.bind.addr w.self := by
        intro e he
        simpa [w1, wfo, step] using Xpkg.bindAddr_stable e he c.fn c.args c.toCtx wfo
      have hRXw1 : RXs Xpkg.bs w1
          (mkEvmStateExt ([] : List UInt8) σ₁ ξ₁ evmKeccak (dummyCtx self)) :=
        RXs_mkEvmStateExt_ne Xpkg.hF hRXobs
          (Eq.symm hξobs) (by simpa [dummyCtx] using BindEnvs.neSelf_of_addr hBindNe haddr)
      have hBindNe1 : BindEnvs.neSelf Xpkg.bs self w1.self :=
        BindEnvs.neSelf_of_addr hBindNe haddr
      have hinj1 : BindEnvs.addrInj Xpkg.bs w1.self :=
        BindEnvs.addrInj_of_addr hinj haddr
      have hw1 : Inv w1 :=
        hInvL _ [] (hP c wfo (by simpa [wfo] using htgt)
          (by simpa [wfo] using hne) hwfo)
      obtain ⟨σ', ξ', w', htl, hs', hwf', hRX', hInv', hle⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hs1 hwf1 htlB hWtl hw1
          ((hAirr (callsOf rest) (step (.call c) w) w1).mp hAtl) hRXw1 hBindNe1 hinj1
      exact ⟨σ', ξ', w',
        EvmTraceRunExt.cons (call := encodeCall T c) h1
          (by simpa [encodeCalls] using htl), hs', hwf', hRX', hInv',
        Nat.le_trans hle1 hle⟩

end Lsc.Compiler
