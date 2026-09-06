import Lsc.Compiler.Proof.Dispatch
import Lsc.Compiler.Proof.Lift
import Lsc.Compiler.Proof.Calldata
import Lsc.Compiler.Proof.EvmDet
import Lsc.Compiler.Bytecode
import Lsc.Compiler.YulExec
import Lsc.Security.Trace
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
End-to-end glue: call-free `RunCommitted` → powdr `compile_correct` → EVM `Steps`.
`EvmCallRun` is universal over halted executions (`steps_halted_unique`).
The compiler still does not import `Security` except in this module.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- Keccak oracle forced by `EnvMatch.keccak` (`targetKeccakOracle_agrees`). -/
abbrev evmKeccak : List UInt8 → U256 := targetKeccakOracle

@[instance_reducible] def closedModel : ExternalModel where
  calls := ExternalCalls.none
  creates := ExternalCreates.none

def ofConv (v : EvmSemantics.UInt256) : U256 := BitVec.ofNat 256 v.toNat

theorem ofConv_conv (v : U256) : ofConv (conv v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [ofConv, conv_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]

/-- Yul storage recovered from the executing account through `conv`. -/
def accountYulStorage (s : State) : U256 → U256 :=
  fun k => ofConv ((s.accountMap s.executionEnv.address).storage.get (conv k))

def storageRel' {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (σ : S) (s : State) : Prop :=
  storageRel c Γ κ σ (accountYulStorage s)

def haltOK (t : RetTy) (v : t.denote) (s : State) : Prop :=
  if t = .unit then s.halt = .Success
  else s.halt = .Returned ∧ s.hReturn.toList = abiBytes (retWords (t := t) v)

theorem committedState_halted (st0 st' : EvmState) :
    (committedState st0 st').halted = st'.halted := by
  unfold committedState
  split <;> [rfl; split <;> rfl]

theorem storage_eq_account {yst : EvmState} {s : State} (hm : StateMatch yst s) :
    accountYulStorage s = yst.storage := by
  funext k
  have h := hm.stor k
  simp only [accountYulStorage]
  rw [← h, ofConv_conv]

theorem storageRel_account {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ σ} {yst : EvmState} {s : State}
    (hs : storageRel c Γ κ σ yst.storage) (hm : StateMatch yst s) :
    storageRel' c Γ κ σ s := by
  simpa [storageRel', storage_eq_account hm] using hs

theorem haltOK_of_success {t : RetTy} {v : t.denote} {yst : EvmState} {s : State}
    (hs : haltSuccess t v yst.halted) (hHM : HaltedMatch yst s) : haltOK t v s := by
  obtain ⟨hk, hhalt, hM⟩ := hHM
  unfold haltSuccess at hs
  unfold haltOK
  split at hs
  · next ht =>
    rw [if_pos ht]
    rw [hs] at hhalt
    cases hhalt
    simpa [HaltMatch] using hM
  · next ht =>
    rw [if_neg ht]
    rw [hs] at hhalt
    cases hhalt
    simpa [HaltMatch] using hM

theorem reverted_of_halted {yst : EvmState} {s : State} {bytes : List UInt8}
    (h : yst.halted = some (.revert, bytes)) (hHM : HaltedMatch yst s) :
    s.halt = .Reverted ∧ s.hReturn.toList = bytes := by
  obtain ⟨hk, hhalt, hM⟩ := hHM
  rw [h] at hhalt
  cases hhalt
  simpa [HaltMatch] using hM

theorem obs_eq_of_commit {st0 st' stObs : EvmState} {k : HaltKind} {bs : List UInt8}
    (hobs : stObs = committedState st0 st')
    (hhalted : stObs.halted = st'.halted)
    (hh : stObs.halted = some (k, bs)) (hk : k.commits = true) :
    stObs = st' := by
  have hh' : st'.halted = some (k, bs) := hhalted ▸ hh
  rw [hobs, committedState_commit hh' hk]

theorem obs_storage_rollback {st0 st' stObs : EvmState} {bytes : List UInt8}
    (hobs : stObs = committedState st0 st')
    (hhalted : stObs.halted = st'.halted)
    (hh : stObs.halted = some (.revert, bytes)) :
    stObs.storage = st0.storage := by
  have hh' : st'.halted = some (.revert, bytes) := hhalted ▸ hh
  rw [hobs, committedState_rollback hh' HaltKind.revert_commits]

theorem halt_ne_running_of_HaltMatch {hk : YulSemantics.EVM.HaltKind × List UInt8}
    {s : State} (h : HaltMatch hk s) : s.halt ≠ .Running := by
  intro hrun
  unfold HaltMatch at h
  split at h
  · cases (h.symm.trans hrun)
  · cases (h.1.symm.trans hrun)
  · cases (h.1.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.symm.trans hrun)
  · cases (h.1.symm.trans hrun)

theorem Halted_of_HaltedMatch {yst : EvmState} {s : State}
    (h : HaltedMatch yst s) (hcs : s.callStack = []) : Halted s :=
  ⟨by
    obtain ⟨hk, _, hM⟩ := h
    exact halt_ne_running_of_HaltMatch hM, hcs⟩

theorem Halted_of_compile_out {s' : State} {yst' : EvmState} {o : Outcome}
    (hcs : s'.callStack = [])
    (hOut : (o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
            (o = .halt ∧ HaltedMatch yst' s')) : Halted s' := by
  rcases hOut with ⟨_, hs, _⟩ | ⟨_, hHM⟩
  · exact ⟨by simp [hs], hcs⟩
  · exact Halted_of_HaltedMatch hHM hcs

/-- Observable post-storage of a top-level halted frame. Revert rollback is a
modelling assumption (`TRUSTED_COMPUTING_BASE.md`): raw `Steps` does not roll back. -/
def postStorage (yst0 : EvmState) (s' : State) : U256 → U256 :=
  match s'.halt with
  | .Reverted => yst0.storage
  | _ => accountYulStorage s'

theorem postStorage_reverted {yst0 s'} (h : s'.halt = .Reverted) :
    postStorage yst0 s' = yst0.storage := by simp [postStorage, h]

theorem postStorage_commit {yst0 s'} (h : s'.halt ≠ .Reverted) :
    postStorage yst0 s' = accountYulStorage s' := by
  unfold postStorage
  split
  · next h' => exact absurd h' h
  · rfl

def EvmStartOK (is : List Instr) (yst0 : EvmState) (s0 : State) : Prop :=
  FrameOK (assemble is) s0 ∧ StateMatch yst0 s0 ∧
  s0.pc = EvmSemantics.UInt256.ofNat 0 ∧ s0.stack = []

def setGas (s : State) (g : Nat) : State :=
  { s with gasAvailable := g }

@[simp] theorem setGas_gas (s g) : (setGas s g).gasAvailable = g := rfl
@[simp] theorem setGas_pc (s g) : (setGas s g).pc = s.pc := rfl
@[simp] theorem setGas_stack (s g) : (setGas s g).stack = s.stack := rfl

theorem frameOK_setGas {code s g} (h : FrameOK code s) : FrameOK code (setGas s g) :=
  ⟨h.hcode, h.codeSmall, h.fork, h.noPrecompile, h.callStack, h.running⟩

theorem stateMatch_setGas {yst s g} (h : StateMatch yst s) :
    StateMatch yst (setGas s g) := by
  cases h
  constructor <;> assumption

theorem evmStartOK_setGas {is yst0 s0 g} (h : EvmStartOK is yst0 s0) :
    EvmStartOK is yst0 (setGas s0 g) :=
  ⟨frameOK_setGas h.1, stateMatch_setGas h.2.1, h.2.2.1, h.2.2.2⟩

/-- One compiled call: every matching start state with enough gas has a halted
`Steps` run, and **every** halted run determines the same post-storage `σ'`. -/
def EvmCallRun (is : List Instr) (yst0 : EvmState) (σ' : U256 → U256) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    EvmStartOK is yst0 s0 → b ≤ s0.gasAvailable →
    (∃ s', Steps s0 s' ∧ Halted s') ∧
    ∀ s', Steps s0 s' → Halted s' → σ' = postStorage yst0 s'

theorem evmCallRun_eq_of_start {is yst0 σ1 σ2 s0}
    (h1 : EvmCallRun is yst0 σ1) (h2 : EvmCallRun is yst0 σ2)
    (hs : EvmStartOK is yst0 s0) : σ1 = σ2 := by
  obtain ⟨b1, hb1⟩ := h1
  obtain ⟨b2, hb2⟩ := h2
  let s0' := setGas s0 (s0.gasAvailable + b1 + b2)
  have hs' : EvmStartOK is yst0 s0' := evmStartOK_setGas hs
  have hgas1 : b1 ≤ s0'.gasAvailable := by
    change b1 ≤ s0.gasAvailable + b1 + b2
    omega
  have hgas2 : b2 ≤ s0'.gasAvailable := by
    change b2 ≤ s0.gasAvailable + b1 + b2
    omega
  obtain ⟨s', hS, hH⟩ := (hb1 s0' hs' hgas1).1
  have e1 := (hb1 s0' hs' hgas1).2 s' hS hH
  have e2 := (hb2 s0' hs' hgas2).2 s' hS hH
  exact e1.trans e2.symm

structure EvmCall where
  ctx : Ctx
  calldata : List UInt8

inductive EvmTraceRun (is : List Instr) : List EvmCall → (U256 → U256) → (U256 → U256) → Prop
  | nil (σ : U256 → U256) : EvmTraceRun is [] σ σ
  | cons {call : EvmCall} {tr : List EvmCall} {σ σ₁ σ' : U256 → U256} {yst0 : EvmState}
      (hcd : yst0.env.calldata = call.calldata)
      (hσ : yst0.storage = σ)
      (h1 : EvmCallRun is yst0 σ₁)
      (htl : EvmTraceRun is tr σ₁ σ') :
      EvmTraceRun is (call :: tr) σ σ'

/-- Universal trace: each call is an `EvmCallRun` at `mkEvmState` of that
call, witnessed by some matching start state (so post-storage is unique). -/
inductive EvmTraceRunAll (is : List Instr) : List EvmCall → (U256 → U256) → (U256 → U256) → Prop
  | nil (σ : U256 → U256) : EvmTraceRunAll is [] σ σ
  | cons {call : EvmCall} {tr : List EvmCall} {σ σ₁ σ' : U256 → U256} {s0 : State}
      (hstart : EvmStartOK is (mkEvmState call.calldata σ evmKeccak call.ctx) s0)
      (h1 : EvmCallRun is (mkEvmState call.calldata σ evmKeccak call.ctx) σ₁)
      (htl : EvmTraceRunAll is tr σ₁ σ') :
      EvmTraceRunAll is (call :: tr) σ σ'

/-- Dispatcher conclusion, interpreted on the compiled bytecode. -/
def BytecodeCallCorrect {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState) (is : List Instr) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    FrameOK (assemble is) s0 → StateMatch yst0 s0 →
    s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
    ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
      match selectedFn c yst0.env.calldata with
      | none => s'.halt = .Reverted ∧ s'.hReturn.toList = []
      | some f =>
        match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
        | .ok (v, w') => haltOK f.ret v s' ∧ storageRel' c Γ κ w'.self s'
        | .error e =>
          s'.halt = .Reverted ∧ ∃ bytes, s'.hReturn.toList = bytes ∧ haltError c Γ e bytes

theorem bytecode_call_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is := by
  let _model : ExternalModel := closedModel
  simp only [BytecodeCallCorrect]
  obtain ⟨stObs, hRC, hconcl⟩ :=
    runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound rt hrt ctx w yst0 hctx hR
  obtain ⟨yst', hrun, hobs⟩ := runCommitted_lift_run .none .none .any hRC
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have ⟨b, hb⟩ := compile_correct (model := closedModel) ExternalsRealized.none hcomp himm hrun
  refine ⟨b, ?_⟩
  intro s0 hOK hM hpc hstk hgas
  obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
  have hHM : HaltedMatch yst' s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH⟩
    · cases hn
    · exact hH
  have hhalted : stObs.halted = yst'.halted := by
    rw [hobs, committedState_halted]
  refine ⟨s', hSteps, hcs, ?_⟩
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    obtain ⟨hh, _⟩ := hconcl
    exact reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      obtain ⟨hsucc, hR'⟩ := hconcl
      obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
      have heq : stObs = yst' := obs_eq_of_commit hobs hhalted hh hk
      rcases hR' with ⟨hs, _, _, _⟩
      exact ⟨haltOK_of_success (heq ▸ hsucc) hHM, storageRel_account (heq ▸ hs) hSM⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      obtain ⟨bytes, hh, herr, _⟩ := hconcl
      have hr := reverted_of_halted (hhalted ▸ hh) hHM
      exact ⟨hr.1, bytes, hr.2, herr⟩

theorem evmCallRun_of_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ', EvmCallRun is yst0 σ' ∧
      match selectedFn c yst0.env.calldata with
      | none => σ' = yst0.storage
      | some f =>
        match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
        | .ok (_, w') => storageRel c Γ evmKeccak w'.self σ'
        | .error _ => σ' = yst0.storage := by
  let _model : ExternalModel := closedModel
  obtain ⟨stObs, hRC, hconcl⟩ :=
    runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound rt hrt ctx w yst0 hctx hR
  obtain ⟨yst', hrun, hobs⟩ := runCommitted_lift_run .none .none .any hRC
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have ⟨b, hb⟩ := compile_correct (model := closedModel) ExternalsRealized.none hcomp himm hrun
  have hhalted : stObs.halted = yst'.halted := by
    rw [hobs, committedState_halted]
  refine ⟨stObs.storage, ?_, ?_⟩
  · refine ⟨b, ?_⟩
    intro s0 hstart hgas
    rcases hstart with ⟨hOK, hM, hpc, hstk⟩
    obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
    have hH : Halted s' := Halted_of_compile_out hcs hOut
    have hHM : HaltedMatch yst' s' := by
      rcases hOut with ⟨hn, _⟩ | ⟨_, hH'⟩
      · cases hn
      · exact hH'
    have hpost : stObs.storage = postStorage yst0 s' := by
      cases hsel : selectedFn c yst0.env.calldata with
      | none =>
        simp only [hsel] at hconcl
        obtain ⟨hh, _⟩ := hconcl
        have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
        rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
      | some f =>
        simp only [hsel] at hconcl
        cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
        | ok prod =>
          rcases prod with ⟨v, w'⟩
          simp only [htx] at hconcl
          obtain ⟨hsucc, _⟩ := hconcl
          obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
          have heq : stObs = yst' := obs_eq_of_commit hobs hhalted hh hk
          have hOK' := haltOK_of_success (heq ▸ hsucc) hHM
          have hnr : s'.halt ≠ .Reverted := by
            unfold haltOK at hOK'
            split at hOK'
            · intro h; cases (hOK'.symm.trans h)
            · intro h; cases (hOK'.1.symm.trans h)
          rw [postStorage_commit hnr, storage_eq_account hSM, heq]
        | error e =>
          simp only [htx] at hconcl
          obtain ⟨bytes, hh, _, _⟩ := hconcl
          have hr := reverted_of_halted (hhalted ▸ hh) hHM
          rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
    refine ⟨⟨s', hSteps, hH⟩, ?_⟩
    intro s'' hS'' hH''
    rw [steps_halted_unique hS'' hSteps hH'' hH]
    exact hpost
  · cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl ⊢
      obtain ⟨hh, _⟩ := hconcl
      exact obs_storage_rollback hobs hhalted hh
    | some f =>
      simp only [hsel] at hconcl ⊢
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hconcl ⊢
        obtain ⟨hsucc, hR'⟩ := hconcl
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = yst' := obs_eq_of_commit hobs hhalted hh hk
        rcases hR' with ⟨hs, _, _, _⟩
        simpa [heq] using hs
      | error e =>
        simp only [htx] at hconcl ⊢
        obtain ⟨bytes, hh, _, _⟩ := hconcl
        exact obs_storage_rollback hobs hhalted hh

/-- Fold `Core.denote` like `Security.run` on encoded `(ctx, fn, args)` calls. -/
def coreRun {S X E ε : Type} (Γ : ContractSchema S X E ε) :
    List (Ctx × FnDef × List Nat) → World S X E → World S X E
  | [], w => w
  | (ctx, f, args) :: rest, w =>
    coreRun Γ rest
      { Security.worldAfter (Core.denote Γ f.core args.reverse) ctx w with log := [] }

theorem coreRun_nil {S X E ε} {Γ : ContractSchema S X E ε} (w : World S X E) :
    coreRun Γ [] w = w := rfl

theorem coreRun_cons {S X E ε} {Γ : ContractSchema S X E ε}
    (ctx : Ctx) (f : FnDef) (args : List Nat) (rest : List (Ctx × FnDef × List Nat))
    (w : World S X E) :
    coreRun Γ ((ctx, f, args) :: rest) w =
    coreRun Γ rest
      { Security.worldAfter (Core.denote Γ f.core args.reverse) ctx w with log := [] } := rfl

theorem mkEvmState_halted (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).halted = none := rfl

theorem mkEvmState_immutable (cd σ κ ctx k) :
    (mkEvmState cd σ κ ctx).env.immutable k = 0 := rfl

theorem mkEvmState_storage (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).storage = σ := rfl

theorem mkEvmState_calldata (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).env.calldata = cd := rfl

theorem mkEvmState_keccak (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).env.keccakOf = κ := rfl

theorem mkEvmState_logs (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).logs = [] := rfl

theorem ctxRel_mkEvmState (cd : List UInt8) (σ : U256 → U256) (κ : List UInt8 → U256)
    (ctx : Ctx) (hwf : CtxWF ctx) (hcd : cd.length < wordBound) :
    ctxRel ctx (mkEvmState cd σ κ ctx) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, mkEvmState_halted cd σ κ ctx, hcd, hwf⟩
  simp [mkEvmState, EvmState.init]
  rfl

theorem logsRel_empty {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} {st : EvmState} (hlog : w.log = []) (hl : st.logs = []) :
    logsRel c Γ w st := by
  simp [logsRel, selfLogs, hlog, hl]

theorem R_mkEvmState {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    (κ : List UInt8 → U256) (w : World S X E) (cd σ ctx)
    (hs : storageRel c Γ κ w.self σ) (hlog : w.log = []) (hwf : WorldWF c Γ w) :
    R c Γ κ w (mkEvmState cd σ κ ctx) :=
  ⟨by simpa [mkEvmState_storage] using hs,
    logsRel_empty hlog (mkEvmState_logs cd σ κ ctx),
    mkEvmState_keccak cd σ κ ctx, hwf⟩

theorem WorldWF_log {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} (log' : List E) (h : WorldWF c Γ w) :
    WorldWF c Γ { w with log := log' } := by
  unfold WorldWF at h ⊢
  exact h

theorem WorldWF_of_self {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w w' : World S X E} (h : w.self = w'.self) (hwf : WorldWF c Γ w) :
    WorldWF c Γ w' := by
  unfold WorldWF at hwf ⊢
  intro i fd hfd
  simpa [h] using hwf i fd hfd

/-- One encoded call, starting from related storage: forward `EvmCallRun`. -/
theorem evmCallRun_fnCalldata {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (f : FnDef) (args : List Nat) (w : World S X E)
    (σ : U256 → U256)
    (hf : f ∈ c.functions) (hk : f.kind ≠ .constructor)
    (hlenA : args.length = f.params.length)
    (hW : ∀ n ∈ args, n < wordBound)
    (hctxWF : CtxWF ctx)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcd : (fnCalldata f args).length < wordBound) :
    let yst0 := mkEvmState (fnCalldata f args) σ evmKeccak ctx
    ∃ σ', EvmCallRun is yst0 σ' ∧
      (match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
        | .ok (_, w') => storageRel c Γ evmKeccak w'.self σ'
        | .error _ => σ' = σ) := by
  intro yst0
  have hsel : selectedFn c (fnCalldata f args) = some f :=
    selectedFn_fnCalldata c f args hf hnd hlenA
  have hdec : decodeArgs f (fnCalldata f args) = args :=
    decodeArgs_fnCalldata f args hk hlenA hW
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmState _ _ _ _ hctxWF hcd
  have hR : R c Γ evmKeccak w yst0 := R_mkEvmState evmKeccak w _ σ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmState_immutable _ _ _ _ k
  obtain ⟨σ', hRun, hpost⟩ :=
    evmCallRun_of_correct c Γ hΓ hκ hcf hctor hlen hbound rt hrt is hcomp
      ctx w yst0 hctx hR himm0
  refine ⟨σ', hRun, ?_⟩
  rw [← hdec]
  rw [mkEvmState_calldata] at hpost
  simp only [hsel] at hpost
  rw [mkEvmState_storage] at hpost
  exact hpost

/-- Forward transport of encoded Core calls. Env/log stripping: each step is run
from `{w with log := []}` Yul state; `σ'` tracks `.self` only. Converse is open. -/
theorem bytecode_trace_transport {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound) :
    ∃ σ', EvmTraceRun is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' ∧
      storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
      WorldWF c Γ (coreRun Γ calls { w with log := [] }) := by
  induction calls generalizing w σ with
  | nil =>
    refine ⟨σ, EvmTraceRun.nil σ, ?_, ?_⟩
    · simpa [coreRun] using hs
    · simpa [coreRun] using WorldWF_log [] hwf
  | cons p rest ih =>
    rcases p with ⟨ctx, f, args⟩
    have hp := hcalls ⟨ctx, f, args⟩ (List.mem_cons.mpr (Or.inl rfl))
    rcases hp with ⟨hf, hk, hlenA, hW, hctxWF, hcd⟩
    have hrest : ∀ q ∈ rest, _ := fun q hq =>
      hcalls q (List.mem_cons_of_mem _ hq)
    let yst0 := mkEvmState (fnCalldata f args) σ evmKeccak ctx
    obtain ⟨σ₁, h1, hpost⟩ :=
      evmCallRun_fnCalldata c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp
        ctx f args { w with log := [] } σ hf hk hlenA hW hctxWF (by simpa using hs) rfl
        (WorldWF_log [] hwf) hcd
    let w1 : World S X E :=
      let w' := Security.worldAfter (Core.denote Γ f.core args.reverse) ctx { w with log := [] }
      { w' with log := [] }
    have hs1 : storageRel c Γ evmKeccak w1.self σ₁ := by
      dsimp [w1]
      cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
      | ok prod =>
        rcases prod with ⟨_, w'⟩
        simp [Security.worldAfter, htx] at hpost ⊢
        exact hpost
      | error e =>
        simp [Security.worldAfter, htx] at hpost ⊢
        simpa [hpost] using hs
    have hwf1 : WorldWF c Γ w1 := by
      have hctx : ctxRel ctx yst0 := ctxRel_mkEvmState _ _ _ _ hctxWF hcd
      have hR : R c Γ evmKeccak { w with log := [] } yst0 :=
        R_mkEvmState evmKeccak _ _ σ ctx (by simpa using hs) rfl (WorldWF_log [] hwf)
      obtain ⟨stObs, _, hconcl⟩ :=
        runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound
          rt hrt ctx { w with log := [] } yst0 hctx hR
      have hsel : selectedFn c yst0.env.calldata = some f := by
        simpa [yst0, mkEvmState_calldata] using
          selectedFn_fnCalldata c f args hf hnd hlenA
      have hdec : decodeArgs f yst0.env.calldata = args := by
        simpa [yst0, mkEvmState_calldata] using decodeArgs_fnCalldata f args hk hlenA hW
      simp only [hsel, hdec] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
      | ok prod =>
        rcases prod with ⟨_, w'⟩
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, hR'⟩
        rcases hR' with ⟨_, _, _, hwf'⟩
        simpa [w1, Security.worldAfter, htx] using WorldWF_log [] hwf'
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, _, _, hR'⟩
        rcases hR' with ⟨_, _, _, hwf'⟩
        simpa [w1, Security.worldAfter, htx] using hwf'
    obtain ⟨σ', htl, hs', hwf'⟩ := ih w1 σ₁ hs1 rfl hwf1 hrest
    refine ⟨σ', EvmTraceRun.cons (yst0 := yst0)
        (mkEvmState_calldata _ _ _ _) (mkEvmState_storage _ _ _ _) h1 htl, ?_, ?_⟩
    · simpa [coreRun, w1] using hs'
    · simpa [coreRun, w1] using hwf'

/-- Universal transport: an `EvmTraceRunAll` post-storage is `storageRel` of `coreRun`.
Needs a matching start state at each call so `evmCallRun_eq_of_start` applies. -/
theorem bytecode_trace_all {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound)
    (hE : EvmTraceRunAll is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ') :
    storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
    WorldWF c Γ (coreRun Γ calls { w with log := [] }) := by
  induction calls generalizing w σ σ' with
  | nil =>
    cases hE
    refine ⟨?_, ?_⟩
    · simpa [coreRun] using hs
    · simpa [coreRun] using WorldWF_log [] hwf
  | cons p rest ih =>
    rcases p with ⟨ctx, f, args⟩
    have hp := hcalls ⟨ctx, f, args⟩ (List.mem_cons.mpr (Or.inl rfl))
    rcases hp with ⟨hf, hk, hlenA, hW, hctxWF, hcd⟩
    have hrest : ∀ q ∈ rest, _ := fun q hq =>
      hcalls q (List.mem_cons_of_mem _ hq)
    have hE' : EvmTraceRunAll is
        (⟨ctx, fnCalldata f args⟩ :: rest.map fun q => ⟨q.1, fnCalldata q.2.1 q.2.2⟩) σ σ' := by
      simpa using hE
    cases hE' with
    | cons hstart h1 htl =>
      let yst0 := mkEvmState (fnCalldata f args) σ evmKeccak ctx
      obtain ⟨σp, hRun, hpost⟩ :=
        evmCallRun_fnCalldata c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp
          ctx f args { w with log := [] } σ hf hk hlenA hW hctxWF (by simpa using hs) rfl
          (WorldWF_log [] hwf) hcd
      have heq := evmCallRun_eq_of_start h1 hRun hstart
      rw [heq] at htl
      let w1 : World S X E :=
        let w' := Security.worldAfter (Core.denote Γ f.core args.reverse) ctx { w with log := [] }
        { w' with log := [] }
      have hs1 : storageRel c Γ evmKeccak w1.self σp := by
        dsimp [w1]
        cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp [Security.worldAfter, htx] at hpost ⊢
          exact hpost
        | error e =>
          simp [Security.worldAfter, htx] at hpost ⊢
          simpa [hpost] using hs
      have hwf1 : WorldWF c Γ w1 := by
        have hctx : ctxRel ctx yst0 := ctxRel_mkEvmState _ _ _ _ hctxWF hcd
        have hR : R c Γ evmKeccak { w with log := [] } yst0 :=
          R_mkEvmState evmKeccak _ _ σ ctx (by simpa using hs) rfl (WorldWF_log [] hwf)
        obtain ⟨stObs, _, hconcl⟩ :=
          runtimeBlock_correct_callFree c Γ hΓ evmKeccak hκ hcf hctor hlen hbound
            rt hrt ctx { w with log := [] } yst0 hctx hR
        have hsel : selectedFn c yst0.env.calldata = some f := by
          simpa [yst0, mkEvmState_calldata] using
            selectedFn_fnCalldata c f args hf hnd hlenA
        have hdec : decodeArgs f yst0.env.calldata = args := by
          simpa [yst0, mkEvmState_calldata] using decodeArgs_fnCalldata f args hk hlenA hW
        simp only [hsel, hdec] at hconcl
        cases htx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with log := [] } with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp only [htx] at hconcl
          rcases hconcl with ⟨_, hR'⟩
          rcases hR' with ⟨_, _, _, hwf'⟩
          simpa [w1, Security.worldAfter, htx] using WorldWF_log [] hwf'
        | error e =>
          simp only [htx] at hconcl
          rcases hconcl with ⟨_, _, _, hR'⟩
          rcases hR' with ⟨_, _, _, hwf'⟩
          simpa [w1, Security.worldAfter, htx] using hwf'
      obtain ⟨hs', hwf'⟩ := ih w1 σp σ' hs1 rfl hwf1 hrest htl
      refine ⟨?_, ?_⟩
      · simpa [coreRun, w1] using hs'
      · simpa [coreRun, w1] using hwf'

end Lsc.Compiler

