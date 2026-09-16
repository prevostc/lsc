import Lsc.Compiler.EndToEnd
import Lsc.Compiler.Proof.EndToEndProof

set_option linter.unusedVariables false

/-!
Call-free bytecode: compiled runtime related to the high-level model by
the dispatcher, and to EVM steps by the pinned Yul-to-EVM compiler.

Also the `EvmCallRun` / `mkEvmState` framing lemmas and forward
`bytecode_trace_transport`. Shared assumptions: the compiler accepted the
contract, the layout is lawful, keccak keys do not collide, there are no
CALLs, constructors are excluded, and the frame has enough gas.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.MemorySpillStateSound
open EvmSemantics.EVM (State Steps)

/-- Converting a Yul word to an EVM word and back is the identity. -/
theorem ofConv_conv (v : U256) : ofConv (conv v) = v :=
  Proof.ofConv_conv v

/-- Committed observation keeps the Yul halt payload. -/
theorem committedState_halted (st0 st' : EvmState) :
    (committedState st0 st').halted = st'.halted :=
  Proof.committedState_halted st0 st'

/-- Yul storage recovered from a matching EVM account is the Yul map. -/
theorem storage_eq_account {yst : EvmState} {s : State} (hm : StateMatch yst s) :
    accountYulStorage s = yst.storage :=
  Proof.storage_eq_account hm

/-- `storageRel` on Yul storage is `storageRel'` on a matching EVM account. -/
theorem storageRel_account {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ σ} {yst : EvmState} {s : State}
    (hs : storageRel c Γ κ σ yst.storage) (hm : StateMatch yst s) :
    storageRel' c Γ κ σ s :=
  Proof.storageRel_account hs hm

/-- A successful Yul halt related by `HaltedMatch` is an EVM `haltOK`. -/
theorem haltOK_of_success {t : RetTy} {v : t.denote} {yst : EvmState} {s : State}
    (hs : haltSuccess t v yst.halted) (hHM : HaltedMatch yst s) : haltOK t v s :=
  Proof.haltOK_of_success hs hHM

/-- A Yul revert related by `HaltedMatch` is an EVM revert with the same bytes. -/
theorem reverted_of_halted {yst : EvmState} {s : State} {bytes : List UInt8}
    (h : yst.halted = some (.revert, bytes)) (hHM : HaltedMatch yst s) :
    s.halt = .Reverted ∧ s.hReturn.toList = bytes :=
  Proof.reverted_of_halted h hHM

/-- A committing halt makes the committed observation the post-state. -/
theorem obs_eq_of_commit {st0 st' stObs : EvmState} {k : HaltKind} {bs : List UInt8}
    (hobs : stObs = committedState st0 st')
    (hhalted : stObs.halted = st'.halted)
    (hh : stObs.halted = some (k, bs)) (hk : k.commits = true) :
    stObs = st' :=
  Proof.obs_eq_of_commit hobs hhalted hh hk

/-- A revert restores pre-state storage in the committed observation. -/
theorem obs_storage_rollback {st0 st' stObs : EvmState} {bytes : List UInt8}
    (hobs : stObs = committedState st0 st')
    (hhalted : stObs.halted = st'.halted)
    (hh : stObs.halted = some (.revert, bytes)) :
    stObs.storage = st0.storage :=
  Proof.obs_storage_rollback hobs hhalted hh

/-- `HaltMatch` implies the EVM frame is not still running. -/
theorem halt_ne_running_of_HaltMatch {hk : YulSemantics.EVM.HaltKind × List UInt8}
    {s : State} (h : HaltMatch hk s) : s.halt ≠ .Running :=
  Proof.halt_ne_running_of_HaltMatch h

/-- A related halted Yul frame with an empty call stack is EVM-halted. -/
theorem Halted_of_HaltedMatch {yst : EvmState} {s : State}
    (h : HaltedMatch yst s) (hcs : s.callStack = []) : Halted s :=
  Proof.Halted_of_HaltedMatch h hcs

/-- A compiler outcome that is stop or halt yields an EVM-halted frame. -/
theorem Halted_of_compile_out {s' : State} {yst' : EvmState} {o : Outcome}
    (hcs : s'.callStack = [])
    (hOut : (o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
            (o = .halt ∧ HaltedMatch yst' s')) : Halted s' :=
  Proof.Halted_of_compile_out hcs hOut

/-- Observable post-storage on revert is the pre-state Yul storage. -/
theorem postStorage_reverted {yst0 s'} (h : s'.halt = .Reverted) :
    postStorage yst0 s' = yst0.storage :=
  Proof.postStorage_reverted h

/-- Observable post-storage on a non-revert is the account Yul storage. -/
theorem postStorage_commit {yst0 s'} (h : s'.halt ≠ .Reverted) :
    postStorage yst0 s' = accountYulStorage s' :=
  Proof.postStorage_commit h

/-- Observable foreign storage on revert is the pre-state map. -/
theorem postForeign_reverted {yst0 s'} (h : s'.halt = .Reverted) :
    postForeign yst0 s' = evmForeign yst0 :=
  Proof.postForeign_reverted h

/-- Observable foreign storage on a non-revert is the account map. -/
theorem postForeign_commit {yst0 s'} (h : s'.halt ≠ .Reverted) :
    postForeign yst0 s' = accountForeign s' :=
  Proof.postForeign_commit h

/-- Foreign storage recovered from a matching EVM state is `evmForeign`. -/
theorem foreign_eq_account {yst : EvmState} {s : State} (hm : StateMatch yst s) :
    accountForeign s = evmForeign yst :=
  Proof.foreign_eq_account hm

/-- A revert restores pre-state foreign storage in the observation. -/
theorem obs_foreign_rollback {st0 st' stObs : EvmState} {bytes : List UInt8}
    (hobs : stObs = committedState st0 st')
    (hhalted : stObs.halted = st'.halted)
    (hh : stObs.halted = some (.revert, bytes)) :
    evmForeign stObs = evmForeign st0 :=
  Proof.obs_foreign_rollback hobs hhalted hh

/-- `setGas` writes `gasAvailable`. -/
@[simp]
theorem setGas_gas (s g) : (setGas s g).gasAvailable = g :=
  Proof.setGas_gas s g

/-- `setGas` does not change the program counter. -/
@[simp]
theorem setGas_pc (s g) : (setGas s g).pc = s.pc :=
  Proof.setGas_pc s g

/-- `setGas` does not change the stack. -/
@[simp]
theorem setGas_stack (s g) : (setGas s g).stack = s.stack :=
  Proof.setGas_stack s g

/-- `setGas` preserves `FrameOK`. -/
theorem frameOK_setGas {code s g} (h : FrameOK code s) : FrameOK code (setGas s g) :=
  Proof.frameOK_setGas h

/-- `setGas` preserves `StateMatch`. -/
theorem stateMatch_setGas {yst s g} (h : StateMatch yst s) :
    StateMatch yst (setGas s g) :=
  Proof.stateMatch_setGas h

/-- `setGas` preserves `EvmStartOK`. -/
theorem evmStartOK_setGas {is yst0 s0 g} (h : EvmStartOK is yst0 s0) :
    EvmStartOK is yst0 (setGas s0 g) :=
  Proof.evmStartOK_setGas h

/-- Two `EvmCallRun`s of the same start state agree on post-storage. -/
theorem evmCallRun_eq_of_start {is yst0 σ1 σ2 s0}
    (h1 : EvmCallRun is yst0 σ1) (h2 : EvmCallRun is yst0 σ2)
    (hs : EvmStartOK is yst0 s0) : σ1 = σ2 :=
  Proof.evmCallRun_eq_of_start h1 h2 hs

/-- An `EvmCallRunξ` is an `EvmCallRun` of the same post-storage. -/
theorem EvmCallRun_of_ξ {is yst0 σ' ξ'} (h : EvmCallRunξ is yst0 σ' ξ') :
    EvmCallRun is yst0 σ' :=
  Proof.EvmCallRun_of_ξ h

/-- Two `EvmCallRunξ`s of the same start state agree on storage maps. -/
theorem evmCallRunξ_eq_of_start {is yst0 σ1 ξ1 σ2 ξ2 s0}
    (h1 : EvmCallRunξ is yst0 σ1 ξ1) (h2 : EvmCallRunξ is yst0 σ2 ξ2)
    (hs : EvmStartOK is yst0 s0) : σ1 = σ2 ∧ ξ1 = ξ2 :=
  Proof.evmCallRunξ_eq_of_start h1 h2 hs

/-- A `Run` of the memoryguard-erased runtime matches the successful
`compileBlock` branch: erase, or powdr spill with `GuardedRunOfErased`. -/
theorem runtimeSrc_of_erased {c : ContractDef} {rt : YBlock} {is : List Instr}
    {yst0 yst' : EvmState} {o : Outcome}
    (hrt : runtimeBlock c = some rt)
    (hcomp : compileBlock rt = some is)
    (hrun : Run (evmWithExternal ExternalCalls.none ExternalCreates.none ExternalGas.any)
      (eraseMemoryGuardStmts rt) yst0 [] yst' o) :
    RuntimeCompileSrc (model := closedModel) rt is yst0 yst' o :=
  Proof.runtimeSrc_of_erased hrt hcomp hrun

/-- Erase and spill post-states agree on storage and halt. -/
theorem ystF_agree {b : YBlock} {is : List Instr} {yst' ystF : EvmState}
    (hcomp : compileBlock b = some is)
    (hFe : compileErased b = some is → ystF = yst')
    (hFs : ∀ r, compileErased b = none → spillRuntime? b = some r →
      ScratchRel r.base r.reserved yst' ystF) :
    ystF.storage = yst'.storage ∧ ystF.halted = yst'.halted :=
  Proof.ystF_agree hcomp hFe hFs

/-- Erase and spill post-states agree on foreign storage. -/
theorem ystF_foreign {b : YBlock} {is : List Instr} {yst' ystF : EvmState}
    (hcomp : compileBlock b = some is)
    (hFe : compileErased b = some is → ystF = yst')
    (hFs : ∀ r, compileErased b = none → spillRuntime? b = some r →
      ScratchRel r.base r.reserved yst' ystF) :
    evmForeign ystF = evmForeign yst' :=
  Proof.ystF_foreign hcomp hFe hFs

/-- `HaltedMatch` transports along equal Yul halt payloads. -/
theorem HaltedMatch_of_ystF {yst' ystF : EvmState} {s' : State}
    (hHM : HaltedMatch ystF s') (hh : ystF.halted = yst'.halted) :
    HaltedMatch yst' s' :=
  Proof.HaltedMatch_of_ystF hHM hh

/-- A correct call-free runtime yields a unique halted EVM post-storage. -/
theorem evmCallRun_of_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) (hLock : LockFree yst0) :
    ∃ σ', EvmCallRun is yst0 σ' ∧
      match dispatchedFn c yst0.env.calldata ctx.value with
      | none => σ' = yst0.storage
      | some f =>
        if f.payable && yst0.env.selfBalance.ult yst0.env.callvalue then
          σ' = yst0.storage
        else
          match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
          | .ok (_, w') => storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w'
          | .error _ => σ' = yst0.storage :=
  Proof.evmCallRun_of_correct c Γ hΓ hκ hcf hctor hlen hbound rt hrt is hcomp ctx w yst0 hctx hR himm0 hLock

/-- The empty encoded-call fold is the identity on worlds. -/
theorem coreRun_nil {S X E ε} {Γ : ContractSchema S X E ε} (w : World S X E) :
    coreRun Γ [] w = w :=
  Proof.coreRun_nil w

/-- `coreRun` peels one encoded call, clearing logs after `worldAfter`. -/
theorem coreRun_cons {S X E ε} {Γ : ContractSchema S X E ε}
    (ctx : Ctx) (f : FnDef) (args : List Nat) (rest : List (Ctx × FnDef × List Nat))
    (w : World S X E) :
    coreRun Γ ((ctx, f, args) :: rest) w =
    coreRun Γ rest
      { Security.worldAfter (Core.denote Γ f.core args.reverse) ctx w with log := [] } :=
  Proof.coreRun_cons ctx f args rest w

/-- `mkEvmState` starts unhalted. -/
theorem mkEvmState_halted (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).halted = none :=
  Proof.mkEvmState_halted cd σ κ ctx

/-- `mkEvmState` has zero immutables. -/
theorem mkEvmState_immutable (cd σ κ ctx k) :
    (mkEvmState cd σ κ ctx).env.immutable k = 0 :=
  Proof.mkEvmState_immutable cd σ κ ctx k

/-- `mkEvmState` installs the given storage map. -/
theorem mkEvmState_storage (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).storage = σ :=
  Proof.mkEvmState_storage cd σ κ ctx

/-- `mkEvmState` installs the given calldata. -/
theorem mkEvmState_calldata (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).env.calldata = cd :=
  Proof.mkEvmState_calldata cd σ κ ctx

/-- `mkEvmState` sets `selfBalance` equal to `callvalue`, so the payable wrap
check never fires in the transport skeleton. -/
theorem mkEvmState_selfBalance_ult_callvalue (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).env.selfBalance.ult
      (mkEvmState cd σ κ ctx).env.callvalue = false :=
  Proof.mkEvmState_selfBalance_ult_callvalue cd σ κ ctx

/-- `mkEvmState` installs the given keccak oracle. -/
theorem mkEvmState_keccak (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).env.keccakOf = κ :=
  Proof.mkEvmState_keccak cd σ κ ctx

/-- `mkEvmState` starts with empty logs. -/
theorem mkEvmState_logs (cd σ κ ctx) :
    (mkEvmState cd σ κ ctx).logs = [] :=
  Proof.mkEvmState_logs cd σ κ ctx

/-- A well-formed context is related to its `mkEvmState`. -/
theorem ctxRel_mkEvmState (cd : List UInt8) (σ : U256 → U256) (κ : List UInt8 → U256)
    (ctx : Ctx) (hwf : CtxWF ctx) (hcd : cd.length < wordBound) :
    ctxRel ctx (mkEvmState cd σ κ ctx) :=
  Proof.ctxRel_mkEvmState cd σ κ ctx hwf hcd

/-- Empty Core logs relate to empty EVM logs. -/
theorem logsRel_empty {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} {st : EvmState} (hlog : w.log = []) (hl : st.logs = []) :
    logsRel c Γ w st :=
  Proof.logsRel_empty hlog hl

/-- Related storage and empty logs give `R` at `mkEvmState`. -/
theorem R_mkEvmState {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    (κ : List UInt8 → U256) (w : World S X E) (cd σ ctx)
    (hs : storageRel c Γ κ w.self σ) (hlog : w.log = []) (hwf : WorldWF c Γ w) :
    R c Γ κ w (mkEvmState cd σ κ ctx) :=
  Proof.R_mkEvmState κ w cd σ ctx hs hlog hwf

/-- `mkEvmState` is `mkEvmStateExt` with zero foreign storage. -/
theorem mkEvmState_eq_ext (cd σ κ ctx) :
    mkEvmState cd σ κ ctx = mkEvmStateExt cd σ (fun _ _ => 0) κ ctx :=
  Proof.mkEvmState_eq_ext cd σ κ ctx

/-- A well-formed context is related to its `mkEvmStateExt`. -/
theorem ctxRel_mkEvmStateExt (cd : List UInt8) (σ : U256 → U256) (ξ : Foreign)
    (κ : List UInt8 → U256) (ctx : Ctx) (hwf : CtxWF ctx) (hcd : cd.length < wordBound) :
    ctxRel ctx (mkEvmStateExt cd σ ξ κ ctx) :=
  Proof.ctxRel_mkEvmStateExt cd σ ξ κ ctx hwf hcd

/-- Related storage and empty logs give `R` at `mkEvmStateExt`. -/
theorem R_mkEvmStateExt {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    (κ : List UInt8 → U256) (w : World S X E) (cd σ ξ ctx)
    (hs : storageRel c Γ κ w.self σ) (hlog : w.log = []) (hwf : WorldWF c Γ w) :
    R c Γ κ w (mkEvmStateExt cd σ ξ κ ctx) :=
  Proof.R_mkEvmStateExt κ w cd σ ξ ctx hs hlog hwf

/-- `WorldWF` ignores the log field. -/
theorem WorldWF_log {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} (log' : List E) (h : WorldWF c Γ w) :
    WorldWF c Γ { w with log := log' } :=
  Proof.WorldWF_log log' h

/-- `WorldWF` depends only on storage. -/
theorem WorldWF_of_self {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w w' : World S X E} (h : w.self = w'.self) (hwf : WorldWF c Γ w) :
    WorldWF c Γ w' :=
  Proof.WorldWF_of_self h hwf

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
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (f : FnDef) (args : List Nat) (w : World S X E)
    (σ : U256 → U256)
    (hf : f ∈ c.functions) (hk : f.kind ≠ .constructor)
    (hlenA : args.length = f.params.length)
    (hW : ∀ n ∈ args, n < wordBound)
    (hctxWF : CtxWF ctx)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcd : (fnCalldata f args).length < wordBound)
    (hvo : valueOk f ctx.value) :
    let yst0 := mkEvmState (fnCalldata f args) σ evmKeccak ctx
    ∃ σ', EvmCallRun is yst0 σ' ∧
      (match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
        | .ok (_, w') => storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w'
        | .error _ => σ' = σ) :=
  Proof.evmCallRun_fnCalldata c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp ctx f args w σ hf hk hlenA hW hctxWF hs hlog hwf hcd hvo

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
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound ∧
        valueOk p.2.1 p.1.value) :
    ∃ σ', EvmTraceRun is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ' ∧
      storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
      WorldWF c Γ (coreRun Γ calls { w with log := [] }) :=
  Proof.bytecode_trace_transport c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp calls w σ hs hlog hwf hcalls

/-- A compiled call-free runtime, started from a matching EVM frame with
enough gas, ends in a halt whose return data and storage are those of
the high-level model on the selected function — or an empty revert if
the selector is unknown. The compiler must have accepted the contract
(`compileBlock`: erase or powdr spill); there are no CALLs; constructors
are excluded. This is the step that
carries a call-free Yul run down to bytecode; Token's anti-extraction
theorems instantiate it. -/
theorem bytecode_call_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (himm0 : ∀ k, yst0.env.immutable k = 0) (hLock : LockFree yst0) :
    BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is :=
  Proof.bytecode_call_correct c Γ hΓ hκ hcf hctor hlen hbound rt hrt is hcomp
    ctx w yst0 hctx hR himm0 hLock

/-- After any halted sequence of well-formed EVM calls against compiled
call-free runtime, the ending storage is exactly the storage the
high-level model predicts for those calls, and stored values still fit
in a word. Each hop needs a matching start state so halted runs are
unique; without that, two EVM runs of the same bytecode could disagree.
Unknown selectors are not in this statement — it is about decoded
functions. Token uses this to move a Core-level claim from start
storage to end storage. -/
theorem bytecode_trace_all {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (calls : List (Ctx × FnDef × List Nat))
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcalls : ∀ p ∈ calls,
        p.2.1 ∈ c.functions ∧ p.2.1.kind ≠ .constructor ∧
        p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
        CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound ∧
        valueOk p.2.1 p.1.value)
    (hE : EvmTraceRunAll is (calls.map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ σ') :
    storageRel c Γ evmKeccak (coreRun Γ calls { w with log := [] }).self σ' ∧
    WorldWF c Γ (coreRun Γ calls { w with log := [] }) :=
  Proof.bytecode_trace_all c Γ hΓ hκ hcf hctor hlen hbound hnd rt hrt is hcomp
    calls w σ σ' hs hlog hwf hcalls hE

end Lsc.Compiler
