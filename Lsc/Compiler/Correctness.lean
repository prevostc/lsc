import Lsc.Compiler.Yul
import Lsc.Compiler.Externals
import YulSemantics.BigStep
import YulSemantics.Observation
import Batteries.Data.List.Basic

/-!
# `toYulFn_correct` / `runtimeBlock_correct`

Stated against powdr `RunCommitted` (S1, closed `evm`) and `RunCommittedExt` (S2,
`yulD calls`). A Yul `revert` rolls back storage/logs, matching `Tx`'s `Except.error`.
S1 (call-free) is `toYulFn_correct_callFree` in `Proof/Core.lean`. S2 is backward:
every Yul run admitted by `Conforms` `calls` is predicted by Core under some fault
oracle (`ToYulFnCorrectExt` in this file; mini-fragment proof in `Proof/Call.lean`).
`runtimeBlock_correct` (dispatcher over `yulD`) is M3.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

/-- Context words fit in an EVM word. -/
def CtxWF (ctx : Ctx) : Prop :=
  let sender : Nat := ctx.sender
  let self : Nat := ctx.self
  sender < wordBound ∧ ctx.value < wordBound ∧ ctx.timestamp < wordBound ∧
    ctx.blockNumber < wordBound ∧ self < wordBound

/-- Context fields the Yul dialect exposes as `caller` / `callvalue` / `timestamp` /
`number` / `address`, plus a non-static unhalted frame. `calldata.length < 2^256` is an
EVM well-formedness fact: it makes `calldatasize` agree with `List.length`. -/
def ctxRel (ctx : Ctx) (st : EvmState) : Prop :=
  st.env.caller = BitVec.ofNat 256 ctx.sender ∧
  st.env.callvalue = BitVec.ofNat 256 ctx.value ∧
  st.env.timestamp = BitVec.ofNat 256 ctx.timestamp ∧
  st.env.number = BitVec.ofNat 256 ctx.blockNumber ∧
  st.env.address = BitVec.ofNat 256 ctx.self ∧
  st.env.static = false ∧
  st.halted = none ∧
  st.env.calldata.length < wordBound ∧
  CtxWF ctx

/-- Every Core local is a word. -/
def EnvWF (env : List Nat) : Prop := ∀ v ∈ env, v < wordBound

/-- `env[i] ↔ v_{d-1-i}`, innermost first. -/
def toVEnv (env : List Nat) : VEnv evm :=
  (List.zip env (List.range env.length)).map fun (x, i) =>
    (identV (env.length - 1 - i), BitVec.ofNat 256 x)

/-- ABI-decode `f`'s arguments from calldata (zero-padded, like `calldataload`). -/
def decodeArgs (f : FnDef) (cd : List UInt8) : List Nat :=
  let off := if f.kind = .constructor then 0 else 4
  (List.range f.params.length).map fun i => (wordFrom cd (off + 32 * i)).toNat

/-- First 4 bytes as `shr(224, calldataload(0))`. -/
def calldataSelector (cd : List UInt8) : Nat :=
  (wordFrom cd 0).toNat >>> 224

/-- Unique matching runtime entrypoint whose calldata is long enough for its parameters. -/
def selectedFn (c : ContractDef) (cd : List UInt8) : Option FnDef :=
  if cd.length < 4 then none
  else
    match c.functions.find? (fun f => f.selector = calldataSelector cd) with
    | none => none
    | some f =>
      if cd.length < 4 + 32 * f.params.length then none else some f

/-- Storage values (and mapping keys) used by `R` fit in an EVM word. -/
def WorldWF {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε) (w : World S X E) : Prop :=
  ∀ (i : Nat) (fd : FieldDef), c.fields[i]? = some fd →
    match fd.kind with
    | .scalar => Γ.st.scalar i w.self < wordBound
    | .map1 => ∀ k, k < wordBound → Γ.st.map1 i w.self k < wordBound
    | .map2 => ∀ k₁ k₂, k₁ < wordBound → k₂ < wordBound →
        Γ.st.map2 i w.self k₁ k₂ < wordBound

/-- TCB: keccak images of mapping keys are distinct from scalar slots and from each other. -/
structure KeccakSep (c : ContractDef) (κ : List UInt8 → U256) : Prop where
  map1_ne_scalar : ∀ {f k i : Nat},
    f < c.fields.length → i < c.fields.length → k < wordBound →
    (c.fields[f]?).map (·.kind) = some .map1 →
    (c.fields[i]?).map (·.kind) = some .scalar →
    mapSlot1 κ f k ≠ BitVec.ofNat 256 i
  map1_inj : ∀ {f₁ k₁ f₂ k₂ : Nat},
    f₁ < c.fields.length → f₂ < c.fields.length →
    k₁ < wordBound → k₂ < wordBound →
    (c.fields[f₁]?).map (·.kind) = some .map1 →
    (c.fields[f₂]?).map (·.kind) = some .map1 →
    mapSlot1 κ f₁ k₁ = mapSlot1 κ f₂ k₂ → f₁ = f₂ ∧ k₁ = k₂
  map2_ne_scalar : ∀ {f k₁ k₂ i : Nat},
    f < c.fields.length → i < c.fields.length →
    k₁ < wordBound → k₂ < wordBound →
    (c.fields[f]?).map (·.kind) = some .map2 →
    (c.fields[i]?).map (·.kind) = some .scalar →
    mapSlot2 κ f k₁ k₂ ≠ BitVec.ofNat 256 i
  map2_ne_map1 : ∀ {f₂ k₁ k₂ f₁ k : Nat},
    f₂ < c.fields.length → f₁ < c.fields.length →
    k₁ < wordBound → k₂ < wordBound → k < wordBound →
    (c.fields[f₂]?).map (·.kind) = some .map2 →
    (c.fields[f₁]?).map (·.kind) = some .map1 →
    mapSlot2 κ f₂ k₁ k₂ ≠ mapSlot1 κ f₁ k
  map2_inj : ∀ {f a₁ a₂ g b₁ b₂ : Nat},
    f < c.fields.length → g < c.fields.length →
    a₁ < wordBound → a₂ < wordBound → b₁ < wordBound → b₂ < wordBound →
    (c.fields[f]?).map (·.kind) = some .map2 →
    (c.fields[g]?).map (·.kind) = some .map2 →
    mapSlot2 κ f a₁ a₂ = mapSlot2 κ g b₁ b₂ → f = g ∧ a₁ = b₁ ∧ a₂ = b₂

/-- Storage layout: scalar field `i` is slot `i`; mappings use Solidity `keccak256(key ‖ slot)`
(and nested keccak for `map2`). Map clauses quantify only over keys `< 2^256`. -/
def storageRel {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (keccak : List UInt8 → U256) (σ : S) (storage : U256 → U256) : Prop :=
  ∀ (i : Nat) (fd : FieldDef), c.fields[i]? = some fd →
    match fd.kind with
    | .scalar => storage (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Γ.st.scalar i σ)
    | .map1 => ∀ k, k < wordBound →
        storage (mapSlot1 keccak i k) = BitVec.ofNat 256 (Γ.st.map1 i σ k)
    | .map2 => ∀ k₁ k₂, k₁ < wordBound → k₂ < wordBound →
        storage (mapSlot2 keccak i k₁ k₂) = BitVec.ofNat 256 (Γ.st.map2 i σ k₁ k₂)

/-- Logs this frame emitted (address = `st.env.address`). Token `Transfer` logs land in
`st.logs` via `finishCall` and must not be related to `w.log`. -/
def selfLogs (st : EvmState) : List LogEntry :=
  st.logs.filter (fun l => l.address = st.env.address)

/-- Logs related in order: each Core event is some `Γ.ev.build i args` with matching ABI data,
compared against `st.logs` **filtered by `st.env.address`**. -/
def logsRel {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (w : World S X E) (st : EvmState) : Prop :=
  List.Forall₂ (fun ev l =>
      ∃ i args, ev = Γ.ev.build i args ∧ ∃ hi : i < c.events.length,
        l = LogEntry.mk st.env.address
          [BitVec.ofNat 256 (c.events[i]).topic0] (abiBytes args))
    w.log (selfLogs st)

/-- Layout relation `R : World S X E → EvmState → Prop`. Ghost/`faults` are not in `R`. -/
def R {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (keccak : List UInt8 → U256) (w : World S X E) (st : EvmState) : Prop :=
  storageRel c Γ keccak w.self st.storage ∧
  logsRel c Γ w st ∧
  st.env.keccakOf = keccak ∧
  WorldWF c Γ w

def haltSuccess (t : RetTy) (v : t.denote) (h : Option (HaltKind × List UInt8)) : Prop :=
  if t = .unit then h = some (.stop, [])
  else h = some (.ret, abiBytes (retWords (t := t) v))

def haltError {S X E ε : Type} (c : ContractDef) (Γ : ContractSchema S X E ε) :
    Err ε → List UInt8 → Prop
  | .arith a, bytes => bytes = panicBytes (arithPanicCode a)
  | .user e, bytes => ∃ i args, e = Γ.err.build i args ∧ bytes = customErrorBytes c i args
  | .callFailed, bytes => bytes = []

/-- Reducible alias of the `toYulFn_correct` conclusion, so per-function restatements
are defeq to the general theorem (`RetTy.unit.denote` unfolds with `f.ret`). -/
@[reducible] def ToYulFnCorrect {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256) (f : FnDef)
    (yul : YBlock) (ctx : Ctx) (w : World S X E) (st0 : EvmState) : Prop :=
  let args := decodeArgs f st0.env.calldata
  match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | .ok (v, w') =>
      ∃ stObs,
        RunCommitted yul st0 [] stObs .halt ∧
        haltSuccess f.ret v stObs.halted ∧
        R c Γ κ w' stObs
  | .error e =>
      ∃ stObs bytes,
        RunCommitted yul st0 [] stObs .halt ∧
        stObs.halted = some (.revert, bytes) ∧
        haltError c Γ e bytes ∧
        R c Γ κ w stObs

/-- Observed run on the S2 dialect. Never `RunCommitted.det` (`evmWithExternal` is
nondeterministic). -/
def RunCommittedExt (calls : ExternalCalls) (prog : YBlock) (st0 : EvmState)
    (V' : VEnv (yulD calls)) (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run (yulD calls) prog st0 V' st' o ∧ stObs = committedState st0 st'

/-- Backward simulation: every Yul run admitted by `calls` is predicted by Core
under some fault oracle `fo` (`w` with `faults := fo`). Success ⇒ `haltSuccess` ∧
`R w' stObs` ∧ `RX α w' stObs`; error ⇒ revert ∧ `haltError` ∧ `R w stObs`.
`Realizes` is not a hypothesis. -/
@[reducible] def ToYulFnCorrectExt {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (f : FnDef) (yul : YBlock)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) yul st0 [] st' o →
      ∃ fo : Nat → Bool,
        let wfo : World S X E := { w with faults := fo }
        let stObs := committedState st0 st'
        match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
            ctx wfo with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
              R c Γ κ w' stObs ∧ RX α bind w' stObs
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
              haltError c Γ e bytes ∧ R c Γ κ w stObs

/-- S1 (call-free, forward) is `toYulFn_correct_callFree`. S2 (backward, `yulD calls`)
is `ToYulFnCorrectExt` here; the mini-fragment proof belongs in `Proof/Call.lean` (import
cycle: `Call` may import `Core`, not the reverse). Dispatcher over `yulD` is M3. -/
theorem runtimeBlock_correct {S X E ε : Type} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    ∃ stObs, RunCommitted yul st0 [] stObs .halt ∧
      match selectedFn c st0.env.calldata with
      | none => stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
      | some f =>
        let args := decodeArgs f st0.env.calldata
        match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
        | .ok (v, w') => haltSuccess f.ret v stObs.halted ∧ R c Γ κ w' stObs
        | .error e =>
          ∃ bytes, stObs.halted = some (.revert, bytes) ∧
            haltError c Γ e bytes ∧ R c Γ κ w stObs := by
  -- TODO(S2): letCall
  sorry

end Lsc.Compiler
