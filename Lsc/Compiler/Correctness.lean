import Lsc.Compiler.Yul
import YulSemantics.Observation

/-!
# `toYul_correct` (call-free fragment)

Stated against powdr `RunCommitted` so a Yul `revert` rolls back storage/logs, matching
`Tx`'s `Except.error`. Proof is S1 work; this file is not imported from `Lsc.lean` or
`Checks.lean`.

-- TODO(S1): proof
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

/-- Context fields the Yul dialect exposes as `caller` / `callvalue` / `timestamp` /
`number` / `address`. -/
def ctxRel (ctx : Ctx) (st : EvmState) : Prop :=
  st.env.caller = BitVec.ofNat 256 ctx.sender ∧
  st.env.callvalue = BitVec.ofNat 256 ctx.value ∧
  st.env.timestamp = BitVec.ofNat 256 ctx.timestamp ∧
  st.env.number = BitVec.ofNat 256 ctx.blockNumber ∧
  st.env.address = BitVec.ofNat 256 ctx.self

/-- Calldata layout expected by `toYulFn`: runtime functions skip a 4-byte selector
prefix; constructors encode arguments at offset 0. `args` is ABI order (first param first);
`Core.denote` takes the reverse. -/
def calldataRel (f : FnDef) (args : List Nat) (st : EvmState) : Prop :=
  args.length = f.params.length ∧
  st.env.calldata =
    if f.kind = .constructor then ctorCalldata args else fnCalldata f args

/-- Storage layout: scalar field `i` is slot `i`; mappings use Solidity `keccak256(key ‖ slot)`
(and nested keccak for `map2`). Distinctness of keccak images from scalar slots is TCB. -/
def storageRel {S E ε} (c : ContractDef) (Γ : ContractSchema S E ε)
    (keccak : List UInt8 → U256) (σ : S) (storage : U256 → U256) : Prop :=
  ∀ (i : Nat) (fd : FieldDef), c.fields[i]? = some fd →
    match fd.kind with
    | .scalar => storage (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Γ.st.scalar i σ)
    | .map1 => ∀ k, storage (mapSlot1 keccak i k) = BitVec.ofNat 256 (Γ.st.map1 i σ k)
    | .map2 => ∀ k₁ k₂,
        storage (mapSlot2 keccak i k₁ k₂) = BitVec.ofNat 256 (Γ.st.map2 i σ k₁ k₂)

/-- Logs: same length as `w.log`, emitted from `address()`, in order.
Full ABI-data agreement needs an inverse of `Γ.ev.build` (event index + args); that
strengthening is left to the proof. -/
def logRel (wLogLen : Nat) (st : EvmState) : Prop :=
  st.logs.length = wLogLen ∧
  ∀ l ∈ st.logs, l.address = st.env.address

/-- Layout relation `R : World S E → EvmState → Prop` (plus the keccak oracle and schema
needed to read slots). -/
def R {S E ε} (c : ContractDef) (Γ : ContractSchema S E ε)
    (keccak : List UInt8 → U256) (w : World S E) (st : EvmState) : Prop :=
  storageRel c Γ keccak w.self st.storage ∧
  logRel w.log.length st ∧
  st.env.keccakOf = keccak

def haltSuccess (t : RetTy) (v : t.denote) (h : Option (HaltKind × List UInt8)) : Prop :=
  if t = .unit then h = some (.stop, [])
  else h = some (.ret, abiBytes (retWords (t := t) v))

def haltError (c : ContractDef) {ε : Type} : Err ε → List UInt8 → Prop
  | .arith a, bytes => bytes = panicBytes (arithPanicCode a)
  | .user _, bytes => ∃ i args, bytes = customErrorBytes c i args

/-- If `Tx.run (Core.denote … f) = .ok (v, w')`, a `RunCommitted` of `toYulFn c f` from a
related state halts with `.ret` (or `stop` for unit) and ABI bytes of `v`, and the
final observed state is related to `w'`. If it reverts with `e`, the run halts with
`.revert` and the Panic/custom-error bytes, observed state related to the pre-world `w`. -/
theorem toYul_correct {S E ε : Type} (c : ContractDef) (Γ : ContractSchema S E ε)
    (f : FnDef) (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S E) (st0 : EvmState) (args : List Nat)
    (hctx : ctxRel ctx st0) (hcd : calldataRel f args st0)
    (hR : R c Γ keccakOf w st0) :
    match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
    | .ok (v, w') =>
        ∃ V' stObs,
          RunCommitted yul st0 V' stObs .halt ∧
          haltSuccess f.ret v stObs.halted ∧
          R c Γ keccakOf w' stObs
    | .error e =>
        ∃ V' stObs bytes,
          RunCommitted yul st0 V' stObs .halt ∧
          stObs.halted = some (.revert, bytes) ∧
          haltError c e bytes ∧
          R c Γ keccakOf w stObs := by
  -- TODO(S1): proof
  sorry

end Lsc.Compiler
