import Lsc.Lang.Interface
import Lsc.Compiler.Yul
import YulSemantics.Dialect.EVM
import YulSemantics.Observation

/-!
# External-call glue (`Conforms`, `NoInterfere`, `RX`, `Realizes`)

Lives in `Compiler`, never in `Lang`. `Security.run` does not see `ExternalCalls`.
`α` is a parameter: foreign ERC20 layout is not ours. `X` stays in `w.ext`; `RX` is
not a field of `R`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

/-- S2 dialect: relational `ExternalCalls`, no creates, no `gas()`.
Bytecode glue must instantiate powdr `ExternalModel` with `gas := .none`
(the class default is `.any`) so the dialect equals `yulD`. -/
@[reducible] def yulD (calls : ExternalCalls) : Dialect :=
  evmWithExternal calls .none .none

/-- Abstraction of a ghost `G` from an EVM/`CallWorld` snapshot at a callee address.
`ofState` / `ofWorld` agree on the `CallWorld` projection (they ignore memory,
returndata, halt, and callee logs). -/
structure Abs (G : Type) where
  ofState : EvmState → Address → G
  ofWorld : CallWorld → Address → G
  ofState_proj : ∀ st a, ofState st a = ofWorld (CallWorld.ofState st) a
  ofWorld_install : ∀ world st a,
    ofWorld (CallWorld.ofState (world.install st)) a = ofWorld world a

/-- Our storage/transient and ETH balances are unchanged (`value = 0`); other
addresses' ghosts are unchanged. Token logs are allowed (`world.logs` is free). -/
def NoInterfere {G} (α : Abs G) (st : EvmState) (world : CallWorld)
    (callee : Address) : Prop :=
  world.storage = st.storage ∧
  world.transient = st.transient ∧
  world.selfBalance = st.env.selfBalance ∧
  world.balanceOf = st.env.balanceOf ∧
  (∀ l ∈ world.logs, l.address ≠ st.env.address) ∧
  ∀ a : Address, a ≠ callee → α.ofWorld world a = α.ofState st a

/-- Decode ABI return data. `boolOpt` treats a short (1–31 byte) or ABI-false
word as **not** a success (so Core `some 1` cannot pair with a Yul revert).
`length < 2^256` so `returndatasize` agrees with `List.length` (`ofNat` would wrap). -/
def decodeRet : AbiRet → List UInt8 → Nat → Prop
  | .boolOpt, bs, v =>
      v = 1 ∧ bs.length < wordBound ∧
      (bs.length = 0 ∨ (32 ≤ bs.length ∧ wordFrom bs 0 = BitVec.ofNat 256 1))
  | .word, bs, v =>
      32 ≤ bs.length ∧ bs.length < wordBound ∧ (wordFrom bs 0).toNat = v
  | .none, _, _ => True

def abiInput (spec : AbiSpec) (args : List Nat) : List UInt8 :=
  selectorBytes spec.selector ++ args.flatMap wordBytes

/-- Ghost at a bound address agrees with `w.ext`. Not a field of `R`. -/
def RX {I : Interface} {S X E} (α : Abs I.Ghost) (b : Binding I S X)
    (w : World S X E) (st : EvmState) : Prop :=
  α.ofState st (b.addr w.self) = b.get w.ext

/-- Foreign ghosts are read from per-address maps (`storageOf` of the callee, …), not from
the executing account's `storage`/`transient` or `storageOf`/`transientOf` at `st.env.address`.
Call-free `sstore` (which also updates `storageOf` at the executing address) preserves `RX`. -/
def Abs.ignoresLocal {G} (α : Abs G) : Prop :=
  ∀ (st : EvmState) (σ τ : U256 → U256)
      (sto : U256 → U256 → U256) (tro : U256 → U256 → U256) (a : Address),
    (∀ addr k, accountKey addr ≠ accountKey st.env.address →
        sto addr k = st.env.storageOf addr k) →
    (∀ addr k, accountKey addr ≠ accountKey st.env.address →
        tro addr k = st.env.transientOf addr k) →
    α.ofState
      { st with
        storage := σ
        transient := τ
        env := { st.env with storageOf := sto, transientOf := tro } } a =
      α.ofState st a

/-- Every **successful** Yul/EVM call from `self` to `addr` decodes to some method
of `I`, matches `I.model`, and `NoInterfere`. Failed responses (`success = false`)
are unconstrained. ABI-false / short `boolOpt` cannot be a success. -/
def Conforms (I : Interface) (self addr : Address) (calls : ExternalCalls)
    (α : Abs I.Ghost) : Prop :=
  ∀ (req : CallRequest) (st : EvmState) (resp : CallResponse),
    calls.Call req st resp →
    req.target = BitVec.ofNat 256 addr →
    req.kind = CallKind.call →
    st.env.address = BitVec.ofNat 256 self →
    resp.success = true →
      ∃ (m : I.Method) (args : List Nat) (ret : Nat) (g' : I.Ghost),
        req.input = abiInput (I.abi m) args ∧
        args.length = (I.abi m).arity ∧
        (∀ x ∈ args, x < wordBound) ∧
        I.model m self args (α.ofState st addr) = some (ret, g') ∧
        decodeRet (I.abi m).ret resp.returndata ret ∧
        α.ofWorld resp.world addr = g' ∧
        NoInterfere α st resp.world addr

/-- Totality of the bound-token relation: every request from every pre-state has
some response. Realistic for EVM `CALL` (the opcode always returns a success
flag and a returndata buffer). TCB: used by `yul_progress` so a Yul `Run` of
the compiled runtime exists, which with EVM determinism gives universality
over halted `Steps`. -/
def CallsTotal (calls : ExternalCalls) : Prop :=
  ∀ req st, ∃ resp, calls.Call req st resp

/-- Inhabitation (forward/non-vacuity). Used only by an `_exists` companion, not
by the backward `toYulFn_correct_ext`. Glue may set `faults n := ¬resp.success`. -/
def Realizes {I : Interface} (α : Abs I.Ghost) (self addr : Address)
    (calls : ExternalCalls) (st : EvmState) (m : I.Method) (args : List Nat)
    (g : I.Ghost) (fault : Bool) : Prop :=
  let req : CallRequest :=
    { kind := .call
      gas := BitVec.ofNat 256 extCallGas
      target := BitVec.ofNat 256 addr
      value := 0
      input := abiInput (I.abi m) args }
  if fault then
    ∃ resp, calls.Call req st resp ∧ resp.success = false
  else
    match I.model m self args g with
    | none => ∃ resp, calls.Call req st resp ∧ resp.success = false
    | some (ret, g') =>
        ∃ resp, calls.Call req st resp ∧ resp.success = true ∧
          decodeRet (I.abi m).ret resp.returndata ret ∧
          α.ofWorld resp.world addr = g' ∧
          NoInterfere α st resp.world addr

/-- Fault oracle that answers `bit` at the current `ncalls` and `rest` afterward.
The continuation of a successful call sees indices `≥ ncalls + 1`. -/
def composeFault (n0 : Nat) (bit : Bool) (rest : Nat → Bool) : Nat → Bool :=
  fun n => if n = n0 then bit else rest n

theorem composeFault_at (n0 : Nat) (bit : Bool) (rest : Nat → Bool) :
    composeFault n0 bit rest n0 = bit := by simp [composeFault]

theorem composeFault_gt {n0 n : Nat} (bit : Bool) (rest : Nat → Bool)
    (h : n0 < n) : composeFault n0 bit rest n = rest n := by
  have : n ≠ n0 := Nat.ne_of_gt h
  simp [composeFault, this]

/-- Schema `ext.call` is `Tx.call` of this binding/method (generated by `lsc_schema`). -/
def ExtAgrees {I : Interface} {S X E ε}
    (Γ : ContractSchema S X E ε) (bIdx : Nat) (bind : Binding I S X)
    (mIdx : Nat) (meth : I.Method) : Prop :=
  ∀ args, Γ.ext.call bIdx mIdx args = Tx.call (E := E) (ε := ε) bind meth args

/-- Compiler binding `bIdx`/`mIdx` is schema `bind`/`meth`. Address is the scalar at
the binding's field slot (read through `R`/`storageRel`, not assumed constant in `S`). -/
structure BindWF {I : Interface} {S X E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (bind : Binding I S X) (bIdx mIdx : Nat) (meth : I.Method) : Prop where
  lookup :
    ∃ bd, c.bindings[bIdx]? = some bd ∧
      (bd.methods[mIdx]?).map (·.snd) = some (I.abi meth) ∧
      (∀ σ, Γ.st.scalar bd.fieldSlot σ = bind.addr σ) ∧
      (c.fields[bd.fieldSlot]?).map (·.kind) = some FieldKind.scalar
  hgetset : ∀ x g, bind.get (bind.set x g) = g
  hext : ExtAgrees Γ bIdx bind mIdx meth
  hsel : ∀ m', (I.abi m').selector < 2 ^ 32
  huniq : ∀ m', (I.abi m').selector = (I.abi meth).selector → m' = meth
  hret : (I.abi meth).ret = .word ∨ (I.abi meth).ret = .boolOpt
  harity : (I.abi meth).arity ≤ 3

end Lsc.Compiler
