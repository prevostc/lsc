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

/-- Foreign account persistent storage (`env.storageOf`), indexed by 256-bit
address words (low-160-bit aliases are the EVM account). -/
abbrev Foreign := U256 → U256 → U256

/-- Projection of an `EvmState` onto foreign persistent storage. -/
def evmForeign (st : EvmState) : Foreign := st.env.storageOf

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

theorem NoInterfere.ofWorld_ne {G} {α : Abs G}
    {st : EvmState} {world : CallWorld} {callee a : Address}
    (h : NoInterfere α st world callee) (hne : a ≠ callee) :
    α.ofWorld world a = α.ofState st a :=
  h.2.2.2.2.2 a hne

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
Call-free `sstore` (which also updates `storageOf` at the executing address) preserves `RX`
at a **foreign** `a` (`accountKey` ≠ executor; `RX`/`Conforms` only read the bound token). -/
def Abs.ignoresLocal {G} (α : Abs G) : Prop :=
  ∀ (st : EvmState) (σ τ : U256 → U256)
      (sto : U256 → U256 → U256) (tro : U256 → U256 → U256) (a : Address),
    accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address →
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

/-- `α` reads a foreign account only through that account's `storageOf` slice
(`evmForeign`). Independent of `ignoresLocal` (local `sstore` at the
executing address). -/
def Abs.ofState_foreign {G} (α : Abs G) : Prop :=
  ∀ (st st' : EvmState) (a : Address),
    (∀ k, evmForeign st (BitVec.ofNat 256 a) k = evmForeign st' (BitVec.ofNat 256 a) k) →
    α.ofState st a = α.ofState st' a

theorem RX_of_foreign {I : Interface} {S X E} {α : Abs I.Ghost} {bind : Binding I S X}
    (hF : α.ofState_foreign) {w : World S X E} {st st' : EvmState}
    (hξ : ∀ k, evmForeign st (BitVec.ofNat 256 (bind.addr w.self)) k =
               evmForeign st' (BitVec.ofNat 256 (bind.addr w.self)) k)
    (hRX : RX α bind w st) : RX α bind w st' :=
  (hF st st' (bind.addr w.self) hξ).symm.trans hRX

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

/-! ## Binding family (S2, one or more external contracts) -/

/-- One external binding in an S2 family. `α` is typically shared (Solidity IERC20). -/
structure BindEnv (I : Interface) (S X : Type) where
  α : Abs I.Ghost
  bind : Binding I S X

/-- Every package's ghost agrees with `w.ext` at its bound address. -/
def RXs {I : Interface} {S X E} (bs : List (BindEnv I S X))
    (w : World S X E) (st : EvmState) : Prop :=
  ∀ e ∈ bs, RX e.α e.bind w st

def BindEnvs.ignoresLocal {I : Interface} {S X} (bs : List (BindEnv I S X)) : Prop :=
  ∀ e ∈ bs, e.α.ignoresLocal

def BindEnvs.ofState_foreign {I : Interface} {S X} (bs : List (BindEnv I S X)) : Prop :=
  ∀ e ∈ bs, e.α.ofState_foreign

def BindEnvs.neSelf {I : Interface} {S X} (bs : List (BindEnv I S X))
    (self : Address) (σ : S) : Prop :=
  ∀ e ∈ bs,
    accountKey (BitVec.ofNat 256 (e.bind.addr σ)) ≠ accountKey (BitVec.ofNat 256 self)

def BindEnvs.conforms {I : Interface} {S X} (bs : List (BindEnv I S X))
    (self : Address) (σ : S) (calls : ExternalCalls) : Prop :=
  ∀ e ∈ bs, Conforms I self (e.bind.addr σ) calls e.α

/-- All packages use the same `Abs` (so `NoInterfere` frames other addresses). -/
def BindEnvs.sameAbs {I : Interface} {S X} (bs : List (BindEnv I S X)) : Prop :=
  ∀ e1 ∈ bs, ∀ e2 ∈ bs, e1.α = e2.α

/-- Distinct callee addresses have independent ghosts. -/
def BindEnvs.orthogonal {I : Interface} {S X} (bs : List (BindEnv I S X)) : Prop :=
  ∀ e1 ∈ bs, ∀ e2 ∈ bs, ∀ σ : S,
    e1.bind.addr σ ≠ e2.bind.addr σ →
      ∀ x g, e2.bind.get (e1.bind.set x g) = e2.bind.get x

/-- Same callee address ⇒ same `α` and same `get` (Conforms is unambiguous). -/
def BindEnvs.addrInj {I : Interface} {S X} (bs : List (BindEnv I S X)) (σ : S) : Prop :=
  ∀ e1 ∈ bs, ∀ e2 ∈ bs, e1.bind.addr σ = e2.bind.addr σ →
    e1.α = e2.α ∧ e1.bind.get = e2.bind.get

/-- A well-formed Core call indexes some package in `bs`. -/
def BindEnvs.lookupWF {I : Interface} {S X E ε}
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (bs : List (BindEnv I S X)) : Prop :=
  ∀ b m args, callWF c b m args = true →
    ∃ e ∈ bs, ∃ meth : I.Method, BindWF c Γ e.bind b m meth

theorem RXs_singleton {I : Interface} {S X E}
    (e : BindEnv I S X) (w : World S X E) (st : EvmState) :
    RXs [e] w st ↔ RX e.α e.bind w st := by
  constructor
  · intro h; exact h e (List.mem_singleton.mpr rfl)
  · intro h e' he'
    have : e' = e := List.mem_singleton.mp he'
    subst this; exact h

theorem RXs_faults {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    {w : World S X E} {st : EvmState} (g : Nat → Bool) :
    RXs bs { w with faults := g } st ↔ RXs bs w st := Iff.rfl

theorem BindEnvs.sameAbs_singleton {I S X} (e : BindEnv I S X) :
    BindEnvs.sameAbs [e] := by
  intro e1 h1 e2 h2
  have h1' : e1 = e := List.mem_singleton.mp h1
  have h2' : e2 = e := List.mem_singleton.mp h2
  subst h1'; subst h2'; rfl

theorem BindEnvs.orthogonal_singleton {I S X} (e : BindEnv I S X) :
    BindEnvs.orthogonal [e] := by
  intro e1 h1 e2 h2 σ hne
  have h1' : e1 = e := List.mem_singleton.mp h1
  have h2' : e2 = e := List.mem_singleton.mp h2
  subst h1'; subst h2'
  exact (hne rfl).elim

theorem BindEnvs.addrInj_singleton {I S X} (e : BindEnv I S X) (σ : S) :
    BindEnvs.addrInj [e] σ := by
  intro e1 h1 e2 h2 _
  have h1' : e1 = e := List.mem_singleton.mp h1
  have h2' : e2 = e := List.mem_singleton.mp h2
  subst h1'; subst h2'
  exact ⟨rfl, rfl⟩

theorem BindEnvs.lookupWF_singleton {I S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {α : Abs I.Ghost} {bind : Binding I S X}
    (hBind : ∀ b m args, callWF c b m args = true →
      ∃ meth, BindWF c Γ bind b m meth) :
    BindEnvs.lookupWF c Γ [⟨α, bind⟩] := by
  intro b m args h
  obtain ⟨meth, hbd⟩ := hBind b m args h
  exact ⟨⟨α, bind⟩, List.mem_singleton.mpr rfl, meth, hbd⟩

theorem BindEnvs.ignoresLocal_singleton {I S X}
    (e : BindEnv I S X) (h : e.α.ignoresLocal) :
    BindEnvs.ignoresLocal [e] := by
  intro e' he'
  have : e' = e := List.mem_singleton.mp he'
  subst this; exact h

theorem BindEnvs.ofState_foreign_singleton {I S X}
    (e : BindEnv I S X) (h : e.α.ofState_foreign) :
    BindEnvs.ofState_foreign [e] := by
  intro e' he'
  have : e' = e := List.mem_singleton.mp he'
  subst this; exact h

theorem BindEnvs.neSelf_singleton {I S X}
    (e : BindEnv I S X) (self : Address) (σ : S)
    (h : accountKey (BitVec.ofNat 256 (e.bind.addr σ)) ≠
      accountKey (BitVec.ofNat 256 self)) :
    BindEnvs.neSelf [e] self σ := by
  intro e' he'
  have : e' = e := List.mem_singleton.mp he'
  subst this; exact h

theorem BindEnvs.conforms_singleton {I S X}
    (e : BindEnv I S X) (self : Address) (σ : S) (calls : ExternalCalls)
    (h : Conforms I self (e.bind.addr σ) calls e.α) :
    BindEnvs.conforms [e] self σ calls := by
  intro e' he'
  have : e' = e := List.mem_singleton.mp he'
  subst this; exact h

theorem BindEnvs.conforms_self {I S X} {bs : List (BindEnv I S X)}
    {self : Address} {σ σ' : S} {calls : ExternalCalls}
    (hσ : σ' = σ) (h : BindEnvs.conforms bs self σ calls) :
    BindEnvs.conforms bs self σ' calls := by
  subst hσ; exact h

theorem BindEnvs.neSelf_self {I S X} {bs : List (BindEnv I S X)}
    {self : Address} {σ σ' : S} (hσ : σ' = σ)
    (h : BindEnvs.neSelf bs self σ) : BindEnvs.neSelf bs self σ' := by
  subst hσ; exact h

theorem BindEnvs.addrInj_self {I S X} {bs : List (BindEnv I S X)} {σ σ' : S}
    (hσ : σ' = σ) (h : BindEnvs.addrInj bs σ) : BindEnvs.addrInj bs σ' := by
  subst hσ; exact h

theorem BindEnvs.neSelf_of_addr {I S X} {bs : List (BindEnv I S X)}
    {self : Address} {σ σ' : S}
    (h : BindEnvs.neSelf bs self σ)
    (ha : ∀ e ∈ bs, e.bind.addr σ' = e.bind.addr σ) :
    BindEnvs.neSelf bs self σ' := by
  intro e he
  simpa [ha e he] using h e he

theorem BindEnvs.addrInj_of_addr {I S X} {bs : List (BindEnv I S X)} {σ σ' : S}
    (h : BindEnvs.addrInj bs σ)
    (ha : ∀ e ∈ bs, e.bind.addr σ' = e.bind.addr σ) :
    BindEnvs.addrInj bs σ' := by
  intro e1 h1 e2 h2 heq
  exact h e1 h1 e2 h2 (by simpa [ha e1 h1, ha e2 h2] using heq)

theorem BindEnvs.conforms_of_addr {I S X} {bs : List (BindEnv I S X)}
    {self : Address} {σ σ' : S} {calls : ExternalCalls}
    (h : BindEnvs.conforms bs self σ calls)
    (ha : ∀ e ∈ bs, e.bind.addr σ' = e.bind.addr σ) :
    BindEnvs.conforms bs self σ' calls := by
  intro e he
  simpa [ha e he] using h e he

theorem RXs_of_foreign {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    (hF : BindEnvs.ofState_foreign bs) {w : World S X E} {st st' : EvmState}
    (hξ : ∀ e ∈ bs, ∀ k,
      evmForeign st (BitVec.ofNat 256 (e.bind.addr w.self)) k =
      evmForeign st' (BitVec.ofNat 256 (e.bind.addr w.self)) k)
    (hRX : RXs bs w st) : RXs bs w st' := by
  intro e he
  exact RX_of_foreign (hF e he) (hξ e he) (hRX e he)

theorem RXs_irrel_log_faults {I : Interface} {S X E} {bs : List (BindEnv I S X)}
    {w : World S X E} {st : EvmState} (log' : List E) (fo : Nat → Bool)
    (h : RXs bs w st) : RXs bs { w with log := log', faults := fo } st := h

theorem RXs_pair {I : Interface} {S X E}
    (e0 e1 : BindEnv I S X) (w : World S X E) (st : EvmState) :
    RXs [e0, e1] w st ↔ RX e0.α e0.bind w st ∧ RX e1.α e1.bind w st := by
  constructor
  · intro h
    exact ⟨h e0 (List.mem_cons.mpr (Or.inl rfl)),
      h e1 (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))⟩
  · intro ⟨h0, h1⟩ e he
    have : e = e0 ∨ e = e1 := by
      simpa [List.mem_cons, List.mem_singleton] using he
    rcases this with rfl | rfl
    · exact h0
    · exact h1

end Lsc.Compiler
