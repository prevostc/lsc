import Lsc.Lang.ExtState
import Lsc.Lang.Tx
import Lsc.Lang.Interface
import Lsc.Compiler.Yul
import YulSemantics.Observation
import YulEvmCompiler.Optimizer.Spec.Observe

/-!
# Memory-blind external-call oracle

An EVM callee never sees the caller's memory or `msize`. It sees the call
request (calldata, value, gas, target) and the world/account projection.
`ExtOracle` is that contract at the type level: the oracle is not given
`EvmState`, so it cannot peek at caller memory. Wrapping through
`toCalls` yields an `ExternalCalls` relation that is scratch-insensitive
for every reservation interval, which is what powdr's spill theorem needs.

`Lsc.Oracle.ofExt` is the one Core bridge: it turns an `ExtOracle` into the
Lang `Oracle ExtState` that `Tx.call` / `Tx.view` consult. There is no
per-interface `Conforms` / `BindEnv` layer.

A second, distinct modelling consequence: `ExtOracle` is a function of the
request and the observable world, so the oracle is deterministic. Wrapping
with `toCalls` discharges `CallsTotal` once (`toCalls_total`) instead of
assuming it.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

/-- Caller/transaction-observable projection: the fixed `Lsc.ExtState`. -/
abbrev ExtView := Lsc.ExtState

/-- Project an `EvmState` onto the view a callee can observe. -/
def ExtView.ofState (st : EvmState) : ExtView := Lsc.ExtState.ofState st

/-- `observables` agreement implies `ExtView.ofState` agreement. -/
theorem ExtView.ofState_congr {l r : EvmState}
    (h : observables l = observables r) :
    ExtView.ofState l = ExtView.ofState r :=
  congrArg (fun o : Obs =>
    ({ storage := o.storage, transient := o.transient, env := o.env,
       returndata := o.returndata, logs := o.logs,
       selfdestructs := o.selfdestructs, halted := o.halted } : Lsc.ExtState)) h

/-- External-call oracle that is memory-free by construction. -/
abbrev ExtOracle := CallRequest → ExtView → CallResponse

/-- Apply a memory-blind oracle to a full Yul state by dropping memory/`msize`. -/
def toCall (o : ExtOracle) (req : CallRequest) (st : EvmState) : CallResponse :=
  o req (ExtView.ofState st)

/-- `ExternalCalls` wrapper: the unique response is `toCall o req st`. -/
def toCalls (o : ExtOracle) : ExternalCalls where
  Call req st resp := resp = toCall o req st

/-- Totality of a CALL relation: every request from every pre-state has some
response. `toCalls o` discharges this by construction. -/
def CallsTotal (calls : ExternalCalls) : Prop :=
  ∀ req st, ∃ resp, calls.Call req st resp

/-- Agreement on every field except memory and `msize` (Yul `EvmState` has no
stack/pc). Stronger than `CallsScratchInsensitive`, which only needs this on
`ScratchRel` pairs. -/
def CallsMemoryBlind (calls : ExternalCalls) : Prop :=
  ∀ req left right response,
    ExtView.ofState left = ExtView.ofState right →
    (calls.Call req left response ↔ calls.Call req right response)

/-! ## Core bridge (`Oracle.ofExt`) -/

/-- ABI words of a returndata buffer, using the EVM `returndatasize` wrap
(`length % 2^256`). Empty is `[]`. A short (1–31 byte) payload is a
two-word poison so `AbiRetType.decode` fails for `word` / `boolOpt`.
Otherwise one word per complete 32-byte chunk of the wrapped size. -/
def rdsNat (bs : List UInt8) : Nat := (BitVec.ofNat 256 bs.length).toNat

def abiWords (bs : List UInt8) : List Nat :=
  let n := rdsNat bs
  if n = 0 then []
  else if n < 32 then [0, 0]
  else (List.range (n / 32)).map fun i => (wordFrom bs (32 * i)).toNat

/-- CALL / STATICCALL request with packed `sel ‖ args` and the `extCallGas`
stipend. -/
def mkCallReq (kind : CallKind) (addr : Address) (sel : Nat) (args : List Nat) :
    CallRequest where
  kind := kind
  gas := BitVec.ofNat 256 extCallGas
  target := BitVec.ofNat 256 addr
  value := 0
  input := selectorBytes sel ++ args.flatMap wordBytes

/-- Install a successful CALL's `CallWorld` onto an `ExtState` (mirrors
`CallWorld.install`, without memory). -/
def installWorld (x : Lsc.ExtState) (world : CallWorld) : Lsc.ExtState where
  storage := world.storage
  transient := world.transient
  env := { x.env with
    selfBalance := world.selfBalance
    balanceOf := world.balanceOf
    extCodeOf := world.extCodeOf
    extCodeHashOf := world.extCodeHashOf
    nonceOf := world.nonceOf
    storageOf := world.storageOf
    transientOf := world.transientOf }
  returndata := x.returndata
  logs := x.logs ++ world.logs
  selfdestructs := x.selfdestructs ++ world.selfdestructs
  halted := x.halted

/-- Successful CALL post-view: installed world plus the response returndata. -/
def ofCallSuccess (x : Lsc.ExtState) (resp : CallResponse) : Lsc.ExtState :=
  { installWorld x resp.world with returndata := resp.returndata }

/-- Drop executing-account storage/transient, the `storageOf`/`transientOf`
slices at `self`, and caller-local logs/returndata/halt/selfdestructs. A
real callee cannot observe those fields without reentering `self`. -/
def scrubSelf (self : Address) (x : Lsc.ExtState) : Lsc.ExtState :=
  let selfKey := accountKey (BitVec.ofNat 256 self)
  { x with
    storage := fun _ => 0
    transient := fun _ => 0
    logs := []
    returndata := []
    halted := none
    selfdestructs := []
    env := { x.env with
      storageOf := fun a k =>
        if accountKey a = selfKey then 0 else x.env.storageOf a k
      transientOf := fun a k =>
        if accountKey a = selfKey then 0 else x.env.transientOf a k } }

/-- Two views agree on everything a callee can see without reentering `self`. -/
def agreeExceptSelf (self : Address) (x y : Lsc.ExtState) : Prop :=
  scrubSelf self x = scrubSelf self y

/-- `w.ext` matches the callee-visible part of `st` (our storage may lag
local `sstore`s; the next CALL refreshes it from the response world). -/
def ExtAgree (self : Address) (x : Lsc.ExtState) (st : EvmState) : Prop :=
  agreeExceptSelf self x (ExtView.ofState st)

/-- Reentrancy is not modelled. This is the only assumption S2 theorems make
about the callee; everything else is adversarial.

On the true Yul view (`ExtView.ofState st` at `self`), a response must not
change this contract's storage, transient storage, or ETH balances, and must
not emit logs attributed to `self`. The oracle also ignores those caller-local
fields of the request view, so Core's `w.ext` may lag local `sstore`s until
the next CALL installs the response world. -/
structure ExtOracle.NoReentry (o : ExtOracle) (self : Address) : Prop where
  noInterfere : ∀ (req : CallRequest) (st : EvmState),
    st.env.address = BitVec.ofNat 256 self →
      let resp := o req (ExtView.ofState st)
      resp.world.storage = st.storage ∧
      resp.world.transient = st.transient ∧
      resp.world.selfBalance = st.env.selfBalance ∧
      resp.world.balanceOf = st.env.balanceOf ∧
      (∀ l ∈ resp.world.logs, l.address ≠ st.env.address)
  ignoresSelf : ∀ (req : CallRequest) (x : ExtView) (st : EvmState),
    st.env.address = BitVec.ofNat 256 self →
    agreeExceptSelf self x (ExtView.ofState st) →
      o req x = o req (ExtView.ofState st)

/-- Decode ABI return data against a Core word. `boolOpt` is empty → `1`, or
exactly one ABI word with `v = 0/1` from the word being zero/nonzero.
`word` is exactly one ABI word. `none` is Core `0`. Length is the wrapped
`returndatasize`, so it agrees with Yul `returndatasize()`. -/
def decodeRet : AbiRet → List UInt8 → Nat → Prop
  | .boolOpt, bs, v =>
      let n := rdsNat bs
      (n = 0 ∧ v = 1) ∨
        (32 ≤ n ∧ n < 64 ∧ v = if wordFrom bs 0 = 0 then 0 else 1)
  | .word, bs, v =>
      let n := rdsNat bs
      32 ≤ n ∧ n < 64 ∧ (wordFrom bs 0).toNat = v
  | .none, _, v => v = 0

def abiInput (sel : Nat) (args : List Nat) : List UInt8 :=
  selectorBytes sel ++ args.flatMap wordBytes

/-- Bridge from a memory-blind EVM CALL oracle to the Lang `Oracle`. `call`
issues a CALL request with packed `sel ‖ args`; failure (`success = false`)
is `none`. `view` issues a STATICCALL request and is total (a failed
STATICCALL becomes a two-word poison so `word`/`boolOpt` decode fails).
The post-`ext` of a successful CALL is the response world; STATICCALL does
not update `ext`. -/
def _root_.Lsc.Oracle.ofExt (o : ExtOracle) : Lsc.Oracle Lsc.ExtState where
  call addr sel args x :=
    let resp := o (mkCallReq .call addr sel args) x
    if resp.success then
      some (abiWords resp.returndata, ofCallSuccess x resp)
    else none
  view addr sel args x :=
    let resp := o (mkCallReq .staticcall addr sel args) x
    if resp.success then abiWords resp.returndata else [0, 0]

end Lsc.Compiler
