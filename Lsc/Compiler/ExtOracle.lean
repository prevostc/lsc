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

/-- Drop executing-account storage/transient, the `storageOf`/`transientOf`
slices at `self`, and caller-local logs/returndata/halt/selfdestructs. A
real callee cannot observe those fields without reentering `self`. -/
def scrubSelfWord (self : U256) (x : Lsc.ExtState) : Lsc.ExtState :=
  let selfKey := accountKey self
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

/-- `scrubSelfWord` at the EVM encoding of an `Address`. -/
def scrubSelf (self : Address) (x : Lsc.ExtState) : Lsc.ExtState :=
  scrubSelfWord (BitVec.ofNat 256 self) x

/-- Two views agree on everything a callee can see without reentering `self`. -/
def agreeExceptSelf (self : Address) (x y : Lsc.ExtState) : Prop :=
  scrubSelf self x = scrubSelf self y

/-- `w.ext` matches the callee-visible part of `st` (our storage may lag
local `sstore`s; the next CALL refreshes it from the response world). -/
def ExtAgree (self : Address) (x : Lsc.ExtState) (st : EvmState) : Prop :=
  agreeExceptSelf self x (ExtView.ofState st)

/-- Restore this contract's storage and transient storage from the
pre-call view, and drop logs attributed to `self`. Justified by the
runtime lock: a nested CALL/STATICCALL into the compiled runtime with
`tstorage[0] ≠ 0` reverts in the 11-step prefix and
`callReturnRevert` restores the parent snapshot
(`nested_lock_reverts`). ETH balances are not restored: a callee can
credit `self` via `SELFDESTRUCT` without executing our code, and
`balanceOf` of foreign accounts is a real CALL effect. -/
def restoreSelfWorld (x : ExtView) (world : CallWorld) : CallWorld :=
  { world with
    storage := x.storage
    transient := x.transient
    logs := world.logs.filter (fun l => l.address ≠ x.env.address) }

/-- Apply `o` to the callee-visible (self-scrubbed) view. -/
def callRaw (o : ExtOracle) (req : CallRequest) (x : ExtView) : CallResponse :=
  o req (scrubSelfWord x.env.address x)

/-- Install the lock restore on a raw oracle response. -/
def restoreCall (x : ExtView) (resp : CallResponse) : CallResponse :=
  { resp with world := restoreSelfWorld x resp.world }

/-- Apply a memory-blind oracle to a full Yul state by dropping memory/`msize`,
hiding `self`'s storage from the callee, and restoring `self`'s storage /
transient / self-logs after the call (the lock makes those writes
uncommitable). -/
def toCall (o : ExtOracle) (req : CallRequest) (st : EvmState) : CallResponse :=
  let x := ExtView.ofState st
  restoreCall x (callRaw o req x)

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
stipend. ABI calls carry value `0`. -/
def mkCallReq (kind : CallKind) (addr : Address) (sel : Nat) (args : List Nat) :
    CallRequest where
  kind := kind
  gas := BitVec.ofNat 256 extCallGas
  target := BitVec.ofNat 256 addr
  value := 0
  input := selectorBytes sel ++ args.flatMap wordBytes

/-- Value-carrying CALL, empty calldata (`Native.send`). -/
def mkSendReq (addr : Address) (value : Nat) : CallRequest where
  kind := .call
  gas := BitVec.ofNat 256 extCallGas
  target := BitVec.ofNat 256 addr
  value := BitVec.ofNat 256 value
  input := []

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

/-- The lock restore plus input scrub: a CALL through `toCall` cannot
overwrite this contract's storage or transient storage, and cannot
append a log attributed to `self`. ETH balances are not constrained
(`SELFDESTRUCT`-to-self and foreign `balanceOf` updates are real
effects of a non-reentering callee). The oracle is not given
caller-local storage: Core's lagged `w.ext` and the Yul view agree
after `scrubSelf`. -/
structure ExtOracle.NoReentry (o : ExtOracle) (self : Address) : Prop where
  noInterfere : ∀ (req : CallRequest) (st : EvmState),
    st.env.address = BitVec.ofNat 256 self →
      let resp := toCall o req st
      resp.world.storage = st.storage ∧
      resp.world.transient = st.transient ∧
      (∀ l ∈ resp.world.logs, l.address ≠ st.env.address)
  ignoresSelf : ∀ (req : CallRequest) (x : ExtView) (st : EvmState),
    st.env.address = BitVec.ofNat 256 self →
    agreeExceptSelf self x (ExtView.ofState st) →
      callRaw o req x = callRaw o req (ExtView.ofState st)

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
Both apply `o` to the self-scrubbed view (`callRaw`), matching `toCall`'s
input. The post-`ext` of a successful CALL is the unrestored response
world (self storage is not part of `ExtAgree`); STATICCALL does not
update `ext`. -/
def _root_.Lsc.Oracle.ofExt (o : ExtOracle) : Lsc.Oracle Lsc.ExtState where
  call addr sel args x :=
    let resp := callRaw o (mkCallReq .call addr sel args) x
    if resp.success then
      some (abiWords resp.returndata, ofCallSuccess x resp)
    else none
  view addr sel args x :=
    let resp := callRaw o (mkCallReq .staticcall addr sel args) x
    if resp.success then abiWords resp.returndata else [0, 0]
  send addr value x :=
    let resp := callRaw o (mkSendReq addr value) x
    if resp.success then some (ofCallSuccess x resp) else none

end Lsc.Compiler
