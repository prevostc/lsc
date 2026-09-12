import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Compiler.TransportTheorems
import Lsc.Compiler.Externals
import Examples.Cpamm.Contract
import Stdlib.ERC20

/-!
CPAMM spec: `claim` is LP share count; `Auth` is the victim's own
`removeLiquidity`. `Inv` is share-support, `protocolShareBps ≤ BPS`, and
each reserve plus that token's protocol bucket covered by the pool's
balance of that token. `k` is a swap fact, not `Inv`.
-/

open Lsc Lsc.Stdlib Lsc.Security Lsc.Compiler Cpamm
open YulSemantics.EVM
open YulEvmCompiler (Instr)

lsc_codec Cpamm

namespace Lsc.Compiler

open Lsc.Stdlib

@[reducible] def cpammBs (α : Abs IERC20.Ghost) : List (BindEnv IERC20 Cpamm.Storage Cpamm.Ext) :=
  [⟨α, Cpamm.token0B⟩, ⟨α, Cpamm.token1B⟩]

end Lsc.Compiler

namespace Cpamm

def claim (a : Address) (σ : Storage) : Nat := (σ.shares a).raw

def claim0 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0
  else (σ.shares a).raw * σ.reserve0.raw / σ.totalShares.raw

def claim1 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0
  else (σ.shares a).raw * σ.reserve1.raw / σ.totalShares.raw

def Auth (a : Address) (c : Call spec) (_s : Storage) : Prop :=
  match c.fn, c.args with
  | .removeLiquidity, _ => c.sender = a
  | _, _ => False

def inflow (c : Call spec) (w : World Storage Ext Event) : Nat :=
  match c.fn, c.args with
  | .addLiquidity, (a0, a1) =>
    match Tx.run (addLiquidity a0 a1) c.toCtx w with
    | .ok (n, _) => n.raw
    | .error _ => 0
  | _, _ => 0

def holdings0 (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.token0.balances self

def holdings1 (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.token1.balances self

def holdings (self : Address) (w : World Storage Ext Event) : Nat :=
  holdings0 self w

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => (σ.shares a).raw) = σ.totalShares.raw

/-- Each reserve plus that token's protocol bucket is covered by the pool's
token balance, share balances have finite support, and the protocol share
is at most 100%. -/
def Inv (self : Address) (w : World Storage Ext Event) : Prop :=
  w.self.reserve0.raw + w.self.protocolFees0.raw ≤ holdings0 self w ∧
  w.self.reserve1.raw + w.self.protocolFees1.raw ≤ holdings1 self w ∧
  InvStorage w.self ∧
  w.self.protocolShareBps ≤ BPS

/-- After a trace, LP pro-rata claims plus protocol buckets are covered. -/
def CoversLpsAndProtocol (self : Address) (w : World Storage Ext Event) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → w.self.shares a = 0) ∧
    H.sum (fun a => claim0 a w.self) + w.self.protocolFees0.raw ≤ holdings0 self w ∧
    H.sum (fun a => claim1 a w.self) + w.self.protocolFees1.raw ≤ holdings1 self w

def cpammRely (self : Address) (x x' : Ext) : Prop :=
  Rely self x.token0 x'.token0 ∧ Rely self x.token1 x'.token1

def cpammClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  (σ (mapSlot1 κ 5 a)).toNat

def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (token0B.addr w'.self) ext α ∧
    Conforms IERC20 self (token1B.addr w'.self) ext α

@[reducible] def cpammEnv0 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token0B⟩

@[reducible] def cpammEnv1 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token1B⟩

/-- Fee-less notional input `⌊dx · (BPS − FEE_BPS) / BPS⌋`. -/
def dxFeeLess (dx : Nat) : Nat :=
  dx * (BPS - FEE_BPS) / BPS

/-- Swap fee `dx − dxF`. -/
def swapFee (dx : Nat) : Nat :=
  dx - dxFeeLess dx

/-- Protocol take: zero when `feeTo = 0`, else `⌊fee · protocolShareBps / BPS⌋`. -/
def protoTake (feeTo protocolShareBps fee : Nat) : Nat :=
  if (feeTo : Nat) = 0 then 0 else fee * protocolShareBps / BPS

def amountOutF (rIn rOut dx : Nat) : Nat :=
  let dxF := dxFeeLess dx
  rOut * dxF / (rIn + dxF)

/-- Shared quote used by both swap directions: `(out, proto)`. -/
def swapQuote (rIn rOut dx feeTo pShareBps : Nat) : Nat × Nat :=
  (amountOutF rIn rOut dx, protoTake feeTo pShareBps (swapFee dx))

end Cpamm
