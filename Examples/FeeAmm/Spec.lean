import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Compiler.TransportTheorems
import Lsc.Compiler.Externals
import Examples.FeeAmm.Contract
import Stdlib.ERC20

/-!
FeeAmm spec: `claim` is LP share count; `Auth` is the victim's own
`removeLiquidity`. `Inv` is share-support, `protocolShareBps ≤ BPS`, and
each reserve plus that token's protocol bucket covered by the pool's
balance of that token. `k` is a swap fact, not `Inv`.
-/

open Lsc Lsc.Stdlib Lsc.Security Lsc.Compiler FeeAmm
open YulSemantics.EVM
open YulEvmCompiler (Instr)

lsc_codec FeeAmm

namespace Lsc.Compiler

open Lsc.Stdlib

@[reducible] def feeAmmBs (α : Abs IERC20.Ghost) : List (BindEnv IERC20 FeeAmm.Storage FeeAmm.Ext) :=
  [⟨α, FeeAmm.token0B⟩, ⟨α, FeeAmm.token1B⟩]

end Lsc.Compiler

namespace FeeAmm

def claim (a : Address) (σ : Storage) : Nat := σ.shares a

def claim0 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.reserve0 / σ.totalShares

def claim1 (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.reserve1 / σ.totalShares

def Auth (a : Address) (c : Call spec) (_s : Storage) : Prop :=
  match c.fn, c.args with
  | .removeLiquidity, _ => c.sender = a
  | _, _ => False

def inflow (c : Call spec) (w : World Storage Ext Event) : Nat :=
  match c.fn, c.args with
  | .addLiquidity, (a0, a1) =>
    match Tx.run (addLiquidity a0 a1) c.toCtx w with
    | .ok (n, _) => n
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
    H.sum (fun a => σ.shares a) = σ.totalShares

def Inv (self : Address) (w : World Storage Ext Event) : Prop :=
  w.self.reserve0 + w.self.protocolFees0 ≤ holdings0 self w ∧
  w.self.reserve1 + w.self.protocolFees1 ≤ holdings1 self w ∧
  InvStorage w.self ∧
  w.self.protocolShareBps ≤ BPS

/-- After a trace, LP pro-rata claims plus protocol buckets are covered. -/
def CoversLpsAndProtocol (self : Address) (w : World Storage Ext Event) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → w.self.shares a = 0) ∧
    H.sum (fun a => claim0 a w.self) + w.self.protocolFees0 ≤ holdings0 self w ∧
    H.sum (fun a => claim1 a w.self) + w.self.protocolFees1 ≤ holdings1 self w

def feeAmmRely (self : Address) (x x' : Ext) : Prop :=
  Rely self x.token0 x'.token0 ∧ Rely self x.token1 x'.token1

def feeAmmClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  (σ (mapSlot1 κ 3 a)).toNat

def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (token0B.addr w'.self) ext α ∧
    Conforms IERC20 self (token1B.addr w'.self) ext α

@[reducible] def feeAmmEnv0 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token0B⟩

@[reducible] def feeAmmEnv1 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token1B⟩

/-- Fee-less notional input `⌊dx · (BPS − FEE_BPS) / BPS⌋`. -/
def dxFeeLess (dx : Nat) : Nat :=
  dx * (BPS - FEE_BPS) / BPS

/-- Swap fee `dx − dxF`. -/
def swapFee (dx : Nat) : Nat :=
  dx - dxFeeLess dx

/-- Protocol take: zero when `feeTo = 0`, else `⌊fee · protocolShareBps / BPS⌋`. -/
def protoTake (feeTo protocolShareBps fee : Nat) : Nat :=
  if feeTo = 0 then 0 else fee * protocolShareBps / BPS

def amountOutF (rIn rOut dx : Nat) : Nat :=
  let dxF := dxFeeLess dx
  dxF * rOut / (rIn + dxF)

/-- Shared quote used by both swap directions: `(out, proto)`. -/
def swapQuote (rIn rOut dx feeTo pShareBps : Nat) : Nat × Nat :=
  (amountOutF rIn rOut dx, protoTake feeTo pShareBps (swapFee dx))

end FeeAmm
