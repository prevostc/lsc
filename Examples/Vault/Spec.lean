import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Lsc.Compiler.TransportTheorems
import Examples.Vault.Contract
import Stdlib.ERC20

/-!
Vault spec: `claim` is floor-rounded redeemable assets; `Auth` is the
victim's own `withdraw`. `Inv` is share-support plus `totalAssets` covered
by the vault's token balance. Between calls, `vaultRely` forbids the token
balance from falling.
-/

open Lsc Lsc.Stdlib Lsc.Security Lsc.Compiler Vault
open YulSemantics.EVM
open YulEvmCompiler (Instr)

lsc_codec Vault

namespace Vault

/-- Redeemable assets of `a`. Zero when the supply is empty. -/
def claim (a : Address) (σ : Storage) : Nat :=
  if σ.totalShares = 0 then 0 else σ.shares a * σ.totalAssets / σ.totalShares

/-- Only a `withdraw` by `a` itself may decrease `claim a`. -/
def Auth (a : Address) (c : Call spec) (_s : Storage) : Prop :=
  match c.fn, c.args with
  | .withdraw, _ => c.sender = a
  | _, _ => False

/-- Deposit is the only inflow of claim-units; it is `0` on revert. -/
def inflow (c : Call spec) (w : World Storage Ext Event) : Nat :=
  match c.fn, c.args with
  | .deposit, assets =>
    match Tx.run (deposit assets) c.toCtx w with
    | .ok _ => assets.toNat
    | .error _ => 0
  | _, _ => 0

/-- Underlying-token balance of the vault. -/
def holdings (self : Address) (w : World Storage Ext Event) : Nat :=
  w.ext.asset.balances self

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => σ.shares a) = σ.totalShares

/-- `totalAssets ≤` ghost balance of `self`, and share balances have finite support. -/
def Inv (self : Address) (w : World Storage Ext Event) : Prop :=
  w.self.totalAssets ≤ holdings self w ∧ InvStorage w.self

/-- Between our calls: vault token balance is non-decreasing and `decimals` is fixed. -/
def vaultRely (self : Address) (x x' : Ext) : Prop :=
  Rely self x.asset x'.asset

def vaultClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  let ta := (σ (BitVec.ofNat 256 0)).toNat
  let ts := (σ (BitVec.ofNat 256 1)).toNat
  let sh := (σ (mapSlot1 κ 2 a)).toNat
  if ts = 0 then 0 else sh * ta / ts

def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (Vault.assetB.addr w'.self) ext α

/-- Holdings of `self` according to `α` at the token address, from bytecode `σ`/`ξ`. -/
def vaultHoldingsRead (α : Abs IERC20.Ghost) (σ : U256 → U256) (ξ : Foreign)
    (self assetAddr : Address) : Nat :=
  (α.ofState (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self))
    assetAddr).balances self

/-- Storage-level solvency: finite support of `vaultClaimRead` on addresses below
`wordBound`, and that support's sum is ≤ holdings read through `α` from `ξ`.
Addresses `≥ wordBound` are outside `storageRel`. Trailing `env` steps may raise
Spec holdings while `ξ'` stays at the last EVM call; this statement tracks `ξ'`. -/
def vaultSolventRead (α : Abs IERC20.Ghost) (σ : U256 → U256) (ξ : Foreign)
    (self assetAddr : Address) : Prop :=
  ∃ H : Finset Address,
    (∀ a, Nat.lt a wordBound → a ∉ H → vaultClaimRead evmKeccak σ a = 0) ∧
    H.sum (vaultClaimRead evmKeccak σ) ≤ vaultHoldingsRead α σ ξ self assetAddr

@[reducible] def vaultEnv (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, Vault.assetB⟩

/-- Solidity ERC20 layout: `balances[o]` at `keccak(abi(o) ‖ abi(0))`, `decimals` at slot 1.
`Ghost` has no allowances or `totalSupply`; both are unread. Uses the fixed `evmKeccak`
oracle (not `st.env.keccakOf`) so `ofState_foreign` holds. -/
def vaultGhostOf (sto : U256 → U256) : IERC20.Ghost where
  balances := fun o =>
    (sto (mapSlot1 evmKeccak IERC20.balancesMappingSlot (o : Nat))).toNat
  decimals := (sto (BitVec.ofNat 256 IERC20.decimalsSlot)).toNat

def vaultAbsSolidity : Abs IERC20.Ghost where
  ofState st a := vaultGhostOf (evmForeign st (BitVec.ofNat 256 (a : Nat)))
  ofWorld w a := vaultGhostOf (w.storageOf (BitVec.ofNat 256 (a : Nat)))
  ofState_proj := fun _ _ => rfl
  ofWorld_install := fun _ _ _ => rfl

end Vault
