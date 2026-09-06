import Lsc.Lang.Amount
import Lsc.Lang.Reify
import Lsc.Stdlib.ERC20

/-!
# Amm — constant-product pool with two IERC20 bindings

No fee. First LP is minted `a0` shares (no `sqrt`). Later LPs get
`min(⌊a0 * S / r0⌋, ⌊a1 * S / r1⌋)`. Swaps use Uniswap-style
`⌊dx * r_out / (r_in + dx)⌋` so `k = r0 * r1` cannot decrease.

External calls run **after** requires and storage updates. That is sound
here because `Conforms` / `NoInterfere` exclude reentrancy (see
`docs/architecture/SECURITY_MODEL.md` and `INTERFACE_MODEL.md`).
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Amm

/-- Phantom markers. Scales are opaque (not Core literals), as in Vault. -/
structure TOKEN0 where
structure TOKEN1 where
structure SHARE where

opaque scale0 : Nat
opaque scale1 : Nat
def shareScale : Nat := WAD

structure Storage where
  reserve0 : Nat
  reserve1 : Nat
  totalShares : Nat
  shares : Mapping Address Nat
  token0 : IERC20.Ref
  token1 : IERC20.Ref
  decimals0 : Nat
  decimals1 : Nat

structure Ext where
  token0 : Ghost
  token1 : Ghost

instance : Inhabited Ext := ⟨⟨{}, {}⟩⟩

def token0B : Binding IERC20 Storage Ext :=
  ⟨(·.token0), (·.token0), fun x g => { x with token0 := g }⟩

def token1B : Binding IERC20 Storage Ext :=
  ⟨(·.token1), (·.token1), fun x g => { x with token1 := g }⟩

inductive Event
  | AddLiquidity (who : Address) (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
      (sharesOut : Amount SHARE shareScale)
  | RemoveLiquidity (who : Address) (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
      (sharesIn : Amount SHARE shareScale)
  | Swap0for1 (who : Address) (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
  | Swap1for0 (who : Address) (a1 : Amount TOKEN1 scale1) (a0 : Amount TOKEN0 scale0)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  | ZeroShares
  | ZeroOut
  | InsufficientShares
  | InsufficientOutput
  | SameToken
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

/-- Bind two distinct tokens and cache `decimals`. -/
def constructor (t0 t1 : Address) : M Unit := do
  Tx.require (t0 ≠ t1) .SameToken
  write token0 t0
  write token1 t1
  let d0 ← Binding.decimals token0B
  write decimals0 d0
  let d1 ← Binding.decimals token1B
  write decimals1 d1

/-- Deposit `a0`/`a1`. First mint is `a0`; later mint is the floor-min. Pulls after writes. -/
def addLiquidity (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1) : M Nat := do
  Tx.require (0 < a0.toNat) .Zero
  Tx.require (0 < a1.toNat) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      pure a0.toNat
    else do
      Tx.require (0 < r0) .Zero
      Tx.require (0 < r1) .Zero
      let s0 ← Tx.mulDivDown a0.toNat ts r0
      let s1 ← Tx.mulDivDown a1.toNat ts r1
      if s0 ≤ s1 then pure s0 else pure s1
  Tx.require (0 < minted) .ZeroShares
  let r0' ← r0 +? a0.toNat
  write reserve0 r0'
  let r1' ← r1 +? a1.toNat
  write reserve1 r1'
  let ts' ← minted +? ts
  write totalShares ts'
  let bal ← read shares[who]
  let bal' ← minted +? bal
  write shares[who] bal'
  let _ ← Binding.transferFrom token0B who me a0.toNat
  let _ ← Binding.transferFrom token1B who me a1.toNat
  Tx.emit (.AddLiquidity who a0 a1 (Amount.ofNat minted))
  pure minted

/-- Burn `s` and send `⌊s * r_i / S⌋` of each token. Transfers after writes. -/
def removeLiquidity (s : Amount SHARE shareScale) : M (Nat × Nat) := do
  Tx.require (0 < s.toNat) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s.toNat ≤ bal) .InsufficientShares
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  Tx.require (0 < ts) .Zero
  let out0 ← Tx.mulDivDown s.toNat r0 ts
  let out1 ← Tx.mulDivDown s.toNat r1 ts
  Tx.require (0 < out0) .ZeroOut
  Tx.require (0 < out1) .ZeroOut
  let bal' ← bal -? s.toNat
  write shares[who] bal'
  let ts' ← ts -? s.toNat
  write totalShares ts'
  let r0' ← r0 -? out0
  write reserve0 r0'
  let r1' ← r1 -? out1
  write reserve1 r1'
  let _ ← Binding.transfer token0B who out0
  let _ ← Binding.transfer token1B who out1
  Tx.emit (.RemoveLiquidity who (Amount.ofNat out0) (Amount.ofNat out1) s)
  pure (out0, out1)

/-- Sell `amountIn` of token0. `out = ⌊dx * r1 / (r0 + dx)⌋`. -/
def swap0for1 (amountIn : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1) : M Nat := do
  Tx.require (0 < amountIn.toNat) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let den ← r0 +? amountIn.toNat
  let out ← Tx.mulDivDown amountIn.toNat r1 den
  Tx.require (minOut.toNat ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let r0' ← r0 +? amountIn.toNat
  write reserve0 r0'
  let r1' ← r1 -? out
  write reserve1 r1'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let _ ← Binding.transferFrom token0B who me amountIn.toNat
  let _ ← Binding.transfer token1B who out
  Tx.emit (.Swap0for1 who amountIn (Amount.ofNat out))
  pure out

/-- Sell `amountIn` of token1. Symmetric to `swap0for1`. -/
def swap1for0 (amountIn : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0) : M Nat := do
  Tx.require (0 < amountIn.toNat) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let den ← r1 +? amountIn.toNat
  let out ← Tx.mulDivDown amountIn.toNat r0 den
  Tx.require (minOut.toNat ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let r1' ← r1 +? amountIn.toNat
  write reserve1 r1'
  let r0' ← r0 -? out
  write reserve0 r0'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let _ ← Binding.transferFrom token1B who me amountIn.toNat
  let _ ← Binding.transfer token0B who out
  Tx.emit (.Swap1for0 who amountIn (Amount.ofNat out))
  pure out

def getReserves : M (Nat × Nat) := do
  let r0 ← read reserve0
  let r1 ← read reserve1
  pure (r0, r1)

def sharesOf (who : Address) : M Nat := read shares[who]

def quote0for1 (amountIn : Amount TOKEN0 scale0) : M Nat := do
  Tx.require (0 < amountIn.toNat) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  let den ← r0 +? amountIn.toNat
  Tx.mulDivDown amountIn.toNat r1 den

end Amm

set_option maxHeartbeats 800000

lsc_schema Amm
lsc_reify Amm.constructor Amm.addLiquidity Amm.removeLiquidity
lsc_reify Amm.swap0for1 Amm.swap1for0 Amm.getReserves Amm.sharesOf Amm.quote0for1
lsc_contract Amm constructor addLiquidity removeLiquidity swap0for1 swap1for0 getReserves sharesOf quote0for1

namespace Amm

def smokeCtx : Ctx := { sender := 2, self := 1 }

def smokeEmpty : World Storage Ext Event where
  self := {
    reserve0 := 0, reserve1 := 0, totalShares := 0
    shares := fun _ => 0
    token0 := 10, token1 := 11
    decimals0 := 18, decimals1 := 18 }
  ext := {
    token0 := { balances := fun a => if a = (2 : Address) then 1000 else 0 }
    token1 := { balances := fun a => if a = (2 : Address) then 2000 else 0 } }

def smokePool : World Storage Ext Event where
  self := {
    reserve0 := 100, reserve1 := 200, totalShares := 100
    shares := fun a => if a = (2 : Address) then 100 else 0
    token0 := 10, token1 := 11
    decimals0 := 18, decimals1 := 18 }
  ext := {
    token0 := { balances := fun a => if a = (1 : Address) then 100 else if a = (2 : Address) then 900 else 0 }
    token1 := { balances := fun a => if a = (1 : Address) then 200 else if a = (2 : Address) then 1800 else 0 } }

def okNat (r : Except (Err Error) (Nat × World Storage Ext Event)) : Option Nat :=
  match r with
  | .ok (n, _) => some n
  | .error _ => none

def okPair (r : Except (Err Error) ((Nat × Nat) × World Storage Ext Event)) : Option (Nat × Nat) :=
  match r with
  | .ok (p, _) => some p
  | .error _ => none

def quoteZeroReverts : Bool :=
  match Tx.run (quote0for1 (Amount.ofNat 0)) smokeCtx smokePool with
  | .error (.user .Zero) => true
  | _ => false

end Amm

#guard Amm.okNat (Lsc.Tx.run (Amm.addLiquidity (Lsc.Amount.ofNat 100) (Lsc.Amount.ofNat 200))
    Amm.smokeCtx Amm.smokeEmpty) == some 100
#guard Amm.okNat (Lsc.Tx.run (Amm.quote0for1 (Lsc.Amount.ofNat 100))
    Amm.smokeCtx Amm.smokePool) == some 100
#guard Amm.okPair (Lsc.Tx.run Amm.getReserves Amm.smokeCtx Amm.smokePool) == some (100, 200)
#guard Amm.okNat (Lsc.Tx.run (Amm.sharesOf 2) Amm.smokeCtx Amm.smokePool) == some 100
#guard Amm.quoteZeroReverts
