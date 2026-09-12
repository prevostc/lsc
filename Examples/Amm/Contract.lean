import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20

/-!
# Amm — constant-product pool with two IERC20 bindings

No fee. First LP is minted `a0` shares (no `sqrt`). Later LPs get
`min(⌊S · a0 / r0⌋, ⌊S · a1 / r1⌋)`. Swaps use Uniswap-style
`⌊r_out · dx / (r_in + dx)⌋` so `k = r0 * r1` cannot decrease.

External calls run **after** requires and storage updates. That is sound
here because `Conforms` / `NoInterfere` exclude reentrancy (see
`docs/internals/SECURITY_MODEL.md` and `INTERFACE_MODEL.md`).
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Amm

def token0 : Asset := ⟨`token0, none⟩
def token1 : Asset := ⟨`token1, none⟩
def lpShare : Asset := ⟨`lpShare, some 18⟩

structure Storage where
  token0Ref : Ref IERC20 token0
  token1Ref : Ref IERC20 token1
  reserve0 : Amount token0
  reserve1 : Amount token1
  totalShares : Amount lpShare
  shares : Mapping Address (Amount lpShare)

structure Ext where
  token0 : Ghost
  token1 : Ghost

instance : Inhabited Ext := ⟨⟨{}, {}⟩⟩

def token0B : Binding IERC20 Storage Ext :=
  ⟨(·.token0Ref.addr), (·.token0), fun x g => { x with token0 := g }⟩

def token1B : Binding IERC20 Storage Ext :=
  ⟨(·.token1Ref.addr), (·.token1), fun x g => { x with token1 := g }⟩

inductive Event
  | AddLiquidity (who : Address) (a0 : Amount token0) (a1 : Amount token1)
      (sharesOut : Amount lpShare)
  | RemoveLiquidity (who : Address) (a0 : Amount token0) (a1 : Amount token1)
      (sharesIn : Amount lpShare)
  | Swap0for1 (who : Address) (a0 : Amount token0) (a1 : Amount token1)
  | Swap1for0 (who : Address) (a1 : Amount token1) (a0 : Amount token0)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  | ZeroShares
  | ZeroOut
  | InsufficientShares
  | InsufficientOutput
  | SameToken
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

/-- Bind two distinct tokens. -/
def constructor (t0 t1 : Address) : M Unit := do
  Tx.require (t0 ≠ t1) .SameToken
  write token0Ref { addr := t0 }
  write token1Ref { addr := t1 }

/-- Deposit `a0`/`a1`. First mint is `a0`; later mint is the floor-min. Pulls after writes. -/
def addLiquidity (a0 : Amount token0) (a1 : Amount token1) : M (Amount lpShare) := do
  Tx.require (0 < a0) .Zero
  Tx.require (0 < a1) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      pure (Amount.ofWord a0.raw)
    else do
      Tx.require (0 < r0) .Zero
      Tx.require (0 < r1) .Zero
      let s0 ← Amount.mulDivDown ts a0 r0
      let s1 ← Amount.mulDivDown ts a1 r1
      if s0 ≤ s1 then pure s0 else pure s1
  Tx.require (0 < minted) .ZeroShares
  let r0' ← r0 +? a0
  write reserve0 r0'
  let r1' ← r1 +? a1
  write reserve1 r1'
  let ts' ← minted +? ts
  write totalShares ts'
  let bal ← read shares[who]
  let bal' ← minted +? bal
  write shares[who] bal'
  Binding.safeTransferFrom token0B who me a0 .TransferFailed
  Binding.safeTransferFrom token1B who me a1 .TransferFailed
  Tx.emit (.AddLiquidity who a0 a1 minted)
  pure minted

/-- Burn `s` and send `⌊r_i · s / S⌋` of each token. Transfers after writes. -/
def removeLiquidity (s : Amount lpShare) : M (Amount token0 × Amount token1) := do
  Tx.require (0 < s) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s ≤ bal) .InsufficientShares
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  Tx.require (0 < ts) .Zero
  let out0 ← Amount.mulDivDown r0 s ts
  let out1 ← Amount.mulDivDown r1 s ts
  Tx.require (0 < out0) .ZeroOut
  Tx.require (0 < out1) .ZeroOut
  let bal' ← bal -? s
  write shares[who] bal'
  let ts' ← ts -? s
  write totalShares ts'
  let r0' ← r0 -? out0
  write reserve0 r0'
  let r1' ← r1 -? out1
  write reserve1 r1'
  Binding.safeTransfer token0B who out0 .TransferFailed
  Binding.safeTransfer token1B who out1 .TransferFailed
  Tx.emit (.RemoveLiquidity who out0 out1 s)
  pure (out0, out1)

/-- Sell `amountIn` of token0. `out = ⌊r1 · dx / (r0 + dx)⌋`. -/
def swap0for1 (amountIn : Amount token0) (minOut : Amount token1) : M (Amount token1) := do
  Tx.require (0 < amountIn) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let den ← r0 +? amountIn
  let out ← Amount.mulDivDown r1 amountIn den
  Tx.require (minOut ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let r0' ← r0 +? amountIn
  write reserve0 r0'
  let r1' ← r1 -? out
  write reserve1 r1'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  Binding.safeTransferFrom token0B who me amountIn .TransferFailed
  Binding.safeTransfer token1B who out .TransferFailed
  Tx.emit (.Swap0for1 who amountIn out)
  pure out

/-- Sell `amountIn` of token1. Symmetric to `swap0for1`. -/
def swap1for0 (amountIn : Amount token1) (minOut : Amount token0) : M (Amount token0) := do
  Tx.require (0 < amountIn) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let den ← r1 +? amountIn
  let out ← Amount.mulDivDown r0 amountIn den
  Tx.require (minOut ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let r1' ← r1 +? amountIn
  write reserve1 r1'
  let r0' ← r0 -? out
  write reserve0 r0'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  Binding.safeTransferFrom token1B who me amountIn .TransferFailed
  Binding.safeTransfer token0B who out .TransferFailed
  Tx.emit (.Swap1for0 who amountIn out)
  pure out

def getReserves : M (Amount token0 × Amount token1) := do
  let r0 ← read reserve0
  let r1 ← read reserve1
  pure (r0, r1)

def sharesOf (who : Address) : M (Amount lpShare) := read shares[who]

def quote0for1 (amountIn : Amount token0) : M (Amount token1) := do
  Tx.require (0 < amountIn) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  let den ← r0 +? amountIn
  Amount.mulDivDown r1 amountIn den

end Amm

set_option maxHeartbeats 4000000

lsc_schema Amm
lsc_reify Amm.constructor Amm.addLiquidity Amm.removeLiquidity
lsc_reify Amm.swap0for1 Amm.swap1for0 Amm.getReserves Amm.sharesOf Amm.quote0for1
lsc_contract Amm constructor addLiquidity removeLiquidity swap0for1 swap1for0 getReserves sharesOf quote0for1

namespace Amm

def smokeCtx : Ctx := { sender := 2, self := 1 }

def smokeEmpty : World Storage Ext Event where
  self := {
    token0Ref := ⟨10⟩, token1Ref := ⟨11⟩
    reserve0 := 0, reserve1 := 0, totalShares := 0
    shares := fun _ => 0 }
  ext := {
    token0 := { balances := fun a => if a = (2 : Address) then 1000 else 0 }
    token1 := { balances := fun a => if a = (2 : Address) then 2000 else 0 } }

def smokePool : World Storage Ext Event where
  self := {
    token0Ref := ⟨10⟩, token1Ref := ⟨11⟩
    reserve0 := 100, reserve1 := 200, totalShares := 100
    shares := fun a => if a = (2 : Address) then 100 else 0 }
  ext := {
    token0 := { balances := fun a => if a = (1 : Address) then 100 else if a = (2 : Address) then 900 else 0 }
    token1 := { balances := fun a => if a = (1 : Address) then 200 else if a = (2 : Address) then 1800 else 0 } }

def okNat (r : Except (Err Error) (Amount lpShare × World Storage Ext Event)) : Option Nat :=
  match r with
  | .ok (n, _) => some n.raw
  | .error _ => none

def okQuote (r : Except (Err Error) (Amount token1 × World Storage Ext Event)) : Option Nat :=
  match r with
  | .ok (n, _) => some n.raw
  | .error _ => none

def okPair (r : Except (Err Error) ((Amount token0 × Amount token1) × World Storage Ext Event)) :
    Option (Nat × Nat) :=
  match r with
  | .ok ((a, b), _) => some (a.raw, b.raw)
  | .error _ => none

def quoteZeroReverts : Bool :=
  match Tx.run (quote0for1 0) smokeCtx smokePool with
  | .error (.user .Zero) => true
  | _ => false

end Amm

#guard Amm.okNat (Lsc.Tx.run (Amm.addLiquidity 100 200)
    Amm.smokeCtx Amm.smokeEmpty) == some 100
#guard Amm.okQuote (Lsc.Tx.run (Amm.quote0for1 100)
    Amm.smokeCtx Amm.smokePool) == some 100
#guard Amm.okPair (Lsc.Tx.run Amm.getReserves Amm.smokeCtx Amm.smokePool) == some (100, 200)
#guard (match Lsc.Tx.run (Amm.sharesOf 2) Amm.smokeCtx Amm.smokePool with
    | .ok (n, _) => n.raw == 100
    | _ => false)
#guard Amm.quoteZeroReverts
