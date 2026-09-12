import Lsc.Lang.Amount
import Lsc.Lang.Reify
import Lsc.Lang.Inline
import Stdlib.ERC20
import Stdlib.SafeERC20
import Stdlib.Scales

/-!
# CPAMM (constant-product AMM with LP fee and protocol-fee switch)

Same storage prefix as `Amm` (reserves, shares, token slots), then owner,
fee recipient, protocol share, and protocol-fee buckets. The swap fee is
immutable (`FEE_BPS = 30`). A protocol share of that fee (not of `amountIn`)
is skimmed off the curve when `feeTo ≠ 0`. External calls run after storage
writes; `Conforms` / `NoInterfere` exclude reentrancy.
-/

open Lsc Lsc.Syntax Lsc.Stdlib Stdlib

namespace Cpamm

/-- Phantom markers. Scales are opaque (not Core literals), as in Amm. -/
structure TOKEN0 where
structure TOKEN1 where
structure SHARE where

opaque scale0 : Nat
opaque scale1 : Nat
def shareScale : Nat := WAD

/-- Basis-point denominator. -/
def BPS : Nat := 10000
/-- Immutable swap fee: 30 bps = 0.3% of `amountIn`. -/
def FEE_BPS : Nat := 30

structure Storage where
  reserve0 : Nat
  reserve1 : Nat
  totalShares : Nat
  shares : Mapping Address Nat
  token0 : IERC20.Ref
  token1 : IERC20.Ref
  decimals0 : Nat
  decimals1 : Nat
  owner : Address
  feeTo : Address
  protocolShareBps : Nat
  protocolFees0 : Nat
  protocolFees1 : Nat

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
  | ProtocolShareSet (bps : Nat)
  | FeeToSet (who : Address)
  | ProtocolFeesCollected (who : Address) (a0 : Amount TOKEN0 scale0) (a1 : Amount TOKEN1 scale1)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  | ZeroShares
  | ZeroOut
  | InsufficientShares
  | InsufficientOutput
  | SameToken
  | TransferFailed
  | NotOwner
  | FeeTooHigh
  | NoFeeTo
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

/-- Bind two distinct tokens, cache `decimals`, set owner. `feeTo` and the
protocol share start at 0 (disabled). -/
def constructor (owner t0 t1 : Address) : M Unit := do
  Tx.require (t0 ≠ t1) .SameToken
  write owner owner
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
  Binding.safeTransferFrom token0B who me a0.toNat .TransferFailed
  Binding.safeTransferFrom token1B who me a1.toNat .TransferFailed
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
  Binding.safeTransfer token0B who out0 .TransferFailed
  Binding.safeTransfer token1B who out1 .TransferFailed
  Tx.emit (.RemoveLiquidity who (Amount.ofNat out0) (Amount.ofNat out1) s)
  pure (out0, out1)

/-- Fee-less output `⌊dxF · rOut / (rIn + dxF)⌋`. Shared by both ABI swaps. -/
@[lsc_inline]
def swapOut (rIn rOut dx : Nat) : M Nat := do
  let dxF ← Tx.mulDivDown dx 9970 10000
  let den ← rIn +? dxF
  Tx.mulDivDown dxF rOut den

/-- Protocol take `⌊fee · coeff / BPS⌋` for a caller-chosen coefficient
(`0` when `feeTo = 0`, else `protocolShareBps`). -/
@[lsc_inline]
def swapProto (dx coeff : Nat) : M Nat := do
  let dxF ← Tx.mulDivDown dx 9970 10000
  let fee ← dx -? dxF
  Tx.mulDivDown fee coeff 10000

/-- Sell `amountIn` of token0. Output uses the fee-less notional `dxF`; the
protocol take never enters the curve. -/
def swap0for1 (amountIn : Amount TOKEN0 scale0) (minOut : Amount TOKEN1 scale1) : M Nat := do
  Tx.require (0 < amountIn.toNat) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let out ← swapOut r0 r1 amountIn.toNat
  Tx.require (minOut.toNat ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let ft ← read feeTo
  let who ← Tx.sender
  let me ← Tx.selfAddress
  -- Tail `if` so the two token calls are not join-duplicated in the certificate.
  if ft = 0 then do
    let r0' ← r0 +? amountIn.toNat
    write reserve0 r0'
    let r1' ← r1 -? out
    write reserve1 r1'
    Binding.safeTransferFrom token0B who me amountIn.toNat .TransferFailed
    Binding.safeTransfer token1B who out .TransferFailed
    Tx.emit (.Swap0for1 who amountIn (Amount.ofNat out))
    pure out
  else do
    let ps ← read protocolShareBps
    let proto ← swapProto amountIn.toNat ps
    let taken ← amountIn.toNat -? proto
    let r0' ← r0 +? taken
    write reserve0 r0'
    let r1' ← r1 -? out
    write reserve1 r1'
    let acc ← read protocolFees0
    let acc' ← acc +? proto
    write protocolFees0 acc'
    Binding.safeTransferFrom token0B who me amountIn.toNat .TransferFailed
    Binding.safeTransfer token1B who out .TransferFailed
    Tx.emit (.Swap0for1 who amountIn (Amount.ofNat out))
    pure out

/-- Sell `amountIn` of token1. Symmetric to `swap0for1`. -/
def swap1for0 (amountIn : Amount TOKEN1 scale1) (minOut : Amount TOKEN0 scale0) : M Nat := do
  Tx.require (0 < amountIn.toNat) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let out ← swapOut r1 r0 amountIn.toNat
  Tx.require (minOut.toNat ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let ft ← read feeTo
  let who ← Tx.sender
  let me ← Tx.selfAddress
  if ft = 0 then do
    let r1' ← r1 +? amountIn.toNat
    write reserve1 r1'
    let r0' ← r0 -? out
    write reserve0 r0'
    Binding.safeTransferFrom token1B who me amountIn.toNat .TransferFailed
    Binding.safeTransfer token0B who out .TransferFailed
    Tx.emit (.Swap1for0 who amountIn (Amount.ofNat out))
    pure out
  else do
    let ps ← read protocolShareBps
    let proto ← swapProto amountIn.toNat ps
    let taken ← amountIn.toNat -? proto
    let r1' ← r1 +? taken
    write reserve1 r1'
    let r0' ← r0 -? out
    write reserve0 r0'
    let acc ← read protocolFees1
    let acc' ← acc +? proto
    write protocolFees1 acc'
    Binding.safeTransferFrom token1B who me amountIn.toNat .TransferFailed
    Binding.safeTransfer token0B who out .TransferFailed
    Tx.emit (.Swap1for0 who amountIn (Amount.ofNat out))
    pure out

/-- Owner sets the protocol's share of the swap fee, in bps of that fee. -/
def setProtocolShare (bps : Nat) : M Unit := do
  let who ← Tx.sender
  let own ← read owner
  Tx.require (who = own) .NotOwner
  Tx.require (bps ≤ 10000) .FeeTooHigh
  write protocolShareBps bps
  Tx.emit (.ProtocolShareSet bps)

/-- Owner sets the protocol-fee recipient. Address 0 disables the take. -/
def setFeeTo (recipient : Address) : M Unit := do
  let who ← Tx.sender
  let own ← read owner
  Tx.require (who = own) .NotOwner
  write feeTo recipient
  Tx.emit (.FeeToSet recipient)

/-- `feeTo` withdraws both protocol buckets. Reserves are unchanged. -/
def collectProtocolFees : M (Nat × Nat) := do
  let who ← Tx.sender
  let ft ← read feeTo
  Tx.require (ft ≠ 0) .NoFeeTo
  Tx.require (who = ft) .NotOwner
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  write protocolFees0 0
  write protocolFees1 0
  Binding.safeTransfer token0B who p0 .TransferFailed
  Binding.safeTransfer token1B who p1 .TransferFailed
  Tx.emit (.ProtocolFeesCollected who (Amount.ofNat p0) (Amount.ofNat p1))
  pure (p0, p1)

def getReserves : M (Nat × Nat) := do
  let r0 ← read reserve0
  let r1 ← read reserve1
  pure (r0, r1)

def sharesOf (who : Address) : M Nat := read shares[who]

def protocolFees : M (Nat × Nat) := do
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  pure (p0, p1)

end Cpamm

set_option maxHeartbeats 8000000

lsc_schema Cpamm
lsc_reify Cpamm.constructor Cpamm.addLiquidity Cpamm.removeLiquidity
lsc_reify Cpamm.setProtocolShare Cpamm.setFeeTo Cpamm.collectProtocolFees
lsc_reify Cpamm.getReserves Cpamm.sharesOf Cpamm.protocolFees
lsc_reify Cpamm.swap0for1
lsc_reify Cpamm.swap1for0
lsc_contract Cpamm constructor addLiquidity removeLiquidity swap0for1 swap1for0
  setProtocolShare setFeeTo collectProtocolFees getReserves sharesOf protocolFees


namespace Cpamm

def smokeCtx : Ctx := { sender := 2, self := 1 }

def smokeEmpty : World Storage Ext Event where
  self := {
    reserve0 := 0, reserve1 := 0, totalShares := 0
    shares := fun _ => 0
    token0 := 10, token1 := 11
    decimals0 := 18, decimals1 := 18
    owner := 2, feeTo := 0, protocolShareBps := 0
    protocolFees0 := 0, protocolFees1 := 0 }
  ext := {
    token0 := { balances := fun a => if a = (2 : Address) then 100000 else 0 }
    token1 := { balances := fun a => if a = (2 : Address) then 200000 else 0 } }

def smokePool : World Storage Ext Event where
  self := {
    reserve0 := 1000, reserve1 := 2000, totalShares := 1000
    shares := fun a => if a = (2 : Address) then 1000 else 0
    token0 := 10, token1 := 11
    decimals0 := 18, decimals1 := 18
    owner := 2, feeTo := 0, protocolShareBps := 0
    protocolFees0 := 0, protocolFees1 := 0 }
  ext := {
    token0 := { balances := fun a =>
      if a = (1 : Address) then 1000 else if a = (2 : Address) then 99000 else 0 }
    token1 := { balances := fun a =>
      if a = (1 : Address) then 2000 else if a = (2 : Address) then 198000 else 0 } }

/-- Pool with protocol take enabled: 100% of the 0.3% swap fee. -/
def smokePoolProto : World Storage Ext Event where
  self := { smokePool.self with feeTo := 3, protocolShareBps := BPS }
  ext := smokePool.ext

def okNat (r : Except (Err Error) (Nat × World Storage Ext Event)) : Option Nat :=
  match r with
  | .ok (n, _) => some n
  | .error _ => none

def okPair (r : Except (Err Error) ((Nat × Nat) × World Storage Ext Event)) : Option (Nat × Nat) :=
  match r with
  | .ok (p, _) => some p
  | .error _ => none

def swap0World (w : World Storage Ext Event) : Option (World Storage Ext Event) :=
  match Tx.run (swap0for1 (Amount.ofNat 100) (Amount.ofNat 0)) smokeCtx w with
  | .ok (_, w') => some w'
  | .error _ => none

end Cpamm

#guard Cpamm.okNat (Lsc.Tx.run (Cpamm.addLiquidity (Lsc.Amount.ofNat 100) (Lsc.Amount.ofNat 200))
    Cpamm.smokeCtx Cpamm.smokeEmpty) == some 100
#guard Cpamm.okPair (Lsc.Tx.run Cpamm.getReserves Cpamm.smokeCtx Cpamm.smokePool) == some (1000, 2000)
#guard Cpamm.okNat (Lsc.Tx.run (Cpamm.sharesOf 2) Cpamm.smokeCtx Cpamm.smokePool) == some 1000
#guard Cpamm.okPair (Lsc.Tx.run Cpamm.protocolFees Cpamm.smokeCtx Cpamm.smokePool) == some (0, 0)
-- dx=100, dxF=99, out=⌊99·2000/1099⌋=180, feeTo=0 so proto=0, r0'=1100, r1'=1820
#guard (match Cpamm.swap0World Cpamm.smokePool with
    | some w' => w'.self.reserve0 == 1100 && w'.self.reserve1 == 1820
        && w'.self.protocolFees0 == 0 && w'.self.protocolFees1 == 0
    | none => false)
-- 100% protocol take: proto=1, r0'=1099, bucket0=1, r1' still 1820
#guard (match Cpamm.swap0World Cpamm.smokePoolProto with
    | some w' => w'.self.reserve0 == 1099 && w'.self.reserve1 == 1820
        && w'.self.protocolFees0 == 1 && w'.self.protocolFees1 == 0
    | none => false)
#guard (match Lsc.Tx.run (Cpamm.setProtocolShare 5000) Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (_, w') => w'.self.protocolShareBps == 5000 && w'.self.protocolFees0 == 0
    | _ => false)
#guard (match Lsc.Tx.run (Cpamm.setProtocolShare 5000)
      { Cpamm.smokeCtx with sender := 9 } Cpamm.smokePool with
    | .error (.user .NotOwner) => true
    | _ => false)
#guard (match Lsc.Tx.run (Cpamm.setProtocolShare 10001) Cpamm.smokeCtx Cpamm.smokePool with
    | .error (.user .FeeTooHigh) => true
    | _ => false)
