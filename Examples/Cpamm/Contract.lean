import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20

/-!
# CPAMM — constant-product AMM with LP fee and protocol-fee switch

Two typed `Ref (IERC20 …)` tokens. The swap fee is 30 bps of `amountIn`; LPs
keep it on the curve. When `feeTo ≠ 0`, a protocol share of that fee is skimmed
into `protocolFees*` and never enters `k`. External calls run after storage
writes; reentrancy is not modelled.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Cpamm

/-- Basis-point denominator. -/
def BPS : Nat := 10000
/-- Immutable swap fee: 30 bps = 0.3% of `amountIn`. -/
def FEE_BPS : Nat := 30

def asset0 : Asset := ⟨`token0, none⟩
def asset1 : Asset := ⟨`token1, none⟩
def lpShare : Asset := ⟨`lpShare, some 18⟩

structure Storage where
  token0 : Ref (IERC20 asset0)
  token1 : Ref (IERC20 asset1)
  reserve0 : Amount asset0
  reserve1 : Amount asset1
  totalShares : Amount lpShare
  shares : Mapping Address (Amount lpShare)
  owner : Address
  feeTo : Address
  protocolShareBps : Word
  protocolFees0 : Amount asset0
  protocolFees1 : Amount asset1

inductive Event
  | AddLiquidity (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
      (sharesOut : Amount lpShare)
  | RemoveLiquidity (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
      (sharesIn : Amount lpShare)
  | Swap0for1 (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
  | Swap1for0 (who : Address) (a1 : Amount asset1) (a0 : Amount asset0)
  | ProtocolShareSet (bps : Word)
  | FeeToSet (who : Address)
  | ProtocolFeesCollected (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
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

abbrev M := Tx Storage ExtState Event Error

/-- Bind two distinct tokens and set the owner; protocol take starts disabled. -/
def constructor (owner t0 t1 : Address) : M Unit := do
  Tx.require (t0 ≠ t1) .SameToken
  write owner owner
  write token0 { addr := t0 }
  write token1 { addr := t1 }

/-- Deposit `a0`/`a1`. First mint is `a0`; later mint is the floor-min. -/
def addLiquidity (a0 : Amount asset0) (a1 : Amount asset1) : M (Amount lpShare) := do
  Tx.require (0 < a0) .Zero
  Tx.require (0 < a1) .Zero
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  let minted ←
    if ts = 0 then
      (1 : Amount lpShare) mulDiv↓ a0 / (1 : Amount asset0)
    else do
      Tx.require (0 < r0) .Zero
      Tx.require (0 < r1) .Zero
      let s0 ← ts mulDiv↓ a0 / r0
      let s1 ← ts mulDiv↓ a1 / r1
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
  let t0 ← read token0
  let t1 ← read token1
  safeTransferFrom t0 who me a0 .TransferFailed
  safeTransferFrom t1 who me a1 .TransferFailed
  Tx.emit (.AddLiquidity who a0 a1 minted)
  pure minted

/-- Burn `s` and send the floor-pro-rata of each reserve. -/
def removeLiquidity (s : Amount lpShare) : M (Amount asset0 × Amount asset1) := do
  Tx.require (0 < s) .Zero
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s ≤ bal) .InsufficientShares
  let r0 ← read reserve0
  let r1 ← read reserve1
  let ts ← read totalShares
  Tx.require (0 < ts) .Zero
  let out0 ← r0 mulDiv↓ s / ts
  let out1 ← r1 mulDiv↓ s / ts
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
  let t0 ← read token0
  let t1 ← read token1
  safeTransfer t0 who out0 .TransferFailed
  safeTransfer t1 who out1 .TransferFailed
  Tx.emit (.RemoveLiquidity who out0 out1 s)
  pure (out0, out1)

/-- Sell `amountIn` of token0. Output uses the 0.3%-fee notional; the protocol
take never enters the curve. -/
def swap0for1 (amountIn : Amount asset0) (minOut : Amount asset1) : M (Amount asset1) := do
  Tx.require (0 < amountIn) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let dxF ← amountIn mulDiv↓ (9970 : Amount asset0) / (10000 : Amount asset0)
  let den ← r0 +? dxF
  let out ← r1 mulDiv↓ dxF / den
  Tx.require (minOut ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let ft ← read feeTo
  let ps ← read protocolShareBps
  let coeffW ← if ft = 0 then pure (0 : Word) else pure ps
  let coeff ← (1 : Amount asset0) *? coeffW
  let fee ← amountIn -? dxF
  let proto ← fee mulDiv↓ coeff / (10000 : Amount asset0)
  let taken ← amountIn -? proto
  let r0' ← r0 +? taken
  write reserve0 r0'
  let r1' ← r1 -? out
  write reserve1 r1'
  let acc ← read protocolFees0
  let acc' ← acc +? proto
  write protocolFees0 acc'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let t0 ← read token0
  let t1 ← read token1
  safeTransferFrom t0 who me amountIn .TransferFailed
  safeTransfer t1 who out .TransferFailed
  Tx.emit (.Swap0for1 who amountIn out)
  pure out

/-- Sell `amountIn` of token1. Symmetric to `swap0for1`. -/
def swap1for0 (amountIn : Amount asset1) (minOut : Amount asset0) : M (Amount asset0) := do
  Tx.require (0 < amountIn) .Zero
  let r0 ← read reserve0
  let r1 ← read reserve1
  Tx.require (0 < r0) .Zero
  Tx.require (0 < r1) .Zero
  let dxF ← amountIn mulDiv↓ (9970 : Amount asset1) / (10000 : Amount asset1)
  let den ← r1 +? dxF
  let out ← r0 mulDiv↓ dxF / den
  Tx.require (minOut ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let ft ← read feeTo
  let ps ← read protocolShareBps
  let coeffW ← if ft = 0 then pure (0 : Word) else pure ps
  let coeff ← (1 : Amount asset1) *? coeffW
  let fee ← amountIn -? dxF
  let proto ← fee mulDiv↓ coeff / (10000 : Amount asset1)
  let taken ← amountIn -? proto
  let r1' ← r1 +? taken
  write reserve1 r1'
  let r0' ← r0 -? out
  write reserve0 r0'
  let acc ← read protocolFees1
  let acc' ← acc +? proto
  write protocolFees1 acc'
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let t1 ← read token1
  let t0 ← read token0
  safeTransferFrom t1 who me amountIn .TransferFailed
  safeTransfer t0 who out .TransferFailed
  Tx.emit (.Swap1for0 who amountIn out)
  pure out

/-- Owner sets the protocol's share of the swap fee, in bps of that fee. -/
def setProtocolShare (bps : Word) : M Unit := do
  let who ← Tx.sender
  let own ← read owner
  Tx.require (who = own) .NotOwner
  Tx.require (bps ≤ BPS) .FeeTooHigh
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
def collectProtocolFees : M (Amount asset0 × Amount asset1) := do
  let who ← Tx.sender
  let ft ← read feeTo
  Tx.require (ft ≠ 0) .NoFeeTo
  Tx.require (who = ft) .NotOwner
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  write protocolFees0 0
  write protocolFees1 0
  let t0 ← read token0
  let t1 ← read token1
  safeTransfer t0 who p0 .TransferFailed
  safeTransfer t1 who p1 .TransferFailed
  Tx.emit (.ProtocolFeesCollected who p0 p1)
  pure (p0, p1)

/-- Current reserves. -/
def getReserves : M (Amount asset0 × Amount asset1) := do
  let r0 ← read reserve0
  let r1 ← read reserve1
  pure (r0, r1)

/-- LP share balance of `who`. -/
def sharesOf (who : Address) : M (Amount lpShare) := read shares[who]

/-- Current protocol-fee buckets. -/
def protocolFees : M (Amount asset0 × Amount asset1) := do
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  pure (p0, p1)

end Cpamm

set_option maxHeartbeats 20000000

lsc_schema Cpamm

