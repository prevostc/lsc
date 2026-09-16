import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20
import Stdlib.SafeERC20
import Stdlib.Scales

/-!
# CPAMM — constant-product AMM with LP fee and protocol-fee switch

Two typed `Ref (IERC20 …)` tokens. The swap fee is 30 bps of `amountIn`; LPs
keep it on the curve. When `feeTo ≠ 0`, a protocol share of that fee is skimmed
into `protocolFees*` and never enters `k`. External calls run after storage
writes; reentrancy is not modelled.
-/

open Lsc Lsc.Syntax Lsc.Stdlib Stdlib

namespace Cpamm

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
  protocolShareBps : Bps
  protocolFees0 : Amount asset0
  protocolFees1 : Amount asset1
  deriving Fields

open Storage.Fields

inductive Event
  | AddLiquidity (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
      (sharesOut : Amount lpShare)
  | RemoveLiquidity (who : Address) (a0 : Amount asset0) (a1 : Amount asset1)
      (sharesIn : Amount lpShare)
  | Swap (who : Address) (zeroForOne : Bool) (amountIn amountOut : Word)
  | ProtocolShareSet (bps : Bps)
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
  | InsufficientLiquidity
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

inductive SwapDirection
  | zeroForOne
  | oneForZero
  deriving DecidableEq, Repr

@[reducible] def SwapDirection.assetIn : SwapDirection → Asset
  | .zeroForOne => asset0
  | .oneForZero => asset1

@[reducible] def SwapDirection.assetOut : SwapDirection → Asset
  | .zeroForOne => asset1
  | .oneForZero => asset0

/-- `true` when selling token0. Event payload; ABI has no user inductive. -/
@[reducible] def SwapDirection.zeroForOneB : SwapDirection → Bool
  | .zeroForOne => true
  | .oneForZero => false

/-- Storage fields on the input/output side of a swap. -/
@[reducible] def SwapDirection.reserveIn :
    (d : SwapDirection) → Field Storage (Amount d.assetIn)
  | .zeroForOne => reserve0
  | .oneForZero => reserve1

@[reducible] def SwapDirection.reserveOut :
    (d : SwapDirection) → Field Storage (Amount d.assetOut)
  | .zeroForOne => reserve1
  | .oneForZero => reserve0

@[reducible] def SwapDirection.tokenIn :
    (d : SwapDirection) → Field Storage (Ref (IERC20 d.assetIn))
  | .zeroForOne => token0
  | .oneForZero => token1

@[reducible] def SwapDirection.tokenOut :
    (d : SwapDirection) → Field Storage (Ref (IERC20 d.assetOut))
  | .zeroForOne => token1
  | .oneForZero => token0

@[reducible] def SwapDirection.protocolFees :
    (d : SwapDirection) → Field Storage (Amount d.assetIn)
  | .zeroForOne => protocolFees0
  | .oneForZero => protocolFees1

/-- Constant-product quote: 0.3% fee, output and protocol take; oversized take reverts. -/
@[lsc_inline] def swapOut {a b : Asset} (rIn : Amount a) (rOut : Amount b)
    (amountIn : Amount a) (share : Bps) : M (Amount b × Amount a) := do
  let dxF ← amountIn mulDiv↓ 9970 / 10000
  let den ← rIn +? dxF
  let out ← rOut mulDiv↓ dxF / den
  let fee ← amountIn -? dxF
  let protoFee ← fee *?↓ share
  Tx.require (protoFee ≤ fee) .FeeTooHigh
  return (out, protoFee)

/-- Bind two distinct tokens and set the owner; protocol take starts disabled. -/
def constructor (owner t0 t1 : Address) : M Unit := do
  Tx.require (t0 ≠ t1) .SameToken
  write owner owner
  write token0 { addr := t0 }
  write token1 { addr := t1 }

/-- Uniswap-v2 minimum liquidity burned to address 0 on the first mint. -/
def MINIMUM_LIQUIDITY : Amount lpShare := 1000

/-- Mint `n` shares to `to` and bump `totalShares`. -/
@[lsc_inline] def mint (to : Address) (n : Amount lpShare) : M Unit := do
  write shares[to] (read shares[to] +? n)
  write totalShares (read totalShares +? n)

/-- Deposit `a0`/`a1`. First mint relabels `a0` as LP shares (two-asset pools
have no single decimals; Uniswap-v2 convention) and burns
`MINIMUM_LIQUIDITY` to address 0. Later mint is the floor-min. -/
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
      -- two-asset LP shares have no single decimals; Uniswap-v2 convention:
      -- token0's raw amount, minus MINIMUM_LIQUIDITY locked at address 0
      let raw := a0.asUnchecked lpShare
      Tx.require (MINIMUM_LIQUIDITY < raw) .InsufficientLiquidity
      mint 0 MINIMUM_LIQUIDITY
      raw -? MINIMUM_LIQUIDITY
    else
      Tx.require (0 < r0) .Zero
      Tx.require (0 < r1) .Zero
      let s0 ← ts mulDiv↓ a0 / r0
      let s1 ← ts mulDiv↓ a1 / r1
      if s0 ≤ s1 then s0 else s1
  Tx.require (0 < minted) .ZeroShares
  write reserve0 (r0 +? a0)
  write reserve1 (r1 +? a1)
  mint who minted
  let t0 ← read token0
  let t1 ← read token1
  safeTransferFrom t0 who me a0 .TransferFailed
  safeTransferFrom t1 who me a1 .TransferFailed
  Tx.emit (.AddLiquidity who a0 a1 minted)
  return minted

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
  write shares[who] (bal -? s)
  write totalShares (ts -? s)
  write reserve0 (r0 -? out0)
  write reserve1 (r1 -? out1)
  let t0 ← read token0
  let t1 ← read token1
  safeTransfer t0 who out0 .TransferFailed
  safeTransfer t1 who out1 .TransferFailed
  Tx.emit (.RemoveLiquidity who out0 out1 s)
  return (out0, out1)

/-- Sell `amountIn` on side `d`; reverts unless `out ≥ minOut`. -/
@[lsc_inline] def swap (d : SwapDirection) (amountIn : Amount d.assetIn)
    (minOut : Amount d.assetOut) : M (Amount d.assetOut) := do
  Tx.require (0 < amountIn) .Zero
  let rIn ← read d.reserveIn
  let rOut ← read d.reserveOut
  Tx.require (0 < rIn) .Zero
  Tx.require (0 < rOut) .Zero
  let ft ← read feeTo
  let ps ← read protocolShareBps
  let coeff : Bps := if ft = 0 then 0 else ps
  let (out, protoFee) ← swapOut rIn rOut amountIn coeff
  Tx.require (minOut ≤ out) .InsufficientOutput
  Tx.require (0 < out) .ZeroOut
  let taken ← amountIn -? protoFee
  write d.reserveIn (rIn +? taken)
  write d.reserveOut (rOut -? out)
  write d.protocolFees (read d.protocolFees +? protoFee)
  let who ← Tx.sender
  let me ← Tx.selfAddress
  safeTransferFrom (← read d.tokenIn) who me amountIn .TransferFailed
  safeTransfer (← read d.tokenOut) who out .TransferFailed
  Tx.emit (.Swap who d.zeroForOneB (AbiType.encode amountIn) (AbiType.encode out))
  return out

def swap0for1 (amountIn : Amount asset0) (minOut : Amount asset1) :
    M (Amount asset1) :=
  swap .zeroForOne amountIn minOut

def swap1for0 (amountIn : Amount asset1) (minOut : Amount asset0) :
    M (Amount asset0) :=
  swap .oneForZero amountIn minOut

/-- Owner sets the protocol's share of the swap fee, in bps of that fee. -/
def setProtocolShare (bps : Bps) : M Unit := do
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
  return (p0, p1)

/-- Current reserves. -/
def getReserves : M (Amount asset0 × Amount asset1) := do
  let r0 ← read reserve0
  let r1 ← read reserve1
  return (r0, r1)

/-- LP share balance of `who`. -/
def sharesOf (who : Address) : M (Amount lpShare) := read shares[who]

/-- Current protocol-fee buckets. -/
def protocolFees : M (Amount asset0 × Amount asset1) := do
  let p0 ← read protocolFees0
  let p1 ← read protocolFees1
  return (p0, p1)

end Cpamm

set_option maxHeartbeats 40000000

lsc_schema Cpamm
lsc_contract Cpamm constructor addLiquidity removeLiquidity swap0for1 swap1for0
  setProtocolShare setFeeTo collectProtocolFees getReserves sharesOf protocolFees

