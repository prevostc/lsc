import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Wealth
import Examples.Cpamm.Contract
import Stdlib.ERC20
import Stdlib.Scales

/-!
CPAMM spec: `claim` is LP share count; `Auth` is the victim's own
`removeLiquidity`. `Inv` is share-support, `protocolShareBps ≤ BPS`, and
each reserve plus that token's protocol bucket covered by the pool's live
token balance. `k` is a swap fact, not `Inv`. Between our transactions,
`cpammRely` lets `ext` change except that neither pool balance falls and
each token's `totalSupply` view stays the same — that is `ClaimMonoEnv`
for the share-count claim.
-/

open Lsc Lsc.Stdlib Lsc.Security Cpamm Stdlib

namespace Cpamm

abbrev Token0Impl := IERC20.Impl asset0 (WorldView ExtState)
abbrev Token1Impl := IERC20.Impl asset1 (WorldView ExtState)

/-- LP share count of `a`. -/
def claim : Claim Storage ExtState Event :=
  Claim.ofSelf fun a s => (s.shares a).raw

/-- Floor-pro-rata token0 claim of `a`. Zero when the supply is empty. -/
def claim0 : Claim Storage ExtState Event :=
  Claim.ofSelf fun a σ =>
    if σ.totalShares = 0 then 0
    else (σ.shares a).raw * σ.reserve0.raw / σ.totalShares.raw

/-- Floor-pro-rata token1 claim of `a`. Zero when the supply is empty. -/
def claim1 : Claim Storage ExtState Event :=
  Claim.ofSelf fun a σ =>
    if σ.totalShares = 0 then 0
    else (σ.shares a).raw * σ.reserve1.raw / σ.totalShares.raw

/-- Only a `removeLiquidity` by `a` itself may decrease `claim a`. -/
def Auth : AuthPred spec :=
  AuthPred.ofSelf fun a c _s =>
    match c.fn, c.args with
    | .removeLiquidity, _ => c.sender = a
    | _, _ => False

/-- `addLiquidity` is the only inflow of share-count; it is `0` on revert. -/
def inflow (c : Call spec) (w : World) : Nat :=
  match c.fn, c.args with
  | .addLiquidity, (a0, a1) =>
    match Tx.run (addLiquidity a0 a1) c.toCtx w with
    | .ok (n, _) => n.raw
    | .error _ => 0
  | _, _ => 0

/-- Live token0 balance of the pool, from the bound token's view. -/
def holdings0 (self : Address) (w : World) : Nat :=
  (w.self.token0.impl.balanceOf self w.view).raw

/-- Live token1 balance of the pool, from the bound token's view. -/
def holdings1 (self : Address) (w : World) : Nat :=
  (w.self.token1.impl.balanceOf self w.view).raw

def InvStorage (σ : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → σ.shares a = 0) ∧
    H.sum (fun a => (σ.shares a).raw) = σ.totalShares.raw

/-- Each reserve plus that token's protocol bucket is covered by the pool's
token balance, share balances have finite support, and the protocol share
is at most 100%. -/
def Inv (self : Address) (w : World) : Prop :=
  w.self.reserve0.raw + w.self.protocolFees0.raw ≤ holdings0 self w ∧
  w.self.reserve1.raw + w.self.protocolFees1.raw ≤ holdings1 self w ∧
  InvStorage w.self ∧
  w.self.protocolShareBps ≤ BPS

/-- After a trace, LP pro-rata claims plus protocol buckets are covered. -/
def CoversLpsAndProtocol (self : Address) (w : World) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → w.self.shares a = 0) ∧
    H.sum (fun a => claim0 a w) + w.self.protocolFees0.raw ≤ holdings0 self w ∧
    H.sum (fun a => claim1 a w) + w.self.protocolFees1.raw ≤ holdings1 self w

/-- `balanceOf` / `totalSupply` selectors. -/
def balSel0 : Nat := Interface.selector (I := IERC20 asset0) "balanceOf"
def balSel1 : Nat := Interface.selector (I := IERC20 asset1) "balanceOf"
def supplySel0 : Nat := Interface.selector (I := IERC20 asset0) "totalSupply"
def supplySel1 : Nat := Interface.selector (I := IERC20 asset1) "totalSupply"

/-- Live `balanceOf` of `who` at the bound token0, through `IERC20.Impl`. -/
def viewBal0 (t0 : IERC20.Ref asset0) (who : Address)
    (oracle : Oracle ExtState) (x : ExtState) : Amount asset0 :=
  t0.impl.balanceOf who { oracle, ext := x }

/-- Live `balanceOf` of `who` at the bound token1, through `IERC20.Impl`. -/
def viewBal1 (t1 : IERC20.Ref asset1) (who : Address)
    (oracle : Oracle ExtState) (x : ExtState) : Amount asset1 :=
  t1.impl.balanceOf who { oracle, ext := x }

/-- Live `totalSupply` of the bound token0, through `IERC20.Impl`. -/
def viewSupply0 (t0 : IERC20.Ref asset0)
    (oracle : Oracle ExtState) (x : ExtState) : Word :=
  (t0.impl.totalSupply { oracle, ext := x }).raw

/-- Live `totalSupply` of the bound token1, through `IERC20.Impl`. -/
def viewSupply1 (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState) (x : ExtState) : Word :=
  (t1.impl.totalSupply { oracle, ext := x }).raw

/-- Between our transactions the outside world may change `ext` arbitrarily,
except that neither pool token balance falls and each token's `totalSupply`
view stays the same. -/
def cpammRely (self : Address) (t0 : IERC20.Ref asset0) (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState) (x x' : ExtState) : Prop :=
  (viewBal0 t0 self oracle x).raw ≤ (viewBal0 t0 self oracle x').raw ∧
  (viewBal1 t1 self oracle x).raw ≤ (viewBal1 t1 self oracle x').raw ∧
  viewSupply0 t0 oracle x = viewSupply0 t0 oracle x' ∧
  viewSupply1 t1 oracle x = viewSupply1 t1 oracle x'

/-- A CALL at one token does not change the other's `balanceOf` / `totalSupply`
views. Distinct addresses are required; the oracle may otherwise share `ext`. -/
def TokensIndependent (t0 : IERC20.Ref asset0) (t1 : IERC20.Ref asset1)
    (oracle : Oracle ExtState) : Prop :=
  t0.addr ≠ t1.addr ∧
  (∀ sel args x rets x',
    oracle.call t0.addr sel args x = some (rets, x') →
      ∀ sel' args',
        oracle.view t1.addr sel' args' x' = oracle.view t1.addr sel' args' x) ∧
  (∀ sel args x rets x',
    oracle.call t1.addr sel args x = some (rets, x') →
      ∀ sel' args',
        oracle.view t0.addr sel' args' x' = oracle.view t0.addr sel' args' x)

/-- Fee-less notional input `⌊dx · (BPS.raw − FEE_BPS) / BPS.raw⌋`. -/
def dxFeeLess (dx : Nat) : Nat :=
  dx * (BPS.raw - FEE_BPS) / BPS.raw

/-- Swap fee `dx − dxF`. -/
def swapFee (dx : Nat) : Nat :=
  dx - dxFeeLess dx

/-- Protocol take: zero when `feeTo = 0`, else `⌊fee · protocolShareBps / BPS.raw⌋`. -/
def protoTake (feeTo protocolShareBps fee : Nat) : Nat :=
  if (feeTo : Nat) = 0 then 0 else fee * protocolShareBps / BPS.raw

def amountOutF (rIn rOut dx : Nat) : Nat :=
  let dxF := dxFeeLess dx
  rOut * dxF / (rIn + dxF)

/-- Shared quote used by both swap directions: `(out, proto)`. -/
def swapQuote (rIn rOut dx feeTo pShareBps : Nat) : Nat × Nat :=
  (amountOutF rIn rOut dx, protoTake feeTo pShareBps (swapFee dx))

end Cpamm
