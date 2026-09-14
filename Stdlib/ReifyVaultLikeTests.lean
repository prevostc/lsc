import Lsc.Lang.Reify
import Stdlib.SafeERC20

/-!
Slice 5a acceptance: a vault-like contract with `Amount`/`Bool` bodies, schema
`Ref` + non-first scalars, `safeTransferFrom`, the mulDiv operator, and
effect-based ABI kinds — **no** hand-written cores or certificates.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Stdlib.ReifyVaultLikeTests

def tAsset : Asset := ⟨`tAsset, none⟩
def tShare : Asset := ⟨`tShare, some 18⟩

structure IShares (s : Asset) where
  sharesOf : View (Address → Amount s)
  transferShares : Fn (Address → Amount s → Bool)
  deriving Interface

namespace VaultLike

structure Storage where
  asset : Ref (IERC20 tAsset)
  owner : Address
  paused : Flag
  totalShares : Amount tShare
  shares : Mapping Address (Amount tShare)

inductive Event
  | Deposit (who : Address) (assets : Amount tAsset) (sharesOut : Amount tShare)
  | Withdraw (who : Address) (assets : Amount tAsset) (sharesIn : Amount tShare)
  deriving DecidableEq, Repr

inductive Error
  | Paused
  | InsufficientShares
  | ZeroShares
  | TransferFailed
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

def constructor (owner tok : Address) : M Unit := do
  write owner owner
  write asset { addr := tok }
  write paused Flag.off

def deposit (n : Amount tAsset) : M (Amount tShare) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let tok ← read asset
  safeTransferFrom tok who me n .TransferFailed
  let one : Amount tAsset := 1
  let minted ← (Amount.ofWord (a := tShare) n.raw) mulDiv↓ one / one
  Tx.require (0 < minted) .ZeroShares
  let ts ← read totalShares
  write totalShares (← ts +? minted)
  let bal ← read shares[who]
  write shares[who] (← bal +? minted)
  Tx.emit (.Deposit who n minted)
  return minted

def withdraw (s : Amount tShare) : M (Amount tAsset) := do
  let p ← read paused
  Tx.require (p = Flag.off) .Paused
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s ≤ bal) .InsufficientShares
  let ts ← read totalShares
  let assetsOut ←
    if ts = 0 then
      pure (0 : Amount tAsset)
    else
      let one : Amount tShare := 1
      (Amount.ofWord (a := tAsset) s.raw) mulDiv↓ one / one
  write shares[who] (← bal -? s)
  write totalShares (← ts -? s)
  let tok ← read asset
  safeTransfer tok who assetsOut .TransferFailed
  Tx.emit (.Withdraw who assetsOut s)
  return assetsOut

def transferShares (to : Address) (s : Amount tShare) : M Bool := do
  let who ← Tx.sender
  let bal ← read shares[who]
  Tx.require (s ≤ bal) .InsufficientShares
  write shares[who] (← bal -? s)
  let dst ← read shares[to]
  write shares[to] (← dst +? s)
  return true

def sharesOf (a : Address) : M (Amount tShare) :=
  read shares[a]

def held : M (Amount tAsset) := do
  let tok ← read asset
  tok.balanceOf (← Tx.selfAddress)

/-- Pair-returning body with a CALL: must auto-certify (slice 6a). -/
def split (n : Amount tAsset) : M (Amount tAsset × Amount tShare) := do
  let who ← Tx.sender
  let me ← Tx.selfAddress
  let tok ← read asset
  safeTransferFrom tok who me n .TransferFailed
  let minted : Amount tShare := Amount.ofWord n.raw
  write totalShares minted
  write shares[who] minted
  return (n, minted)

end VaultLike

namespace KindProbe

structure Storage where
  dummy : Nat

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | Unused
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

def writeTrue : M Bool := do
  write dummy 1
  return true

def unitView : M Unit := do
  let _ ← read dummy
  pure ()

end KindProbe

end Stdlib.ReifyVaultLikeTests

open Stdlib.ReifyVaultLikeTests

lsc_schema VaultLike
lsc_contract VaultLike constructor deposit withdraw transferShares sharesOf held split
  implements IShares tShare

#check VaultLike.contract
#check VaultLike.constructor.core_denote
#check VaultLike.deposit.core_denote
#check VaultLike.withdraw.core_denote
#check VaultLike.transferShares.core_denote
#check VaultLike.sharesOf.core_denote
#check VaultLike.held.core_denote
#check VaultLike.split.core_denote
#check (VaultLike.impl : IShares.Impl tShare (World VaultLike.Storage ExtState VaultLike.Event))

#guard
  (match VaultLike.contract.functions.find? (·.name == "transferShares") with
    | some f => f.kind == FnKind.tx
    | none => false)
#guard
  (match VaultLike.contract.functions.find? (·.name == "sharesOf") with
    | some f => f.kind == FnKind.view
    | none => false)
#guard
  (match VaultLike.contract.functions.find? (·.name == "held") with
    | some f => f.kind == FnKind.view
    | none => false)
#guard
  (match VaultLike.contract.functions.find? (·.name == "deposit") with
    | some f => f.kind == FnKind.tx
    | none => false)
#guard
  (match VaultLike.contract.ctor with
    | some c => c.kind == FnKind.constructor
    | none => false)
#guard Core.isPureRead VaultLike.held.core
#guard Core.isPureRead VaultLike.sharesOf.core
#guard !Core.isPureRead VaultLike.deposit.core
#guard !Core.isPureRead VaultLike.transferShares.core
#guard (VaultLike.deposit.core.effects.calls).contains 0x23b872dd
#guard (VaultLike.split.core.effects.calls).contains 0x23b872dd
#guard (VaultLike.held.core.effects.views).contains 0x70a08231

lsc_schema KindProbe
lsc_contract KindProbe writeTrue unitView

#check KindProbe.writeTrue.core_denote
#check KindProbe.unitView.core_denote
#guard
  (match KindProbe.contract.functions.find? (·.name == "writeTrue") with
    | some f => f.kind == FnKind.tx
    | none => false)
#guard
  (match KindProbe.contract.functions.find? (·.name == "unitView") with
    | some f => f.kind == FnKind.view
    | none => false)

def tokAddr : Address := 9

def toyOracle : Oracle ExtState where
  call _addr sel _args ext :=
    if sel == 0x23b872dd || sel == 0xa9059cbb then some ([1], ext) else none
  view _addr sel _args _ext :=
    if sel == 0x70a08231 then [42] else []

def toyWorld : World VaultLike.Storage ExtState VaultLike.Event :=
  { self := {
      asset := ⟨tokAddr⟩
      owner := 0
      paused := Flag.off
      totalShares := 0
      shares := fun _ => 0 }
    ext := default
    oracle := toyOracle }

#guard
  (match Tx.run (VaultLike.deposit (Amount.ofWord 5)) { sender := 5, self := 7 }
      toyWorld with
    | .ok (out, w') =>
        out.raw == 5 && w'.self.totalShares.raw == 5 &&
          (w'.self.shares 5).raw == 5
    | _ => false)

#guard
  (match Tx.run VaultLike.held { sender := 5, self := 7 } toyWorld with
    | .ok (a, w') => a.raw == 42 && w'.self.asset.addr == tokAddr
    | _ => false)
