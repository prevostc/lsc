import Examples.Vault.Contract

/-!
Vault smoke tests. The CALL oracle here always returns `true` for
`transfer`/`transferFrom`; it is not a conforming ERC-20.
-/

open Lsc Lsc.Stdlib Vault

namespace Vault

def smokeOracle : Oracle ExtState where
  call _addr sel _args ext :=
    if sel == 0x23b872dd || sel == 0xa9059cbb then some ([1], ext) else none
  view _addr sel _args _ext :=
    if sel == 0x70a08231 then [100] else []

def smokeCtx : Ctx := { sender := 2, self := 1 }

def smokeEmpty : World Storage ExtState Event where
  self := {
    asset := ⟨10⟩
    owner := 2
    paused := Flag.off
    totalShares := 0
    shares := fun _ => 0 }
  ext := default
  oracle := smokeOracle

def smokeFilled : World Storage ExtState Event where
  self := {
    asset := ⟨10⟩
    owner := 2
    paused := Flag.off
    totalShares := 100
    shares := fun a => if a = (2 : Address) then 100 else 0 }
  ext := default
  oracle := smokeOracle

end Vault

#guard
  (match Lsc.Tx.run (Vault.deposit 50) Vault.smokeCtx Vault.smokeEmpty with
    | .ok (n, _) => n.raw == 50
    | _ => false)

#guard
  (match Lsc.Tx.run (Vault.previewDeposit 50) Vault.smokeCtx Vault.smokeFilled with
    | .ok (n, w') => n.raw == 50 && w'.self.totalShares == 100
    | _ => false)

#guard
  (match Lsc.Tx.run Vault.isPaused Vault.smokeCtx Vault.smokeEmpty with
    | .ok (p, _) => p == Lsc.Flag.off
    | _ => false)
