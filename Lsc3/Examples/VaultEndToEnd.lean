import Lsc3.Examples.Vault
import Lsc3.Compile.Exec

/-!
# Vault end-to-end: deposit / withdraw / pause on the EVM machine
-/

namespace VaultEndToEnd

open Lsc3 Lsc3.EVM Lsc3.Compile.Exec

def depositSel : Nat := selectorOf "deposit" [{ name := "assets", ty := .uint256 }]
def withdrawSel : Nat := selectorOf "withdraw" [{ name := "sharesIn", ty := .uint256 }]
def previewDepSel : Nat := selectorOf "previewDeposit" [{ name := "assets", ty := .uint256 }]
def previewRedSel : Nat := selectorOf "previewRedeem" [{ name := "sharesIn", ty := .uint256 }]
def pauseSel : Nat := selectorOf "pause" []
def unpauseSel : Nat := selectorOf "unpause" []
def pausedSel : Nat := selectorOf "paused?" []

/-- Vault slots: `totalAssets=0`, `totalShares=1`, `shares=2` (map), `paused=3`, `owner=4`, `asset=5`. -/
def mkStorage (ta ts paused owner : Nat) (asset : Nat := 0xeee) : Storage :=
  fun k =>
    if k = 0 then ta
    else if k = 1 then ts
    else if k = 3 then paused
    else if k = 4 then owner
    else if k = 5 then asset
    else 0

/-- Oracle that treats every CALL as success (honest ERC-20). -/
def okExt : Word → Nat → List Nat → Option (List Nat) := fun _ _ _ => some [1]

def formatOutcome : Outcome → String
  | .stop s => s!"stop (ta={s 0}, ts={s 1}, paused={s 3})"
  | .ret w s => s!"ret {w} (ta={s 0}, ts={s 1}, paused={s 3})"
  | .revert => "revert"
  | .fail e => s!"fail {repr e}"
  | .timeout => "timeout"

def emptyWorld (owner : Address) : World Vault.Storage Vault.Event :=
  { self :=
    { totalAssets := 0
      totalShares := 0
      shares := fun _ => 0
      paused := Flag.off
      owner := owner
      asset := 0xeee }
    ext := okExt }

#eval! do
  match Vault.bytecode with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    IO.println s!"bytecode ({code.length} bytes)"
    let owner : Nat := 0xaaa
    let who : Nat := 0xabc
    let st0 := mkStorage 0 0 0 owner
    IO.println s!"previewDeposit 100 on empty: {formatOutcome (exec code (packCall previewDepSel [100]) st0 (ext := okExt))}"
    match exec code (packCall depositSel [100]) st0 who (ext := okExt) with
    | .ret minted s1 => do
      IO.println s!"deposit 100 → minted {minted}, ta={s1 0} ts={s1 1}"
      IO.println s!"previewRedeem 100: {formatOutcome (exec code (packCall previewRedSel [100]) s1 (ext := okExt))}"
      match exec code (packCall withdrawSel [40]) s1 who (ext := okExt) with
      | .ret out s2 => do
        IO.println s!"withdraw 40 → {out} assets, ta={s2 0} ts={s2 1}"
        match exec code (packCall pauseSel) s2 owner (ext := okExt) with
        | .stop s3 => do
          IO.println s!"pause by owner: paused={s3 3}"
          IO.println s!"deposit while paused: {formatOutcome (exec code (packCall depositSel [10]) s3 who (ext := okExt))}"
          IO.println s!"pause by non-owner: {formatOutcome (exec code (packCall pauseSel) s2 who (ext := okExt))}"
          match execState code (packCall unpauseSel) s3 owner (ext := okExt) with
          | some (Halt.stop, s4) =>
            IO.println s!"unpause ok, paused={s4.storage 3}, logs={s4.logs.length}"
          | _ => IO.println "unpause: unexpected halt"
        | o => IO.println s!"pause: {formatOutcome o}"
      | o => IO.println s!"withdraw: {formatOutcome o}"
    | o => IO.println s!"deposit: {formatOutcome o}"
    let ctx : Ctx := { sender := who, self := 1 }
    let txMint : Option Nat :=
      match Tx.run (Vault.deposit 100) ctx (emptyWorld owner) with
      | .ok (m, _) => some (Amount.toNat m)
      | .error _ => none
    let evmMint : Option Nat :=
      match exec code (packCall depositSel [100]) st0 who (ext := okExt) with
      | .ret m _ => some m
      | _ => none
    IO.println s!"Tx vs EVM deposit 100: {txMint} vs {evmMint}"
    match Vault.deploy with
    | .error e => IO.println s!"deploy compile error: {e}"
    | .ok create =>
      match deploy create with
      | some runtime =>
        IO.println s!"deploy: {create.length} bytes → runtime {runtime.length} (match {decide (runtime == code)})"
      | none => IO.println "deploy: did not RETURN runtime"

end VaultEndToEnd
