import Lsc.Compile.BytecodeTest
import Lsc.Selectors
import EvmYul.Wheels
import EvmYul.EVM.Semantics
import EvmYul.State.AccountOps
import EvmYul.Maps.AccountMap
import EvmYul.State.BlockHeader
import EvmYul.State.Substate
import EvmYul.State.Block

open Lsc Lsc.BytecodeTest Lsc.Compile
open EvmYul (AccountAddress Account ExecutionEnv Storage Substate BlockHeader ProcessedBlocks)
open EvmYul.EVM (Ξ ExecutionResult ExecutionException)

namespace Lsc.BytecodeExecTest

private abbrev U256 := EvmYul.UInt256
private abbrev AcctMap := EvmYul.AccountMap .EVM

private def u (n : Nat) : U256 := EvmYul.UInt256.ofNat n

private def execFuel : Nat := 1_000_000
private def execGas : U256 := u 100_000_000

private def contractAddr : AccountAddress := 0x100
private def callerAddr : AccountAddress := 0x200

/-- Topic0 stub for EvmYul execution (256-bit keccak topics currently trip gas accounting). -/
def execEventTopic0 : Ident → Option Nat := fun _ => some 0

def execConfig : Config :=
  configFromContract counterDef execEventTopic0

private def fnSelector (name : Ident) : Nat :=
  match counterDef.functions.find? (·.name == name) with
  | some fn => (computeSelector fn).toNat
  | none => 0

def incrementSelector : Nat := fnSelector "increment"
def pauseSelector : Nat := fnSelector "pause"
def unpauseSelector : Nat := fnSelector "unpause"

def execCounterBytecode : ByteArray :=
  match contractToBytecode counterDef execEventTopic0 with
  | .ok bytes => bytes
  | .error e => panic! e

private def selectorCalldata (sel : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((sel >>> 24) &&& 0xff),
    UInt8.ofNat ((sel >>> 16) &&& 0xff),
    UInt8.ofNat ((sel >>> 8) &&& 0xff),
    UInt8.ofNat (sel &&& 0xff)
  ]

private def mkStorage (number paused owner : U256) : Storage :=
  (default : Storage).insert (u 0) number
    |>.insert (u 1) paused
    |>.insert (u 2) owner

private def mkAccount (code : ByteArray) (storage : Storage) : Account .EVM where
  code := code
  storage := storage
  nonce := u 0
  balance := u 0
  tstorage := default

private def mkAccountMap (code : ByteArray) (storage : Storage) : AcctMap :=
  (default : AcctMap).insert contractAddr (mkAccount code storage)

private def mkExecEnv (code calldata : ByteArray) : ExecutionEnv .EVM where
  codeOwner := contractAddr
  sender := callerAddr
  source := callerAddr
  weiValue := u 0
  calldata := calldata
  code := code
  gasPrice := 0
  header := (default : BlockHeader)
  depth := 0
  perm := true
  blobVersionedHashes := []

private def runCall (code calldata : ByteArray) (storage : Storage) :
    Except ExecutionException AcctMap :=
  let σ := mkAccountMap code storage
  let I := mkExecEnv code calldata
  let emptyCreated := (default : Batteries.RBSet AccountAddress compare)
  let emptyBlocks := (default : ProcessedBlocks)
  let emptySubstate := (default : Substate)
  match Ξ execFuel emptyCreated (default : BlockHeader) emptyBlocks σ σ execGas emptySubstate I with
  | .error e => .error e
  | .ok (.revert _ _) => .error ExecutionException.InvalidInstruction
  | .ok (.success (_, σ', _, _) _) => .ok σ'

private def storageSlot (σ : AcctMap) (slot : Nat) : Option U256 :=
  σ.find? contractAddr |>.map (·.lookupStorage (u slot))

def slot0AfterIncrement : Option U256 :=
  let storage := mkStorage (u 5) (u 0) (u 0)
  match runCall execCounterBytecode (selectorCalldata incrementSelector) storage with
  | .ok σ => storageSlot σ 0
  | _ => none

def slot1AfterPause : Option U256 :=
  let owner := u callerAddr.val
  let storage := mkStorage (u 5) (u 0) owner
  match runCall execCounterBytecode (selectorCalldata pauseSelector) storage with
  | .ok σ => storageSlot σ 1
  | _ => none

def slot1AfterUnpause : Option U256 :=
  let owner := u callerAddr.val
  let storage := mkStorage (u 5) (u 1) owner
  match runCall execCounterBytecode (selectorCalldata unpauseSelector) storage with
  | .ok σ => storageSlot σ 1
  | _ => none

def runSmokeTests : IO Unit := do
  match slot0AfterIncrement with
  | some v =>
    unless v == u 6 do
      panic! s!"increment: expected slot 0 = 6, got {v}"
  | none => panic! "increment call failed"
  match slot1AfterPause with
  | some v =>
    unless v == u 1 do
      panic! s!"pause: expected slot 1 = 1, got {v}"
  | none => panic! "pause call failed"
  match slot1AfterUnpause with
  | some v =>
    unless v == u 0 do
      panic! s!"unpause: expected slot 1 = 0, got {v}"
  | none => panic! "unpause call failed"
  IO.println "BytecodeExecTest smoke tests passed"

end Lsc.BytecodeExecTest
