import Lsc.Compiler.Yul
import YulSemantics.Interp
import YulSemantics.Dialect.EVMExec

/-!
# Executable Yul harness

Builds an `EvmState` from calldata / storage / `Ctx`, runs `Interp.run EVM.exec`, and
applies `committedState` so a revert matches `Tx`'s discarded world. `keccakOf` is
KeccakEngine (the dialect default is opaque).
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

structure RunOut where
  halt : Option (HaltKind × List UInt8)
  storage : U256 → U256
  logs : List LogEntry
  outcome : Outcome
  stuck : Bool

def mkEvmState (calldata : List UInt8) (storage : U256 → U256)
    (keccak : List UInt8 → U256) (ctx : Ctx) : EvmState :=
  let self : U256 := BitVec.ofNat 256 ctx.self
  { EvmState.init with
    storage
    env :=
      { EvmState.init.env with
        calldata
        caller := BitVec.ofNat 256 ctx.sender
        origin := BitVec.ofNat 256 ctx.sender
        address := self
        callvalue := BitVec.ofNat 256 ctx.value
        timestamp := BitVec.ofNat 256 ctx.timestamp
        number := BitVec.ofNat 256 ctx.blockNumber
        keccakOf := keccak
        storageOf := fun addr slot =>
          if accountKey addr = accountKey self then storage slot else 0 } }

def defaultFuel : Nat := 100000

/-- Run a block and observe the committed (caller-visible) state. -/
def runBlock (fuel : Nat) (prog : YBlock) (st0 : EvmState) : RunOut :=
  match Interp.run exec fuel prog st0 with
  | .ok (_, st, o) =>
    let st := committedState st0 st
    { halt := st.halted, storage := st.storage, logs := st.logs, outcome := o, stuck := false }
  | .stuck =>
    { halt := none, storage := st0.storage, logs := [], outcome := .normal, stuck := true }
  | .outOfFuel =>
    { halt := none, storage := st0.storage, logs := [], outcome := .normal, stuck := true }

def runContract (c : ContractDef) (calldata : List UInt8) (storage : U256 → U256)
    (ctx : Ctx) : Option RunOut := do
  let prog ← runtimeBlock c
  some (runBlock defaultFuel prog (mkEvmState calldata storage keccakOf ctx))

/-- Overlay a finite list of (slot, value) pairs; everything else is 0. -/
def storageOf (pairs : List (U256 × U256)) : U256 → U256 :=
  fun slot =>
    match pairs.find? (fun p => p.1 = slot) with
    | some p => p.2
    | none => 0

def u256 (n : Nat) : U256 := BitVec.ofNat 256 n

end Lsc.Compiler
