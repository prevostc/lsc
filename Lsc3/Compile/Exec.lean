import Lsc3.Contract
import Lsc3.EVM.Step

/-!
# ABI call wrapper around `Lsc3.EVM.run`

Used by end-to-end tests and (later) `bytecode_ok` certificates: pack calldata, run the
machine, decode a single returned word.
-/

namespace Lsc3.Compile.Exec

open Lsc3 Lsc3.EVM

def packWord (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat ((n / (256 ^ (31 - i))) % 256)

def packCall (sel : Nat) (args : List Nat := []) : List UInt8 :=
  let selBytes := (List.range 4).map fun i => UInt8.ofNat ((sel / (256 ^ (3 - i))) % 256)
  selBytes ++ args.flatMap packWord

def decodeWord (data : List UInt8) : Nat :=
  (List.range (min 32 data.length)).foldl (fun acc i => acc * 256 + UInt8.toNat data[i]!) 0

def mkEnv (code calldata : List UInt8) (caller : Nat := 0) : Env :=
  { code := code, calldata := calldata, address := 1, caller := caller, callvalue := 0,
    timestamp := 0, number := 0 }

inductive Outcome
  | stop (storage : Storage)
  | ret (word : Nat) (storage : Storage)
  | revert
  | fail (e : Exception)
  | timeout

def exec (code calldata : List UInt8) (storage : Storage) (caller : Nat := 0)
    (fuel : Nat := 100000) : Outcome :=
  match run fuel (mkEnv code calldata caller) { storage := storage } with
  | none => .timeout
  | some (Halt.stop, s) => .stop s.storage
  | some (Halt.ret data, s) => .ret (decodeWord data) s.storage
  | some (Halt.revert _, _) => .revert
  | some (Halt.exceptional e, _) => .fail e

def slot0 (n : Nat) : Storage := fun k => if k = 0 then n else 0

/-- Run and return the raw halt + state (logs, memory, storage). -/
def execState (code calldata : List UInt8) (storage : Storage) (caller : Nat := 0)
    (fuel : Nat := 100000) : Option (Halt × State) :=
  run fuel (mkEnv code calldata caller) { storage := storage }

/-- Execute creation bytecode; `some runtime` iff the preamble `RETURN`s the payload. -/
def deploy (code : List UInt8) (fuel : Nat := 100000) : Option (List UInt8) :=
  match run fuel (mkEnv code []) { storage := fun _ => 0 } with
  | some (Halt.ret data, _) => some data
  | _ => none

@[simp] theorem decodeWord_nil : decodeWord [] = 0 := rfl

@[simp] theorem packWord_length (n : Nat) : (packWord n).length = 32 := by
  simp [packWord]

theorem length_flatMap_packWord (args : List Nat) :
    (args.flatMap packWord).length = 32 * args.length := by
  induction args with
  | nil => simp
  | cons n ns ih =>
    simp [packWord_length, ih]
    omega

@[simp] theorem packCall_length (sel : Nat) (args : List Nat) :
    (packCall sel args).length = 4 + 32 * args.length := by
  simp only [packCall, List.length_append, List.length_map, List.length_range,
    length_flatMap_packWord]

@[simp] theorem decodeWord_packWord_zero : decodeWord (packWord 0) = 0 := rfl

@[simp] theorem decodeWord_packWord_one : decodeWord (packWord 1) = 1 := rfl

@[simp] theorem decodeWord_packWord_42 : decodeWord (packWord 42) = 42 := rfl

end Lsc3.Compile.Exec
