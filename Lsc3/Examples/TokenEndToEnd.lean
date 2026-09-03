import Lsc3.Examples.Token
import Lsc3.Compile.Contract
import Lsc3.EVM.Step

/-!
# Token end-to-end: init + mapping reads on the EVM machine
-/

namespace TokenEndToEnd

open Lsc3 Lsc3.Compile Lsc3.EVM

def packCall (sel : Nat) (args : List Nat := []) : List UInt8 :=
  let selBytes := (List.range 4).map fun i => UInt8.ofNat ((sel / (256 ^ (3 - i))) % 256)
  let argBytes := args.flatMap fun n =>
    (List.range 32).map fun i => UInt8.ofNat ((n / (256 ^ (31 - i))) % 256)
  selBytes ++ argBytes

def mkEnv (code calldata : List UInt8) (caller : Nat := 2) : Env :=
  { code := code, calldata := calldata, address := 1, caller := caller, callvalue := 0,
    timestamp := 0, number := 0 }

def decodeWord (data : List UInt8) : Nat :=
  (List.range (min 32 data.length)).foldl (fun acc i => acc * 256 + UInt8.toNat data[i]!) 0

def runCall (code : List UInt8) (calldata : List UInt8) (storage : Storage)
    (caller : Nat := 2) : IO (Option (Halt × State)) := do
  let env := mkEnv code calldata caller
  let s : State := { storage := storage }
  match run 100000 env s with
  | none => IO.println "fuel exhausted"; pure none
  | some r => pure (some r)

#eval! do
  match Token.bytecode with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    IO.println s!"bytecode ({code.length} bytes)"
    let initSel := selectorOf "init" [{ name := "owner", ty := .address }, { name := "supply", ty := .uint256 }]
    let supplySel := selectorOf "totalSupply" []
    let balSel := selectorOf "balanceOf" [{ name := "who", ty := .address }]
    let owner : Nat := 0xaaa
    let supply : Nat := 1000
    match ← runCall code (packCall initSel [owner, supply]) (fun _ => 0) with
    | some (Halt.stop, s1) => do
      IO.println s!"init: totalSupply slot = {s1.storage 1}"
      match ← runCall code (packCall supplySel) s1.storage with
      | some (Halt.ret data, _) => IO.println s!"totalSupply = {decodeWord data}"
      | some (h, _) => IO.println s!"totalSupply halt {repr h}"
      | none => pure ()
      match ← runCall code (packCall balSel [owner]) s1.storage with
      | some (Halt.ret data, _) => IO.println s!"balanceOf(owner) = {decodeWord data}"
      | some (h, _) => IO.println s!"balanceOf halt {repr h}"
      | none => pure ()
    | some (h, _) => IO.println s!"init halt {repr h}"
    | none => pure ()

end TokenEndToEnd
