import Lsc3.Examples.Counter
import Lsc3.Compile.Contract
import Lsc3.EVM.Step

/-!
# Counter end-to-end: Core → bytecode → EVM machine
-/

namespace CounterEndToEnd

open Lsc3 Lsc3.Compile Lsc3.EVM

/-- Standard ABI: 4-byte selector followed by 32-byte words. -/
def packCall (sel : Nat) (args : List Nat := []) : List UInt8 :=
  let selBytes := (List.range 4).map fun i => UInt8.ofNat ((sel / (256 ^ (3 - i))) % 256)
  let argBytes := args.flatMap fun n =>
    (List.range 32).map fun i => UInt8.ofNat ((n / (256 ^ (31 - i))) % 256)
  selBytes ++ argBytes

def mkEnv (code calldata : List UInt8) : Env :=
  { code := code, calldata := calldata, address := 1, caller := 2, callvalue := 0,
    timestamp := 0, number := 0 }

def decodeWord (data : List UInt8) : Nat :=
  (List.range (min 32 data.length)).foldl (fun acc i => acc * 256 + (data[i]!).toNat) 0

def runCall (code : List UInt8) (calldata : List UInt8) (storage : Nat := 0) : IO Unit := do
  let env := mkEnv code calldata
  let s : State := { storage := fun k => if k = 0 then storage else 0 }
  match run 100000 env s with
  | none => IO.println "run: fuel exhausted"
  | some (Halt.stop, s') =>
    IO.println s!"stop: storage[0] = {s'.storage 0}"
  | some (Halt.ret data, s') =>
    IO.println s!"ret: word = {decodeWord data}, storage[0] = {s'.storage 0}"
  | some (Halt.revert _, _) => IO.println "revert"
  | some (Halt.exceptional e, _) => IO.println s!"exception: {repr e}"

#eval! do
  match Counter.bytecode with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    IO.println s!"bytecode ({code.length} bytes)"
    IO.println "increment on 5"
    runCall code (packCall (selectorOf "increment" [])) 5
    IO.println "get on 42"
    runCall code (packCall (selectorOf "get" [])) 42
    IO.println "incrementBy 7 on 10"
    runCall code (packCall (selectorOf "incrementBy" [{ name := "n", ty := .uint256 }]) [7]) 10
    IO.println "decrement on 5"
    runCall code (packCall (selectorOf "decrement" [])) 5
    IO.println "decrement on 0"
    runCall code (packCall (selectorOf "decrement" [])) 0
    IO.println "incrementBy 0 (should revert)"
    runCall code (packCall (selectorOf "incrementBy" [{ name := "n", ty := .uint256 }]) [0]) 1

end CounterEndToEnd
