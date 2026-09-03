import Lsc3.Examples.Counter
import Lsc3.Compile.Contract
import Lsc3.EVM.Step

/-!
# Counter end-to-end: Core → bytecode → EVM machine
-/

namespace CounterEndToEnd

open Lsc3 Lsc3.Compile Lsc3.EVM

def counterErrors : List ErrorDef :=
  [{ name := "Zero", params := [] }]

def counterEvents : List EventDef :=
  [{ name := "Incremented", params := [{ name := "by_", ty := .uint256 }] }]

def counterFields : List FieldDef :=
  [{ name := "count", kind := .scalar, ty := .uint256 }]

def counterContract : ContractDef where
  name := "Counter"
  fields := counterFields
  functions := [
    { name := "increment", decl := `Counter.increment, kind := .tx, params := [], ret := .unit,
      core := Counter.increment.core },
    { name := "incrementBy", decl := `Counter.incrementBy, kind := .tx,
      params := [{ name := "n", ty := .uint256 }], ret := .unit,
      core := Counter.incrementBy.core },
    { name := "decrement", decl := `Counter.decrement, kind := .tx, params := [], ret := .unit,
      core := Counter.decrement.core },
    { name := "get", decl := `Counter.get, kind := .view, params := [], ret := .word,
      core := Counter.get.core }
  ]
  ctor := none
  events := counterEvents
  errors := counterErrors

def incrementSel : Nat := selectorOf "increment" []
def getSel : Nat := selectorOf "get" []

#eval! do
  match contractInstrs counterContract with
  | .error e => IO.println s!"instrs error: {e}"
  | .ok instrs => IO.println s!"labels: {layoutLabels instrs}"

#eval! do
  match compileContract counterContract with
  | .error e => IO.println s!"compile error: {e}"
  | .ok bytes => IO.println s!"bytecode ({bytes.length} bytes): {toHex bytes}"

/-- Pack a function call: selector left-padded in a 32-byte ABI word, then args. -/
def packCall (sel : Nat) (args : List Nat := []) : List UInt8 :=
  let word := sel * (2 ^ 224)
  let selWord := (List.range 32).map fun i => UInt8.ofNat ((word / (256 ^ (31 - i))) % 256)
  let argBytes := args.flatMap fun n =>
    (List.range 32).map fun i => UInt8.ofNat ((n / (256 ^ (31 - i))) % 256)
  selWord ++ argBytes

def mkEnv (code calldata : List UInt8) : Env :=
  { code := code, calldata := calldata, address := 1, caller := 2, callvalue := 0,
    timestamp := 0, number := 0 }

def runCallDebug (code : List UInt8) (calldata : List UInt8) (storage : Nat := 0) (maxSteps : Nat := 200) : IO Unit := do
  let env := mkEnv code calldata
  let mut s : State := { storage := fun k => if k = 0 then storage else 0 }
  let mut fuel := maxSteps
  while fuel > 0 do
    match step env s with
    | StepResult.halt (.exceptional .badJumpDest) _ =>
      IO.println s!"badJumpDest at pc={s.pc}, stack={s.stack}"; return
    | StepResult.halt h _ => IO.println s!"halt {repr h} at pc={s.pc}"; return
    | StepResult.next s' =>
      s := s'
      fuel := fuel - 1
  IO.println "fuel exhausted in debug"

def runCall (code : List UInt8) (calldata : List UInt8) (storage : Nat := 0) : IO Unit := do
  let env := mkEnv code calldata
  let s : State := { storage := fun k => if k = 0 then storage else 0 }
  match run 100000 env s with
  | none => IO.println "run: fuel exhausted"
  | some (Halt.stop, s') =>
    IO.println s!"stop: storage[0] = {s'.storage 0}, stack = {s'.stack}"
  | some (Halt.ret data, s') =>
    let word := (List.range (min 32 data.length)).foldl (fun acc i =>
      acc * 256 + (data[i]!).toNat) 0
    IO.println s!"ret: word = {word}, storage[0] = {s'.storage 0}"
  | some (Halt.revert _, _) => IO.println "revert"
  | some (Halt.exceptional e, _) => IO.println s!"exception: {repr e}"

#eval! do
  match compileContract counterContract with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    let sel := incrementSel
    IO.println s!"calling increment (sel={sel}) on count=5"
    runCall code (packCall sel) 5

#eval! do
  match compileContract counterContract with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    let sel := getSel
    IO.println s!"calling get (sel={sel}) on count=42"
    runCall code (packCall sel) 42

end CounterEndToEnd
