import Lsc3.Examples.Counter
import Lsc3.Compile.Exec

/-!
# Counter end-to-end: Core → bytecode → EVM machine
-/

namespace CounterEndToEnd

open Lsc3 Lsc3.EVM Lsc3.Compile.Exec

def getSel : Nat := selectorOf "get" []
def incSel : Nat := selectorOf "increment" []
def incBySel : Nat := selectorOf "incrementBy" [{ name := "n", ty := .uint256 }]
def decSel : Nat := selectorOf "decrement" []

def runGet (n : Nat) : Outcome :=
  match Counter.bytecode with
  | .ok code => exec code (packCall getSel) (slot0 n)
  | .error _ => .timeout

def runInc (n : Nat) : Outcome :=
  match Counter.bytecode with
  | .ok code => exec code (packCall incSel) (slot0 n)
  | .error _ => .timeout

def runIncBy (n arg : Nat) : Outcome :=
  match Counter.bytecode with
  | .ok code => exec code (packCall incBySel [arg]) (slot0 n)
  | .error _ => .timeout

def runDec (n : Nat) : Outcome :=
  match Counter.bytecode with
  | .ok code => exec code (packCall decSel) (slot0 n)
  | .error _ => .timeout

def formatOutcome : Outcome → String
  | .stop s => s!"stop: storage[0] = {s 0}"
  | .ret w s => s!"ret: {w} (storage[0] = {s 0})"
  | .revert => "revert"
  | .fail e => s!"fail {repr e}"
  | .timeout => "timeout"

#eval! do
  match Counter.bytecode with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => IO.println s!"bytecode ({code.length} bytes)"
  IO.println s!"increment on 5: {formatOutcome (runInc 5)}"
  IO.println s!"get on 42: {formatOutcome (runGet 42)}"
  IO.println s!"incrementBy 7 on 10: {formatOutcome (runIncBy 10 7)}"
  IO.println s!"decrement on 5: {formatOutcome (runDec 5)}"
  IO.println s!"decrement on 0: {formatOutcome (runDec 0)}"
  IO.println s!"incrementBy 0: {formatOutcome (runIncBy 1 0)}"
  IO.println s!"increment at max word (should revert): {formatOutcome (runInc (wordBound - 1))}"
  let ctx : Ctx := { sender := 2, self := 1 }
  let incTx (n : Nat) : Option Nat :=
    match Tx.run Counter.increment ctx { self := { count := n } } with
    | .ok (_, w) => some w.self.count
    | .error _ => none
  let incEvm (n : Nat) : Option Nat :=
    match runInc n with
    | .stop s => some (s 0)
    | .revert => none
    | _ => none
  let getTx (n : Nat) : Option Nat :=
    match Tx.run Counter.get ctx { self := { count := n } } with
    | .ok (v, _) => some v
    | .error _ => none
  let getEvm (n : Nat) : Option Nat :=
    match runGet n with
    | .ret w _ => some w
    | _ => none
  IO.println s!"Tx vs EVM increment 5: {incTx 5} vs {incEvm 5}"
  IO.println s!"Tx vs EVM increment max: {incTx (wordBound - 1)} vs {incEvm (wordBound - 1)}"
  IO.println s!"Tx vs EVM get 42: {getTx 42} vs {getEvm 42}"
  match Counter.deploy with
  | .error e => IO.println s!"deploy compile error: {e}"
  | .ok create =>
    match Counter.bytecode with
    | .error e => IO.println s!"runtime compile error: {e}"
    | .ok runtime =>
      match deploy create with
      | none => IO.println "deploy: did not RETURN runtime"
      | some installed => do
        IO.println s!"deploy: {create.length} bytes → {installed.length} (match runtime: {decide (installed == runtime)})"
        match exec installed (packCall incSel) (slot0 5) with
        | .stop s => IO.println s!"increment on deployed runtime: storage[0] = {s 0}"
        | o => IO.println s!"increment on deployed: {formatOutcome o}"
        match execState runtime (packCall incSel) (slot0 5) with
        | some (Halt.stop, s) =>
          match s.logs with
          | l :: _ => IO.println s!"increment logs: {s.logs.length}, topic0 = {l.topics.head?}"
          | [] => IO.println "increment: no logs"
        | _ => IO.println "increment: unexpected halt"

end CounterEndToEnd
