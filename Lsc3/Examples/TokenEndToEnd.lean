import Lsc3.Examples.Token
import Lsc3.Compile.Exec

/-!
# Token end-to-end: init, mappings, nested allowances on the EVM machine
-/

namespace TokenEndToEnd

open Lsc3 Lsc3.Compile.Exec

def initSel : Nat :=
  selectorOf "init" [{ name := "owner", ty := .address }, { name := "supply", ty := .uint256 }]
def supplySel : Nat := selectorOf "totalSupply" []
def balSel : Nat := selectorOf "balanceOf" [{ name := "who", ty := .address }]
def approveSel : Nat :=
  selectorOf "approve" [{ name := "spender", ty := .address }, { name := "amount", ty := .uint256 }]
def allowanceSel : Nat :=
  selectorOf "allowance" [{ name := "owner", ty := .address }, { name := "spender", ty := .address }]
def transferSel : Nat :=
  selectorOf "transfer" [{ name := "to", ty := .address }, { name := "amount", ty := .uint256 }]
def transferFromSel : Nat :=
  selectorOf "transferFrom"
    [{ name := "src", ty := .address }, { name := "to", ty := .address },
     { name := "amount", ty := .uint256 }]

def formatOutcome : Outcome → String
  | .stop s => s!"stop (slot1/totalSupply={s 1})"
  | .ret w _ => s!"ret {w}"
  | .revert => "revert"
  | .fail e => s!"fail {repr e}"
  | .timeout => "timeout"

#eval! do
  match Token.bytecode with
  | .error e => IO.println s!"compile error: {e}"
  | .ok code => do
    IO.println s!"bytecode ({code.length} bytes)"
    let owner : Nat := 0xaaa
    let spender : Nat := 0xbbb
    let supply : Nat := 1000
    match exec code (packCall initSel [owner, supply]) (fun _ => 0) with
    | .stop s1 => do
      IO.println s!"init ok, totalSupply slot = {s1 1}"
      IO.println s!"totalSupply: {formatOutcome (exec code (packCall supplySel) s1)}"
      IO.println s!"balanceOf(owner): {formatOutcome (exec code (packCall balSel [owner]) s1)}"
      match exec code (packCall approveSel [spender, 40]) s1 owner with
      | .stop s2 => do
        IO.println s!"approve ok"
        IO.println s!"allowance(owner,spender): {formatOutcome (exec code (packCall allowanceSel [owner, spender]) s2)}"
        match exec code (packCall transferSel [spender, 100]) s2 owner with
        | .stop s3 => do
          IO.println s!"transfer 100 to spender"
          IO.println s!"balanceOf(owner): {formatOutcome (exec code (packCall balSel [owner]) s3)}"
          IO.println s!"balanceOf(spender): {formatOutcome (exec code (packCall balSel [spender]) s3)}"
          let other : Nat := 0xccc
          match exec code (packCall transferFromSel [owner, other, 30]) s3 spender with
          | .stop s4 => do
            IO.println s!"transferFrom 30 owner→other as spender"
            IO.println s!"balanceOf(owner): {formatOutcome (exec code (packCall balSel [owner]) s4)}"
            IO.println s!"balanceOf(other): {formatOutcome (exec code (packCall balSel [other]) s4)}"
            IO.println s!"allowance: {formatOutcome (exec code (packCall allowanceSel [owner, spender]) s4)}"
          | o => IO.println s!"transferFrom: {formatOutcome o}"
        | o => IO.println s!"transfer: {formatOutcome o}"
      | o => IO.println s!"approve: {formatOutcome o}"
    | o => IO.println s!"init: {formatOutcome o}"

end TokenEndToEnd
