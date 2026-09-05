import Lsc.Lang.Contract

/-!
# ABI JSON

Renders a `ContractDef` as a Solidity-compatible JSON ABI (functions, events, errors), for
deployment tooling and differential harnesses. Pure string assembly, no proofs.
-/

namespace Lsc.Tools

open Lsc

private def quote (s : String) : String := "\"" ++ s ++ "\""

private def paramJson (p : Param) : String :=
  "{\"name\":" ++ quote p.name ++ ",\"type\":" ++ quote p.ty.render ++ "}"

private def eventParamJson (p : Param) : String :=
  "{\"name\":" ++ quote p.name ++ ",\"type\":" ++ quote p.ty.render ++ ",\"indexed\":false}"

private def stateMutability : FnKind → String
  | .view => "view"
  | .tx => "nonpayable"
  | .constructor => "nonpayable"

private def outputsJson (ret : RetTy) : String :=
  String.intercalate "," (ret.abi.map fun t => "{\"name\":\"\",\"type\":" ++ quote t.render ++ "}")

private def fnAbiEntry (fn : FnDef) : String :=
  "{\"type\":\"function\",\"name\":" ++ quote fn.name ++
    ",\"inputs\":[" ++ String.intercalate "," (fn.params.map paramJson) ++ "]" ++
    ",\"outputs\":[" ++ outputsJson fn.ret ++ "]" ++
    ",\"stateMutability\":" ++ quote (stateMutability fn.kind) ++ "}"

private def ctorAbiEntry (fn : FnDef) : String :=
  "{\"type\":\"constructor\",\"inputs\":[" ++ String.intercalate "," (fn.params.map paramJson) ++
    "],\"stateMutability\":\"nonpayable\"}"

private def eventAbiEntry (e : EventDef) : String :=
  "{\"type\":\"event\",\"name\":" ++ quote e.name ++ ",\"inputs\":[" ++
    String.intercalate "," (e.params.map eventParamJson) ++ "],\"anonymous\":false}"

private def errorAbiEntry (e : ErrorDef) : String :=
  "{\"type\":\"error\",\"name\":" ++ quote e.name ++ ",\"inputs\":[" ++
    String.intercalate "," (e.params.map paramJson) ++ "]}"

/-- JSON ABI array for a contract. -/
def contractAbiJson (c : ContractDef) : String :=
  let entries := (c.ctor.toList.map ctorAbiEntry) ++ c.functions.map fnAbiEntry ++
    c.events.map eventAbiEntry ++ c.errors.map errorAbiEntry
  "[" ++ String.intercalate ",\n" entries ++ "\n]"

end Lsc.Tools
