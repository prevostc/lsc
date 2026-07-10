import Lsc.Lang.AST
import Lsc.Selectors

namespace Lsc.Tools

open Lsc

private def fnStateMutability (kind : FunctionKind) : String :=
  match kind with
  | .view => "view"
  | .external => "nonpayable"
  | .internal => "nonpayable"
  | .constructor => "nonpayable"

private def paramJson (name : Ident) (ty : Ty) : String :=
  "{\"name\":\"" ++ name ++ "\",\"type\":\"" ++ ty.abiStr ++ "\"}"

private def fnAbiEntry (fn : FunctionDef) : String :=
  let inputs := String.intercalate "," (fn.params.map fun (n, t) => paramJson n t)
  let outputs :=
    if fn.retTy == .unit then ""
    else ",\"outputs\":[{\"name\":\"\",\"type\":\"" ++ fn.retTy.abiStr ++ "\"}]"
  "{\"type\":\"function\",\"name\":\"" ++ fn.name ++ "\",\"inputs\":[" ++ inputs ++ "]" ++
    outputs ++ ",\"stateMutability\":\"" ++ fnStateMutability fn.kind ++ "\"}"

private def eventParamJson (name : Ident) (ty : Ty) : String :=
  "{\"name\":\"" ++ name ++ "\",\"type\":\"" ++ ty.abiStr ++ "\",\"indexed\":false}"

private def eventAbiEntry (name : Ident) (params : List (Ident × Ty)) : String :=
  let inputs := String.intercalate "," (params.map fun (n, t) => eventParamJson n t)
  "{\"type\":\"event\",\"name\":\"" ++ name ++ "\",\"inputs\":[" ++ inputs ++ "],\"anonymous\":false}"

private def errorAbiEntry (name : Ident) (params : List (Ident × Ty)) : String :=
  let inputs := String.intercalate "," (params.map fun (n, t) => paramJson n t)
  "{\"type\":\"error\",\"name\":\"" ++ name ++ "\",\"inputs\":[" ++ inputs ++ "]}"

/-- JSON ABI array for heimdall `-a` (keccak selectors via [`computeSelector`]). -/
def contractAbiJson (c : ContractDef) : String :=
  let fns := c.functions.filter fun fn =>
    fn.kind == .external || fn.kind == .view
  let fnEntries := fns.map fnAbiEntry
  let eventEntries := c.events.map fun (n, ps) => eventAbiEntry n ps
  let errorEntries := c.errors.map fun (n, ps) => errorAbiEntry n ps
  let all := fnEntries ++ eventEntries ++ errorEntries
  "[" ++ String.intercalate ",\n" all ++ "\n]"

end Lsc.Tools
