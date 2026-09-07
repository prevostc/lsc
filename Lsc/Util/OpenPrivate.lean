/-
Minimal `open private` (modelled on Batteries.Tactic.OpenPrivate), with no
Batteries import. `open_private foo from Mod` finds `_private.Mod.0.…foo`
and opens the short name in the current scope.
-/
import Lean.Elab.Command

open Lean Elab Command

namespace Lsc.Util

/-- Private decls of `mod` whose user-facing name ends with `user`. -/
def findPrivateFrom (env : Environment) (user mod : Name) : List Name :=
  let pfx := Name.mkNum (privateHeader ++ mod) 0
  let cand := mkPrivateNameCore mod user
  if env.contains cand then [cand]
  else
    env.constants.fold (fun acc n _ =>
      if isPrivateName n && pfx.isPrefixOf n && user.isSuffixOf n then
        n :: acc
      else acc) []

end Lsc.Util

syntax (name := openPrivateCmd) "open_private " ident " from " ident : command

@[command_elab openPrivateCmd]
def elabOpenPrivateCmd : CommandElab
  | `(open_private $id from $mod) => do
    match Lsc.Util.findPrivateFrom (← getEnv) id.getId mod.getId with
    | [] =>
      throwError "private declaration '{id.getId}' not found in {mod.getId}"
    | [priv] =>
      modifyScope fun scope =>
        { scope with openDecls := .explicit id.getId priv :: scope.openDecls }
    | found =>
      throwError "ambiguous private name '{id.getId}': {found}"
  | _ => throwUnsupportedSyntax
