import Lsc.Compile.Bytecode.Instr
import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open EvmYul Operation
open Instr

private def renderOp (o : Operation .EVM) : String :=
  toString (repr o)

def renderInstr (i : Instr) : String :=
  match i with
  | .op o => renderOp o
  | .push n => s!"PUSH {n}"
  | .pushLabel lbl => s!"PUSH @{lbl}"
  | .jump lbl => s!"JUMP @{lbl}"
  | .jumpi lbl => s!"JUMPI @{lbl}"
  | .jumpDest lbl => s!"@:{lbl}"

/-- Human-readable LSC codegen output (one instruction per line, 0-based index). -/
def renderInstrs (instrs : List Instr) : String :=
  let lines := instrs.mapIdx fun i instr =>
    let idx := toString i
    let pad := String.ofList (List.replicate (Nat.max idx.length 4 - idx.length) ' ')
    s!"{pad}{idx}  {renderInstr instr}"
  String.intercalate "\n" lines

end Lsc.Compile.Bytecode
