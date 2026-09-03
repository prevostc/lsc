import Lsc3.EVM.State

/-!
# LSC v3 — structured EVM assembly before label resolution
-/

namespace Lsc3.Compile

open Lsc3.EVM

/-- Structured assembly instruction (not to be confused with `Lsc3.EVM.Instr`). -/
inductive Asm where
  | op (op : Opcode)
  | push (n : Word)
  | pushLabel (lbl : String)
  | jump (lbl : String)
  | jumpi (lbl : String)
  | jumpDest (lbl : String)
  deriving Repr

end Lsc3.Compile
