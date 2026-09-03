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
  /-- Dispatcher selectors: always `PUSH4`, so jump layout does not depend on the value. -/
  | push4 (n : Word)
  /-- 32-byte immediates (`PUSH32`): revert selectors, event topics. -/
  | push32 (n : Word)
  | pushLabel (lbl : String)
  | jump (lbl : String)
  | jumpi (lbl : String)
  | jumpDest (lbl : String)
  deriving Repr

end Lsc3.Compile
