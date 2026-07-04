import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open EvmYul Operation

/-- Structured EVM assembly before label resolution and byte emission. -/
inductive Instr where
  | op : Operation .EVM → Instr
  | push : Nat → Instr
  | pushLabel : String → Instr
  | jump : String → Instr
  | jumpi : String → Instr
  | jumpDest : String → Instr
  deriving Repr

end Lsc.Compile.Bytecode
