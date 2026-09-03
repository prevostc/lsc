import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open EvmYul Operation

/-- Structured EVM assembly before label resolution and byte emission. -/
inductive Instr where
  | op : Operation .EVM → Instr
  | push : Nat → Instr
  /-- A value encoded with an explicit PUSH32 immediate. Label resolution uses this constructor
  so resolved instruction widths remain identical to production symbolic-label emission. -/
  | push32 : Nat → Instr
  | pushLabel : String → Instr
  | jump : String → Instr
  | jumpi : String → Instr
  | jumpDest : String → Instr
  deriving Repr

end Lsc.Compile.Bytecode
