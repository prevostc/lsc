import YulEvmCompiler.Instr
import YulEvmCompiler.Asm
import EvmSemantics.EVM.State
import EvmSemantics.EVM.Precompile

/-!
Byte layout of the compiled runtime prologue (memoryguard no-op, then the
held-lock revert). Used by `runtime_prefix` and `nested_lock_reverts`.
-/

namespace Lsc.Compiler

open YulEvmCompiler
open EvmSemantics
open EvmSemantics.EVM

/-- Combine a `PUSH2` immediate. -/
def ofBytes2 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- `PUSH{w} k; ISZERO; POP; PUSH0; TLOAD; ISZERO; PUSH2` — opcode bytes,
without the two-byte jump target. `w = byteWidth k`. -/
def lockPrefixP1 (k : Nat) : List UInt8 :=
  (Instr.pushMin (UInt256.ofNat k)).bytes ++
    (Instr.op .ISZERO).bytes ++
    (Instr.op .POP).bytes ++
    (Instr.pushMin ⟨0⟩).bytes ++
    (Instr.op .TLOAD).bytes ++
    (Instr.op .ISZERO).bytes ++
    [UInt8.ofNat (0x5f + labelWidth)]

/-- `JUMPI; PUSH0; PUSH0; REVERT; JUMPDEST`. -/
def lockPrefixP2 : List UInt8 :=
  (Instr.op .JUMPI).bytes ++
    (Instr.pushMin ⟨0⟩).bytes ++
    (Instr.pushMin ⟨0⟩).bytes ++
    (Instr.op .REVERT).bytes ++
    (Instr.op .JUMPDEST).bytes

/-- Full labelled-Asm lowering of the prologue, with jump target `dest`. -/
def lockPrefixInstrs (k dest : Nat) : List Instr :=
  [Instr.pushMin (UInt256.ofNat k),
    Instr.op .ISZERO,
    Instr.op .POP,
    Instr.pushMin ⟨0⟩,
    Instr.op .TLOAD,
    Instr.op .ISZERO,
    Instr.push labelWidthFin (UInt256.ofNat dest),
    Instr.op .JUMPI,
    Instr.pushMin ⟨0⟩,
    Instr.pushMin ⟨0⟩,
    Instr.op .REVERT,
    Instr.op .JUMPDEST]

/-- Pre-peephole Asm of `.cond (lit k) []` then `lockCheckStmt`. -/
def lockPrefixAsmRaw (k : Nat) : List Asm :=
  [.push (BitVec.ofNat 256 k), .op .iszero, .jumpi 0, .label 0,
    .push 0, .op .tload, .op .iszero, .jumpi 1,
    .push 0, .push 0, .op .revert, .label 1]

/-- Post-peephole Asm of the same prefix (`jumpi L0; label L0` → `pop`,
dead `label L0` dropped). -/
def lockPrefixAsmOpt (k : Nat) : List Asm :=
  [.push (BitVec.ofNat 256 k), .op .iszero, .pop,
    .push 0, .op .tload, .op .iszero, .jumpi 1,
    .push 0, .push 0, .op .revert, .label 1]

/-- After round 1 of `optimizeAsm`: `jumpi L0; label L0` became `pop; label L0`
(dead `label L0` still kept because `0` is still in the whole-program refs). -/
def lockPrefixAsmMid (k : Nat) : List Asm :=
  [.push (BitVec.ofNat 256 k), .op .iszero, .pop, .label 0,
    .push 0, .op .tload, .op .iszero, .jumpi 1,
    .push 0, .push 0, .op .revert, .label 1]

/-- Instructions of `lockPrefixAsmOpt` before `.label 1`. -/
def lockPrefixAsmOptPre (k : Nat) : List Asm :=
  [.push (BitVec.ofNat 256 k), .op .iszero, .pop,
    .push 0, .op .tload, .op .iszero, .jumpi 1,
    .push 0, .push 0, .op .revert]

/-- Gas sufficient to run the lock prefix through `REVERT`. -/
def lockPrefixGasBound : Nat := 200

/-- Frame hypotheses for a nested CALL/STATICCALL into our runtime.
Weaker than `FrameOK`: the call stack may be non-empty. -/
structure NestedFrame (code : ByteArray) (s : State) : Prop where
  hcode : s.executionEnv.code = code
  codeSmall : code.size < 2 ^ 256
  fork : s.executionEnv.fork = .Osaka
  noPrecompile :
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false
  running : s.halt = .Running

end Lsc.Compiler
