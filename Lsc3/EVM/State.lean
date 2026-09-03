import Lsc3.Tx

/-!
# LSC v3 — the EVM subset machine: data

`Lsc3.EVM` is a small-step machine for exactly the opcodes the LSC compiler emits. It is the
model against which per-contract bytecode certificates (`f.bytecode_ok`) are proved, so it
is kept tiny, executable and first-order:

* words are `Nat`s below `2^256` (`wordBound`), so `omega`/`simp` proofs stay in `Nat`;
* memory is byte-addressed (`Nat → UInt8`), storage and transient storage are `Nat → Nat`;
* there is no gas: termination is by fuel in `run`, and gas bounds are a separate, later
  theorem against EvmYul's accounting;
* no calls, no `CREATE`, no precompiles in Phase B (calls arrive as oracle steps in Phase D).

The machine is kept honest two ways (Phase B): per-opcode refinement theorems against
EvmYulLean's `EVM.step` under a state projection (`Lsc3/EVM/EvmYulRefinement.lean`), and
executable differential tests. This file is data only; `step`/`run` live in `Lsc3/EVM/Step.lean`.
-/

namespace Lsc3.EVM

/-- An EVM word. Invariant maintained by the machine: `< wordBound`. -/
abbrev Word : Type := Nat

/-- Byte-addressed memory, zero-initialised. -/
abbrev Mem : Type := Nat → UInt8

/-- Persistent or transient storage, zero-initialised. -/
abbrev Storage : Type := Nat → Word

/-! ## Opcodes

Exactly the subset the compiler emits (plus the handful needed by tests). `PUSH k` carries the
immediate width `k ∈ [0, 32]`; `DUP k`/`SWAP k` mean `DUPk+1`/`SWAPk+1`; `LOG k` is `LOGk`. -/
inductive Opcode
  | STOP | ADD | MUL | SUB | DIV | MOD | ADDMOD | MULMOD
  | LT | GT | EQ | ISZERO | AND | OR | XOR | NOT | SHL | SHR
  | KECCAK256
  | ADDRESS | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY | CODESIZE | CODECOPY
  | TIMESTAMP | NUMBER
  | POP | MLOAD | MSTORE | SLOAD | SSTORE | JUMP | JUMPI | JUMPDEST | TLOAD | TSTORE
  | PUSH (k : Fin 33)
  | DUP (k : Fin 16)
  | SWAP (k : Fin 16)
  | LOG (k : Fin 5)
  | RETURN | REVERT | INVALID
  deriving DecidableEq, Repr

namespace Opcode

/-- The byte of an opcode (Yellow Paper appendix H). -/
def toByte : Opcode → UInt8
  | STOP => 0x00 | ADD => 0x01 | MUL => 0x02 | SUB => 0x03 | DIV => 0x04 | MOD => 0x06
  | ADDMOD => 0x08 | MULMOD => 0x09
  | LT => 0x10 | GT => 0x11 | EQ => 0x14 | ISZERO => 0x15 | AND => 0x16 | OR => 0x17
  | XOR => 0x18 | NOT => 0x19 | SHL => 0x1b | SHR => 0x1c
  | KECCAK256 => 0x20
  | ADDRESS => 0x30 | CALLER => 0x33 | CALLVALUE => 0x34 | CALLDATALOAD => 0x35
  | CALLDATASIZE => 0x36 | CALLDATACOPY => 0x37 | CODESIZE => 0x38 | CODECOPY => 0x39
  | TIMESTAMP => 0x42 | NUMBER => 0x43
  | POP => 0x50 | MLOAD => 0x51 | MSTORE => 0x52 | SLOAD => 0x54 | SSTORE => 0x55
  | JUMP => 0x56 | JUMPI => 0x57 | JUMPDEST => 0x5b | TLOAD => 0x5c | TSTORE => 0x5d
  | PUSH k => UInt8.ofNat (0x5f + k.val)
  | DUP k => UInt8.ofNat (0x80 + k.val)
  | SWAP k => UInt8.ofNat (0x90 + k.val)
  | LOG k => UInt8.ofNat (0xa0 + k.val)
  | RETURN => 0xf3 | REVERT => 0xfd | INVALID => 0xfe

/-- Decode one opcode byte. Bytes outside the subset decode to `none` and execute as
`INVALID` (an exceptional halt), which is also what the real EVM does for undefined bytes;
for defined-but-unsupported opcodes this is where the subset machine is deliberately partial. -/
def ofByte (b : UInt8) : Option Opcode :=
  let n := b.toNat
  if h : 0x5f ≤ n ∧ n ≤ 0x7f then some (PUSH ⟨n - 0x5f, by omega⟩)
  else if h : 0x80 ≤ n ∧ n ≤ 0x8f then some (DUP ⟨n - 0x80, by omega⟩)
  else if h : 0x90 ≤ n ∧ n ≤ 0x9f then some (SWAP ⟨n - 0x90, by omega⟩)
  else if h : 0xa0 ≤ n ∧ n ≤ 0xa4 then some (LOG ⟨n - 0xa0, by omega⟩)
  else match b with
  | 0x00 => some STOP | 0x01 => some ADD | 0x02 => some MUL | 0x03 => some SUB
  | 0x04 => some DIV | 0x06 => some MOD | 0x08 => some ADDMOD | 0x09 => some MULMOD
  | 0x10 => some LT | 0x11 => some GT | 0x14 => some EQ | 0x15 => some ISZERO
  | 0x16 => some AND | 0x17 => some OR | 0x18 => some XOR | 0x19 => some NOT
  | 0x1b => some SHL | 0x1c => some SHR
  | 0x20 => some KECCAK256
  | 0x30 => some ADDRESS | 0x33 => some CALLER | 0x34 => some CALLVALUE
  | 0x35 => some CALLDATALOAD | 0x36 => some CALLDATASIZE | 0x37 => some CALLDATACOPY
  | 0x38 => some CODESIZE | 0x39 => some CODECOPY
  | 0x42 => some TIMESTAMP | 0x43 => some NUMBER
  | 0x50 => some POP | 0x51 => some MLOAD | 0x52 => some MSTORE | 0x54 => some SLOAD
  | 0x55 => some SSTORE | 0x56 => some JUMP | 0x57 => some JUMPI | 0x5b => some JUMPDEST
  | 0x5c => some TLOAD | 0x5d => some TSTORE
  | 0xf3 => some RETURN | 0xfd => some REVERT | 0xfe => some INVALID
  | _ => none

/-- Number of immediate bytes following the opcode (non-zero only for `PUSH`). -/
def immBytes : Opcode → Nat
  | PUSH k => k.val
  | _ => 0

end Opcode

/-- A decoded instruction: the opcode and its immediate (`0` when there is none). -/
structure Instr where
  op : Opcode
  imm : Word := 0
  deriving DecidableEq, Repr

/-- One `LOGn` record: `n` topics and the data bytes. -/
structure Log where
  topics : List Word
  data : List UInt8
  deriving DecidableEq, Repr

/-- The immutable part of an execution: the code being run and the call's environment. -/
structure Env where
  code : List UInt8
  calldata : List UInt8
  address : Word
  caller : Word
  callvalue : Word
  timestamp : Word
  number : Word
  deriving Repr

/-- The mutable machine state. -/
structure State where
  pc : Nat := 0
  stack : List Word := []
  mem : Mem := fun _ => 0
  storage : Storage
  tstorage : Storage := fun _ => 0
  logs : List Log := []

/-- Why an execution halted exceptionally. All of these revert every state change and return
no data (the EVM consumes all gas; we have no gas). -/
inductive Exception
  | invalidOpcode
  | stackUnderflow
  | stackOverflow
  | badJumpDest
  deriving DecidableEq, Repr

/-- How an execution ended. -/
inductive Halt
  | stop
  | ret (data : List UInt8)
  | revert (data : List UInt8)
  | exceptional (e : Exception)
  deriving DecidableEq, Repr

/-- The result of one `step`. -/
inductive StepResult
  | next (s : State)
  | halt (h : Halt) (s : State)

/-- The result of `run`: `none` when fuel ran out. -/
abbrev RunResult : Type := Option (Halt × State)

/-- Success means state changes and logs persist: `STOP` or `RETURN`. -/
def Halt.isSuccess : Halt → Bool
  | .stop | .ret _ => true
  | .revert _ | .exceptional _ => false

end Lsc3.EVM
