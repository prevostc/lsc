import Lsc3.EVM.State
import KeccakEngine.Sponge

/-!
# LSC v3 — the EVM subset machine: `step` and `run`

Executable small-step semantics for the opcode subset in `Lsc3.EVM.State`. Words are
`Nat` below `2^256`; checked arithmetic in the surface language maps to EVM wrapping
semantics here.
-/

namespace Lsc3.EVM

open Lsc3 (wordBound)

/-! ## Word helpers -/

def wrap (n : Word) : Word := n % wordBound

def addW (a b : Word) : Word := wrap (a + b)
def subW (a b : Word) : Word := wrap (a + wordBound - b)
def mulW (a b : Word) : Word := wrap (a * b)
def divW (a b : Word) : Word := if b = 0 then 0 else a / b
def modW (a b : Word) : Word := if b = 0 then 0 else a % b

def ltW (a b : Word) : Word := if a < b then 1 else 0
def gtW (a b : Word) : Word := if b < a then 1 else 0
def eqW (a b : Word) : Word := if a = b then 1 else 0
def iszeroW (a : Word) : Word := if a = 0 then 1 else 0

def andW (a b : Word) : Word := a &&& b
def orW (a b : Word) : Word := a ||| b
def xorW (a b : Word) : Word := a ^^^ b
def notW (a : Word) : Word := (wordBound - 1) ^^^ a

def shlW (shift amount : Word) : Word :=
  if shift ≥ 256 then 0 else wrap (amount <<< shift)

def shrW (shift amount : Word) : Word :=
  if shift ≥ 256 then 0 else amount >>> shift

def addmodW (a b n : Word) : Word := if n = 0 then 0 else (a + b) % n
def mulmodW (a b n : Word) : Word := if n = 0 then 0 else (a * b) % n

def bytesToNat (bytes : ByteArray) : Word :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-! ## Memory -/

def memGet (m : Mem) (off : Nat) : UInt8 := m off

def memSet (m : Mem) (off : Nat) (b : UInt8) : Mem := fun i => if i = off then b else m i

/-- Read 32 big-endian bytes from memory starting at `off`. Out-of-range bytes are zero. -/
def memLoad (m : Mem) (off : Nat) : Word :=
  wrap ((List.range 32).foldl (fun acc i => acc * 256 + (memGet m (off + i)).toNat) 0)

/-- Write a word to memory at `off` (big-endian, 32 bytes). -/
def memStore (m : Mem) (off : Word) (v : Word) : Mem :=
  let v' := wrap v
  (List.range 32).foldl (fun mem i =>
    let byte := UInt8.ofNat ((v' / (256 ^ (31 - i))) % 256)
    memSet mem (off + i) byte) m

/-- Copy `size` bytes from `src` in `data` to memory at `dest`. -/
def memCopy (m : Mem) (dest src size : Nat) (data : List UInt8) : Mem :=
  (List.range size).foldl (fun mem i =>
    let b := if src + i < data.length then data[src + i]! else (0 : UInt8)
    memSet mem (dest + i) b) m

/-- Read 32 big-endian bytes from calldata at `off`, zero-padded. -/
def calldataLoad (data : List UInt8) (off : Nat) : Word :=
  wrap ((List.range 32).foldl (fun acc i =>
    let byte := if off + i < data.length then (data[off + i]!).toNat else 0
    acc * 256 + byte) 0)

/-! ## Stack -/

def stackPop (s : List Word) : Option (Word × List Word) :=
  match s with
  | [] => none
  | x :: xs => some (x, xs)

/-- Pop two words in Yellow Paper order: `(top, second, rest)`. -/
def pop2 (s : List Word) : Option (Word × Word × List Word) :=
  match s with
  | a :: b :: rest => some (a, b, rest)
  | _ => none

/-- Pop three words: `(top, second, third, rest)`. -/
def pop3 (s : List Word) : Option (Word × Word × Word × List Word) :=
  match s with
  | a :: b :: c :: rest => some (a, b, c, rest)
  | _ => none

/-- Pop `n` words, top-first (index 0 is the former top). -/
def popN (s : List Word) (n : Nat) : Option (List Word × List Word) :=
  if n > s.length then none
  else some (s.take n, s.drop n)

def stackPush (s : List Word) (v : Word) : Option (List Word) :=
  if s.length ≥ 1024 then none else some (v :: s)

def stackDup (s : List Word) (d : Nat) : Option (List Word) :=
  if d ≥ s.length then none else stackPush s (s[d]!)

def stackSwap (s : List Word) (d : Nat) : Option (List Word) :=
  if d + 1 ≥ s.length then none
  else
    let top := s[0]!
    let other := s[d + 1]!
    some (s.set 0 other |>.set (d + 1) top)

def exceptional (e : Exception) (s : State) : StepResult :=
  StepResult.halt (.exceptional e) s

def withPush (s : State) (nextPc : Nat) (st : List Word) (v : Word) : StepResult :=
  match stackPush st v with
  | none => exceptional .stackOverflow s
  | some st' => StepResult.next { s with stack := st', pc := nextPc }

/-! ## Decode -/

def readImm (code : List UInt8) (pc immLen : Nat) : Word :=
  wrap ((List.range immLen).foldl (fun acc i =>
    if pc + 1 + i < code.length then acc * 256 + (code[pc + 1 + i]!).toNat
    else acc) 0)

def decodeAt (code : List UInt8) (pc : Nat) : Option (Instr × Nat) :=
  if h : pc < code.length then
    match Opcode.ofByte code[pc] with
    | none => some ({ op := .INVALID }, pc + 1)
    | some op =>
      let imm := readImm code pc (Opcode.immBytes op)
      let size := 1 + Opcode.immBytes op
      some ({ op, imm }, pc + size)
  else none

def isJumpDest (code : List UInt8) (dest : Nat) : Bool :=
  match decodeAt code dest with
  | some ({ op := .JUMPDEST }, _) => true
  | _ => false

/-! ## `step` -/

def haltRet (data : List UInt8) (s : State) : StepResult :=
  StepResult.halt (.ret data) s

def haltRevert (data : List UInt8) (s : State) : StepResult :=
  StepResult.halt (.revert data) s

def step (env : Env) (s : State) : StepResult :=
  match decodeAt env.code s.pc with
  | none => exceptional .invalidOpcode s
  | some (instr, nextPc) =>
    let op := instr.op
    let imm := instr.imm
    match op with
    | .STOP => StepResult.halt (.stop) s
    | .JUMPDEST => StepResult.next { s with pc := nextPc }
    | .INVALID => exceptional .invalidOpcode s
    | .PUSH _ =>
      withPush s nextPc s.stack imm
    | .POP =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (_, st) => StepResult.next { s with stack := st, pc := nextPc }
    | .DUP k =>
      match stackDup s.stack k.val with
      | none => exceptional .stackUnderflow s
      | some st => StepResult.next { s with stack := st, pc := nextPc }
    | .SWAP k =>
      match stackSwap s.stack k.val with
      | none => exceptional .stackUnderflow s
      | some st => StepResult.next { s with stack := st, pc := nextPc }
    | .ADDRESS => withPush s nextPc s.stack env.address
    | .CALLER => withPush s nextPc s.stack env.caller
    | .CALLVALUE => withPush s nextPc s.stack env.callvalue
    | .TIMESTAMP => withPush s nextPc s.stack env.timestamp
    | .NUMBER => withPush s nextPc s.stack env.number
    | .CALLDATASIZE => withPush s nextPc s.stack env.calldata.length
    | .CODESIZE => withPush s nextPc s.stack env.code.length
    | .ADD =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (addW a b)
    | .SUB =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (subW a b)
    | .MUL =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (mulW a b)
    | .DIV =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (divW a b)
    | .MOD =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (modW a b)
    | .ADDMOD =>
      match pop3 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, n, st) => withPush s nextPc st (addmodW a b n)
    | .MULMOD =>
      match pop3 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, n, st) => withPush s nextPc st (mulmodW a b n)
    | .LT =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (ltW a b)
    | .GT =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (gtW a b)
    | .EQ =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (eqW a b)
    | .ISZERO =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, st) => withPush s nextPc st (iszeroW a)
    | .AND =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (andW a b)
    | .OR =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (orW a b)
    | .XOR =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, b, st) => withPush s nextPc st (xorW a b)
    | .NOT =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (a, st) => withPush s nextPc st (notW a)
    | .SHL =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (shift, value, st) => withPush s nextPc st (shlW shift value)
    | .SHR =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (shift, value, st) => withPush s nextPc st (shrW shift value)
    | .MLOAD =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, st) => withPush s nextPc st (memLoad s.mem off)
    | .MSTORE =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, v, st) => StepResult.next { s with mem := memStore s.mem off v, stack := st, pc := nextPc }
    | .SLOAD =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (key, st) => withPush s nextPc st (s.storage key)
    | .SSTORE =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (key, v, st) =>
        StepResult.next { s with storage := fun k => if k = key then v else s.storage k, stack := st, pc := nextPc }
    | .TLOAD =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (key, st) => withPush s nextPc st (s.tstorage key)
    | .TSTORE =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (key, v, st) =>
        StepResult.next { s with tstorage := fun k => if k = key then v else s.tstorage k, stack := st, pc := nextPc }
    | .CALLDATALOAD =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, st) => withPush s nextPc st (calldataLoad env.calldata off)
    | .CALLDATACOPY =>
      match pop3 s.stack with
      | none => exceptional .stackUnderflow s
      | some (dest, src, size, st) =>
        StepResult.next { s with mem := memCopy s.mem dest src size env.calldata, stack := st, pc := nextPc }
    | .CODECOPY =>
      match pop3 s.stack with
      | none => exceptional .stackUnderflow s
      | some (dest, src, size, st) =>
        StepResult.next { s with mem := memCopy s.mem dest src size env.code, stack := st, pc := nextPc }
    | .KECCAK256 =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, size, st) =>
        let bytes := ByteArray.mk ((List.range size).map fun i => memGet s.mem (off + i)).toArray
        withPush s nextPc st (bytesToNat (KeccakEngine.keccak256 bytes))
    | .JUMP =>
      match stackPop s.stack with
      | none => exceptional .stackUnderflow s
      | some (dest, st) =>
        if isJumpDest env.code dest then
          StepResult.next { s with stack := st, pc := dest }
        else exceptional .badJumpDest s
    | .JUMPI =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (dest, cond, st) =>
        if cond = 0 then StepResult.next { s with stack := st, pc := nextPc }
        else if isJumpDest env.code dest then
          StepResult.next { s with stack := st, pc := dest }
        else exceptional .badJumpDest s
    | .RETURN =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, size, _) =>
        let data := List.range size |>.map fun i => memGet s.mem (off + i)
        haltRet data s
    | .REVERT =>
      match pop2 s.stack with
      | none => exceptional .stackUnderflow s
      | some (off, size, _) =>
        let data := List.range size |>.map fun i => memGet s.mem (off + i)
        haltRevert data s
    | .LOG k =>
      let n := k.val
      match popN s.stack (2 + n) with
      | none => exceptional .stackUnderflow s
      | some (args, st) =>
        let off := args[0]!
        let size := args[1]!
        let topics := args.drop 2
        let data := List.range size |>.map fun i => memGet s.mem (off + i)
        StepResult.next { s with logs := s.logs ++ [{ topics, data }], stack := st, pc := nextPc }
    | .CALL =>
      match popN s.stack 7 with
      | none => exceptional .stackUnderflow s
      | some (args, st) =>
        let addr := args[1]!
        let argsOff := args[3]!
        let argsSize := args[4]!
        let retOff := args[5]!
        let retSize := args[6]!
        let sel := memLoad s.mem argsOff / (2 ^ 224)
        let nArgs := if argsSize < 4 then 0 else (argsSize - 4) / 32
        let callArgs := (List.range nArgs).map fun i =>
          memLoad s.mem (argsOff + 4 + 32 * i)
        match env.ext addr sel callArgs with
        | none => withPush s nextPc st 0
        | some ret =>
          let mem' :=
            match ret.head? with
            | some v => if 32 ≤ retSize then memStore s.mem retOff v else s.mem
            | none => s.mem
          withPush { s with mem := mem' } nextPc st 1

/-! ## `run` -/

def run : Nat → Env → State → RunResult
  | 0, _, _ => none
  | fuel + 1, env, s =>
    match step env s with
    | StepResult.halt h s' => some (h, s')
    | StepResult.next s' => run fuel env s'

@[simp] theorem run_zero (env : Env) (s : State) : run 0 env s = none := rfl

@[simp] theorem wrap_eq_of_lt {n : Nat} (h : n < wordBound) : wrap n = n :=
  Nat.mod_eq_of_lt h

@[simp] theorem addW_comm (a b : Word) : addW a b = addW b a := by
  simp [addW, wrap, Nat.add_comm]

@[simp] theorem addW_zero (a : Word) : addW a 0 = wrap a := by
  simp [addW]

@[simp] theorem mulW_zero (a : Word) : mulW a 0 = 0 := by
  simp [mulW, wrap]

end Lsc3.EVM
