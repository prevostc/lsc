import Lsc.Compile.IR
import Lsc.Compile.Bytecode.Instr
import Lsc.Compile.Bytecode.Encode
import EvmYul.Operations
import EvmYul.EVM.Instr

namespace Lsc.Compile.Bytecode

open Lsc.Compile.IR
open EvmYul Operation EvmYul.EVM
open Instr

/-! Bytecode spec helpers — encode plain-English codegen properties without hex substring tests. -/

inductive StackSource where
  | local : Ident → StackSource
  | sload : Nat → StackSource
  | unknown : StackSource
  deriving DecidableEq, Repr, Inhabited

namespace StackSource

def matchesAddr (src : StackSource) (addr : IR.Expr) : Bool :=
  match src, addr with
  | .local n, .local m => n == m
  | .sload slot, .sload s => slot == s
  | _, _ => false

end StackSource

/-- Resolve a `letBind` chain for high-level callee checks (e.g. `token` → `sload 2`). -/
partial def resolveCallAddr (stmt : IR.Stmt) (addr : IR.Expr) : List IR.Expr :=
  match addr with
  | .local name =>
    match letBindValue? stmt name with
    | some e => resolveCallAddr stmt e
    | none => [addr]
  | e => [e]
where
  letBindValue? : IR.Stmt → Ident → Option IR.Expr
    | .letBind n e, name => if n == name then some e else none
    | .seq s1 s2, name => letBindValue? s1 name <|> letBindValue? s2 name
    | _, _ => none

private def dupDepth? (o : Operation .EVM) : Option Nat :=
  match o with
  | .Dup (.DUP1) => some 1
  | .Dup (.DUP2) => some 2
  | .Dup (.DUP3) => some 3
  | .Dup (.DUP4) => some 4
  | .Dup (.DUP5) => some 5
  | .Dup (.DUP6) => some 6
  | .Dup (.DUP7) => some 7
  | .Dup (.DUP8) => some 8
  | .Dup (.DUP9) => some 9
  | .Dup (.DUP10) => some 10
  | .Dup (.DUP11) => some 11
  | .Dup (.DUP12) => some 12
  | .Dup (.DUP13) => some 13
  | .Dup (.DUP14) => some 14
  | .Dup (.DUP15) => some 15
  | .Dup (.DUP16) => some 16
  | _ => none

/-- **Property:** after `GAS`, bytecode loads the CALL callee with `DUPn` (used to catch stack-depth bugs). -/
def gasDupDepthBeforeCall (instrs : List Instr) : Option Nat :=
  let rec go (seenGas : Bool) (rest : List Instr) : Option Nat :=
    match rest with
    | [] => none
    | .op o :: tail =>
      if o == CALL then none
      else if o == GAS then go true tail
      else match seenGas, dupDepth? o with
        | true, some d => some d
        | _, _ => go seenGas tail
    | _ :: tail => go seenGas tail
  go false instrs

/-- **Property:** after `GAS`, before `CALL`, bytecode reloads storage slot `slot` via `PUSH slot; SLOAD`. -/
def gasSloadSlotBeforeCall (instrs : List Instr) (slot : Nat) : Bool :=
  let rec go (seenGas : Bool) (rest : List Instr) : Bool :=
    match rest with
    | [] => false
    | .op o :: tail =>
      if o == CALL then false
      else if o == GAS then go true tail
      else go seenGas tail
    | .push n :: .op o :: tail =>
      if seenGas && o == SLOAD && n == slot then true
      else go seenGas (.op o :: tail)
    | _ :: tail => go seenGas tail
  go false instrs

/-- **Property:** after `GAS`, the CALL callee is loaded via `DUPn` or a fresh `SLOAD` of `slot`. -/
def gasLoadsCalleeBeforeCall (instrs : List Instr) (slot : Nat) : Bool :=
  gasDupDepthBeforeCall instrs != none || gasSloadSlotBeforeCall instrs slot

private def dupStack (n : Nat) (stack : List StackSource) : Option (List StackSource) :=
  if n ≤ stack.length then
    let src := stack[stack.length - n]!
    some (stack ++ [src])
  else none

private def callAddrSource (stack : List StackSource) : Option StackSource :=
  if stack.length >= 6 then some stack[stack.length - 6]! else none

private partial def simulateGo (stack : List StackSource) (addr : IR.Expr) (rest : List Instr) : Bool :=
  match rest with
  | [] => false
  | i :: tail =>
    match i with
    | .op o =>
      if o == CALL then
        match callAddrSource stack with
        | some addrSrc => StackSource.matchesAddr addrSrc addr
        | none => false
      else if o == DUP1 then
        match dupStack 1 stack with | some s => simulateGo s addr tail | none => false
      else if o == DUP2 then
        match dupStack 2 stack with | some s => simulateGo s addr tail | none => false
      else if o == DUP3 then
        match dupStack 3 stack with | some s => simulateGo s addr tail | none => false
      else if o == DUP4 then
        match dupStack 4 stack with | some s => simulateGo s addr tail | none => false
      else if o == MSTORE then
        match stack with
        | _ :: _ :: rest => simulateGo rest addr tail
        | _ => false
      else if o == SHL then
        match stack with
        | _ :: _ :: rest => simulateGo (rest ++ [.unknown]) addr tail
        | _ => false
      else if o == GAS then
        simulateGo (stack ++ [.unknown]) addr tail
      else
        simulateGo stack addr tail
    | .push slot =>
      match tail with
      | .op o :: tail' =>
        if o == SLOAD then simulateGo (stack ++ [.sload slot]) addr tail'
        else simulateGo (stack ++ [.unknown]) addr (.op o :: tail')
      | _ => simulateGo (stack ++ [.unknown]) addr tail
    | _ => simulateGo stack addr tail

/-- **Property:** the first `CALL` in `instrs` uses a stack value derived from IR `addr`. -/
def codegenCallUsesAddr (instrs : List Instr) (addr : IR.Expr) : Bool :=
  simulateGo [] addr instrs

/-- **Property:** the first `CALL` uses a stack value derived from `addr`, resolving `letBind` locals. -/
def codegenCallUsesAddrInStmt (stmt : IR.Stmt) (instrs : List Instr) (addr : IR.Expr) : Bool :=
  (resolveCallAddr stmt addr).any (codegenCallUsesAddr instrs ·)

private def instrUsesOp (instrs : List Instr) (target : Operation .EVM) : Bool :=
  instrs.any fun i => match i with | .op o => o == target | _ => false

/-- **Property:** bytecode uses opcode `target`. -/
def usesOp (instrs : List Instr) (target : Operation .EVM) : Bool :=
  instrUsesOp instrs target

private def hasPushPushOpTriple (instrs : List Instr) (val offset : Nat) (target : Operation .EVM) : Bool :=
  let rec go (rest : List Instr) : Bool :=
    match rest with
    | [] => false
    | .push v :: .push o :: instr :: tail =>
      match instr with
      | .op opcode => (v == val && o == offset && opcode == target) || go tail
      | _ => go tail
    | _ :: tail => go tail
  go instrs

/-- **Property:** bytecode stores `val` at memory offset `offset` via `MSTORE`. -/
def mstoresAt (instrs : List Instr) (offset val : Nat) : Bool :=
  hasPushPushOpTriple instrs val offset MSTORE

private def hasPushOpPair (instrs : List Instr) (slot : Nat) (target : Operation .EVM) : Bool :=
  let rec go (rest : List Instr) : Bool :=
    match rest with
    | [] => false
    | .push n :: .op o :: tail => (n == slot && o == target) || go tail
    | _ :: tail => go tail
  go instrs

/-- **Property:** bytecode includes calldata size/selector dispatch machinery. -/
def hasSelectorDispatch (instrs : List Instr) : Bool :=
  instrUsesOp instrs CALLDATASIZE && instrUsesOp instrs CALLDATALOAD && instrUsesOp instrs JUMPI

/-- **Property:** all jump destination labels are unique. -/
def jumpDestsUnique (instrs : List Instr) : Bool :=
  let labels := jumpDestLabelList instrs
  labels.all fun lbl => labels.count lbl == 1

/-- **Property:** bytecode reads a storage slot (push slot + SLOAD). -/
def readsStorageSlot (instrs : List Instr) (slot : Nat) : Bool :=
  hasPushOpPair instrs slot SLOAD

/-- **Property:** bytecode writes a storage slot (push slot + SSTORE). -/
def writesStorageSlot (instrs : List Instr) (slot : Nat) : Bool :=
  hasPushOpPair instrs slot SSTORE

/-- **Property:** constructor/entry loads a calldata word at byte offset `offset`. -/
def loadsCalldataWord (instrs : List Instr) (offset : Nat) : Bool :=
  hasPushOpPair instrs offset CALLDATALOAD

/-- **Property:** bytecode contains a RETURN opcode (view functions). -/
def containsReturn (instrs : List Instr) : Bool :=
  instrUsesOp instrs RETURN

end Lsc.Compile.Bytecode
