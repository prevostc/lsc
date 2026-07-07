import Lsc.Compile.IR
import Lsc.Compile.Bytecode.Instr
import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open Lsc.Compile.IR
open EvmYul Operation
open Instr

structure Ctx where
  locals : List (Ident × Nat) := []
  stackDepth : Nat := 0
  labelCounter : Nat := 0
  labelPrefix : String := ""
  deriving Repr

namespace Ctx

def freshLabel (ctx : Ctx) (tag : String) : String × Ctx :=
  let lbl := ctx.labelPrefix ++ tag ++ toString ctx.labelCounter
  (lbl, { ctx with labelCounter := ctx.labelCounter + 1 })

/-- Reset per-function stack/locals while keeping the global label counter. -/
def forFunction (ctx : Ctx) (fnName : Ident) : Ctx :=
  { locals := [], stackDepth := 0, labelCounter := ctx.labelCounter, labelPrefix := fnName ++ "." }

/-- Drop function-local state after emitting a body; label counter stays global. -/
def afterFunction (ctx : Ctx) : Ctx :=
  { locals := [], stackDepth := 0, labelCounter := ctx.labelCounter, labelPrefix := "" }

-- Record the absolute 1-based stack position (from bottom) at time of binding.
-- codegenExpr has already incremented stackDepth before this is called, so
-- ctx.stackDepth IS the position of the new top-of-stack value.
def bindLocal (ctx : Ctx) (name : Ident) : Ctx :=
  { ctx with locals := (name, ctx.stackDepth) :: ctx.locals }

-- Compute the DUP argument from the stored absolute position.
-- DUP n accesses the item n slots from the top (1 = top).
def lookupDepth (ctx : Ctx) (name : Ident) : Except String Nat :=
  match ctx.locals.find? (·.1 == name) with
  | some (_, absPos) => .ok (ctx.stackDepth - absPos + 1)
  | none => .error s!"unknown local {name}"

def dupOp (depth : Nat) : Except String (Operation .EVM) :=
  match depth with
  | 1 => .ok DUP1
  | 2 => .ok DUP2
  | 3 => .ok DUP3
  | 4 => .ok DUP4
  | 5 => .ok DUP5
  | 6 => .ok DUP6
  | 7 => .ok DUP7
  | 8 => .ok DUP8
  | 9 => .ok DUP9
  | 10 => .ok DUP10
  | 11 => .ok DUP11
  | 12 => .ok DUP12
  | 13 => .ok DUP13
  | 14 => .ok DUP14
  | 15 => .ok DUP15
  | 16 => .ok DUP16
  | _ => .error s!"stack depth {depth} exceeds DUP16"

def popStack (ctx : Ctx) (n : Nat := 1) : Ctx :=
  { ctx with stackDepth := ctx.stackDepth - n }

end Ctx

namespace Codegen

private def emitOp (op : Operation .EVM) : List Instr := [.op op]

private partial def codegenExpr (ctx : Ctx) (e : Expr) : Except String (List Instr × Ctx) :=
  match e with
  | .lit n => .ok ([.push n], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .local name =>
    if name == "caller" then
      .ok (emitOp CALLER, { ctx with stackDepth := ctx.stackDepth + 1 })
    else do
      let d ← ctx.lookupDepth name
      let op ← Ctx.dupOp d
      .ok (emitOp op, { ctx with stackDepth := ctx.stackDepth + 1 })
  | .sload slot =>
    .ok ([.push slot, .op SLOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .add a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp ADD, { c2 with stackDepth := c2.stackDepth - 1 })
  | .sub a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp SUB, { c2 with stackDepth := c2.stackDepth - 1 })
  | .mul a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp MUL, { c2 with stackDepth := c2.stackDepth - 1 })
  | .div a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp DIV, { c2 with stackDepth := c2.stackDepth - 1 })
  | .lt a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp LT, { c2 with stackDepth := c2.stackDepth - 1 })
  | .eq a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp EQ, { c2 with stackDepth := c2.stackDepth - 1 })
  | .isZero a => do
    let (i1, c1) ← codegenExpr ctx a
    .ok (i1 ++ emitOp ISZERO, c1)

private partial def codegenStmt (ctx : Ctx) (s : Stmt) : Except String (List Instr × Ctx) :=
  match s with
  | .skip => .ok ([], ctx)
  | .seq s1 s2 => do
    let (i1, c1) ← codegenStmt ctx s1
    let (i2, c2) ← codegenStmt c1 s2
    .ok (i1 ++ i2, c2)
  | .letBind name e => do
    let (instrs, c1) ← codegenExpr ctx e
    .ok (instrs, c1.bindLocal name)
  | .sstore slot e => do
    let (instrs, c1) ← codegenExpr ctx e
    -- c1.stackDepth = ctx.stackDepth + 1 (codegenExpr pushed e).
    -- `push slot` adds 1, `SSTORE` pops 2: net from c1 is -1, so net from ctx is 0.
    .ok (instrs ++ [.push slot, .op SSTORE], c1.popStack 1)
  | .ifRevert cond => do
    let (revLbl, c1) := Ctx.freshLabel ctx "rev"
    let (contLbl, c2) := Ctx.freshLabel c1 "cont"
    let (cInstr, c3) ← codegenExpr c2 cond
    let jumpInstrs : List Instr := [
      .pushLabel revLbl,
      .op JUMPI,
      .pushLabel contLbl,
      .op JUMP,
      .jumpDest revLbl,
      .push 0,
      .push 0,
      .op REVERT,
      .jumpDest contLbl
    ]
    .ok (cInstr ++ jumpInstrs, c3.popStack 1)
  | .log0 topic =>
    let popsAfter := List.replicate ctx.locals.length (.op POP)
    let logInstrs : List Instr := [
      .push 0,
      .push 0,
      .push topic,
      .op LOG1
    ]
    .ok (popsAfter ++ logInstrs, { locals := [], stackDepth := 0 })
  | .log1 topic data => do
    let (dataInstr, c1) ← codegenExpr ctx data
    let memStore : List Instr := [.push 0, .op MSTORE]
    let popsAfter := List.replicate c1.locals.length (.op POP)
    let logInstrs : List Instr := [
      .push 0,
      .push 32,
      .push topic,
      .op LOG1
    ]
    .ok (dataInstr ++ memStore ++ popsAfter ++ logInstrs, { locals := [], stackDepth := 0 })
  | .revert0 =>
    .ok ([.push 0, .push 0, .op REVERT], ctx.popStack ctx.stackDepth)
  | .ret e => do
    -- Every supported `Ty` is a single 32-byte word (`IR.lean`'s `.ret` docstring) — write it
    -- to memory offset 0 and `RETURN` exactly those 32 bytes, the minimal-viable ABI encoding
    -- for a scalar return value (matches Solidity's own codegen for a single-word return type).
    let (eInstr, c1) ← codegenExpr ctx e
    let retInstrs : List Instr := [.push 0, .op MSTORE, .push 32, .push 0, .op RETURN]
    .ok (eInstr ++ retInstrs, c1.popStack 1)
  | .safeExternalCall .. =>
    -- Not yet supported by this raw stack-machine backend (`CALL`'s 7 stack arguments need
    -- careful DUP-free ordering this backend's simple `codegenExpr`-per-operand shape doesn't
    -- give for free) — the Yul backend (`Lsc.Compile.Yul.irToYulContract`/`safeExternalCallToYul`)
    -- is the one real, tested lowering for this node today; rejecting cleanly here rather than
    -- emitting wrong bytecode is the deliberate choice (mirrors this file's existing
    -- `Lower.lean`'s "reject cleanly, don't silently miscompile" precedent).
    .error "IR.Stmt.safeExternalCall is not yet supported by the raw bytecode codegen backend \
      — use the Yul backend (Lsc.Compile.Yul) instead"

def stmt (ctx : Ctx) (s : IR.Stmt) : Except String (List Instr × Ctx) :=
  codegenStmt ctx s

def stmtFresh (s : IR.Stmt) : Except String (List Instr) :=
  stmt {} s |>.map Prod.fst

end Codegen
end Lsc.Compile.Bytecode
