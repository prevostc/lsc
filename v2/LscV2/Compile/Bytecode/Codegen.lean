import LscV2.Compile.IR
import LscV2.Compile.Bytecode.Instr
import EvmYul.Operations

namespace LscV2.Compile.Bytecode

open LscV2.Compile.IR
open EvmYul Operation
open Instr

structure Ctx where
  locals : List (Ident × Nat) := []
  stackDepth : Nat := 0
  labelCounter : Nat := 0
  deriving Repr

namespace Ctx

def freshLabel (ctx : Ctx) (tag : String) : String × Ctx :=
  let lbl := tag ++ toString ctx.labelCounter
  (lbl, { ctx with labelCounter := ctx.labelCounter + 1 })

def bindLocal (ctx : Ctx) (name : Ident) : Ctx :=
  let shifted := ctx.locals.map fun (n, d) => (n, d + 1)
  { ctx with locals := (name, 1) :: shifted, stackDepth := ctx.stackDepth + 1 }

def lookupDepth (ctx : Ctx) (name : Ident) : Except String Nat :=
  match ctx.locals.find? (·.1 == name) with
  | some (_, d) => .ok d
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
  | .local name => do
    let d ← ctx.lookupDepth name
    let op ← Ctx.dupOp d
    .ok (emitOp op, { ctx with stackDepth := ctx.stackDepth + 1 })
  | .sload slot =>
    .ok ([.push slot, .op SLOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .add a b => do
    let (i1, c1) ← codegenExpr ctx a
    let (i2, c2) ← codegenExpr c1 b
    .ok (i1 ++ i2 ++ emitOp ADD, { c2 with stackDepth := c2.stackDepth - 1 })
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
    .ok (instrs ++ [.push slot, .op SSTORE], c1.popStack 2)
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
  | .log1 topic data => do
    let (instrs, c1) ← codegenExpr ctx data
    let logInstrs : List Instr := [
      .push 0,
      .op MSTORE,
      .push 0,
      .push 32,
      .push topic,
      .op LOG1
    ]
    .ok (instrs ++ logInstrs, c1.popStack 2)
  | .revert0 =>
    .ok ([.push 0, .push 0, .op REVERT], ctx.popStack ctx.stackDepth)

def stmt (s : IR.Stmt) : Except String (List Instr) :=
  codegenStmt {} s |>.map Prod.fst

end Codegen
end LscV2.Compile.Bytecode
