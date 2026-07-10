import Lsc.Compile.IR
import Lsc.Compile.Abi
import Lsc.Compile.Bytecode.Instr
import EvmYul.Operations

namespace Lsc.Compile.Bytecode

open Lsc.Compile.IR
open Lsc.Compile.Abi
open EvmYul Operation
open Instr

/-- Stack slot + optional `letBind` source for reload-at-use (avoids stale `DUP` after control flow). -/
structure LocalBinding where
  absPos : Nat
  src : Option Expr := none
  deriving Repr

structure Ctx where
  locals : List (Ident × LocalBinding) := []
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

def lookupBinding (ctx : Ctx) (name : Ident) : Option LocalBinding :=
  (ctx.locals.find? (·.1 == name)).map (·.2)

-- Record the absolute 1-based stack position (from bottom) at time of binding.
-- codegenExpr has already incremented stackDepth before this is called, so
-- ctx.stackDepth IS the position of the new top-of-stack value.
def bindLocal (ctx : Ctx) (name : Ident) (src : Option Expr := none) : Ctx :=
  { ctx with locals := (name, { absPos := ctx.stackDepth, src }) :: ctx.locals }

-- Compute the DUP argument from the stored absolute position.
-- DUP n accesses the item n slots from the top (1 = top).
def lookupDepth (ctx : Ctx) (name : Ident) : Except String Nat :=
  match ctx.lookupBinding name with
  | some b => .ok (ctx.stackDepth - b.absPos + 1)
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

private def calldataSize (args : List Expr) : Nat :=
  4 + 32 * args.length

/-- `mstore(0, paddedSelector selector)` — leaves stack unchanged. -/
private def packSelector (ctx : Ctx) (selector : Nat) : List Instr × Ctx :=
  ( [.push (paddedSelector selector), .push 0, .op MSTORE]
  , ctx )

/-- Revert when the stack top is zero (`ISZERO` then `JUMPI`). -/
private def emitRevertIfZero (ctx : Ctx) : List Instr × Ctx :=
  let (revLbl, c1) := Ctx.freshLabel ctx "callfail"
  let (contLbl, c2) := Ctx.freshLabel c1 "callok"
  ( [ .op ISZERO
    , .pushLabel revLbl
    , .op JUMPI
    , .pushLabel contLbl
    , .op JUMP
    , .jumpDest revLbl
    , .push 0
    , .push 0
    , .op REVERT
    , .jumpDest contLbl ]
  , c2.popStack 1 )

/-- `mload(0)` — binds the loaded word as `bindName`. -/
private def emitMloadBind (ctx : Ctx) (bindName : Ident) : List Instr × Ctx :=
  let c1 := { ctx with stackDepth := ctx.stackDepth + 1 }
  ( [.push 0, .op MLOAD]
  , c1.bindLocal bindName )

/-- Legacy ERC20 bool guard: revert when `returndatasize() > 0` and `mload(0) == 0`. -/
private def emitBoolReturnCheck (ctx : Ctx) : List Instr × Ctx :=
  let (revLbl, c1) := Ctx.freshLabel ctx "boolfail"
  let (skipLbl, c2) := Ctx.freshLabel c1 "boolskip"
  let (contLbl, c3) := Ctx.freshLabel c2 "boolcont"
  ( [ .op RETURNDATASIZE
    , .op ISZERO
    , .pushLabel skipLbl
    , .op JUMPI
    , .push 0
    , .op MLOAD
    , .op ISZERO
    , .pushLabel revLbl
    , .op JUMPI
    , .pushLabel contLbl
    , .op JUMP
    , .jumpDest revLbl
    , .push 0
    , .push 0
    , .op REVERT
    , .jumpDest skipLbl
    , .pushLabel contLbl
    , .op JUMP
    , .jumpDest contLbl ]
  , c3 )

private partial def codegenExpr (ctx : Ctx) (e : Expr) : Except String (List Instr × Ctx) :=
  match e with
  | .lit n => .ok ([.push n], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .local name =>
    if name == "caller" then
      .ok (emitOp CALLER, { ctx with stackDepth := ctx.stackDepth + 1 })
    else
      match ctx.lookupBinding name with
      | none => .error s!"unknown local {name}"
      | some { src := some (.sload slot), .. } =>
        .ok ([.push slot, .op SLOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
      | some { src := some (.calldataWord offset), .. } =>
        .ok ([.push offset, .op CALLDATALOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
      | some { src := some (.lit n), .. } =>
        .ok ([.push n], { ctx with stackDepth := ctx.stackDepth + 1 })
      | some _ => do
        let d ← ctx.lookupDepth name
        let op ← Ctx.dupOp d
        .ok (emitOp op, { ctx with stackDepth := ctx.stackDepth + 1 })
  | .sload slot =>
    .ok ([.push slot, .op SLOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .calldataWord offset =>
    .ok ([.push offset, .op CALLDATALOAD], { ctx with stackDepth := ctx.stackDepth + 1 })
  | .mapSlot base key => do
    let (keyInstr, c1) ← codegenExpr ctx key
    let hashInstr : List Instr :=
      [.push 0, .op MSTORE, .push base, .push 32, .op MSTORE, .push 64, .push 0, .op KECCAK256]
    .ok (keyInstr ++ hashInstr, { c1 with stackDepth := c1.stackDepth + 1 })
  | .dynSload slotExpr => do
    let (slotInstr, c1) ← codegenExpr ctx slotExpr
    .ok (slotInstr ++ [.op SLOAD], c1)
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

/-- ABI-pack each argument at `4 + 32*i` after the selector word. -/
private partial def packArgs (ctx : Ctx) (args : List Expr) (i : Nat) :
    Except String (List Instr × Ctx) :=
  match args with
  | [] => .ok ([], ctx)
  | arg :: rest => do
    let (argInstr, _) ← codegenExpr ctx arg
    let offset := 4 + 32 * i
    -- `codegenExpr` + `push offset` + `MSTORE` is net stack-neutral; keep `ctx.stackDepth`.
    let (restInstr, c2) ← packArgs ctx rest (i + 1)
    .ok (argInstr ++ [.push offset, .op MSTORE] ++ restInstr, c2)

private def packCalldata (ctx : Ctx) (selector : Nat) (args : List Expr) :
    Except String (List Instr × Ctx) := do
  let (selInstr, c1) := packSelector ctx selector
  let (argInstr, c2) ← packArgs c1 args 0
  .ok (selInstr ++ argInstr, c2)

/-- `CALL(gas(), addr, 0, 0, inSize, 0, outSize)` — leaves success bool on stack. -/
private def emitCall (ctx : Ctx) (addr : Expr) (inSize outSize : Nat) :
    Except String (List Instr × Ctx) := do
  let gasInstr := emitOp GAS
  let c1 := { ctx with stackDepth := ctx.stackDepth + 1 }
  let (addrInstr, c2) ← codegenExpr c1 addr
  let callInstrs : List Instr :=
    [.push 0, .push 0, .push inSize, .push 0, .push outSize, .op CALL]
  .ok (gasInstr ++ addrInstr ++ callInstrs, { c2 with stackDepth := c2.stackDepth - 5 })

/-- `STATICCALL(gas(), addr, 0, inSize, 0, outSize)` — leaves success bool on stack. -/
private def emitStaticCall (ctx : Ctx) (addr : Expr) (inSize outSize : Nat) :
    Except String (List Instr × Ctx) := do
  let gasInstr := emitOp GAS
  let c1 := { ctx with stackDepth := ctx.stackDepth + 1 }
  let (addrInstr, c2) ← codegenExpr c1 addr
  let callInstrs : List Instr :=
    [.push 0, .push inSize, .push 0, .push outSize, .op STATICCALL]
  .ok (gasInstr ++ addrInstr ++ callInstrs, { c2 with stackDepth := c2.stackDepth - 4 })

private def codegenExternalCall (ctx : Ctx) (addr : Expr) (selector : Nat) (args : List Expr)
    (checkBoolReturn : Bool) : Except String (List Instr × Ctx) := do
  let inSize := calldataSize args
  let (packInstr, c1) ← packCalldata ctx selector args
  let (callInstr, c2) ← emitCall c1 addr inSize 32
  let (revInstr, c3) := emitRevertIfZero c2
  let (boolInstr, c4) := if checkBoolReturn then emitBoolReturnCheck c3 else ([], c3)
  .ok (packInstr ++ callInstr ++ revInstr ++ boolInstr, c4)

private def codegenExternalCallBind (ctx : Ctx) (addr : Expr) (selector : Nat)
    (args : List Expr) (bindName : Ident) : Except String (List Instr × Ctx) := do
  let inSize := calldataSize args
  let (packInstr, c1) ← packCalldata ctx selector args
  let (callInstr, c2) ← emitCall c1 addr inSize 32
  let (revInstr, c3) := emitRevertIfZero c2
  let (loadInstr, c4) := emitMloadBind c3 bindName
  .ok (packInstr ++ callInstr ++ revInstr ++ loadInstr, c4)

private def codegenStaticCall (ctx : Ctx) (addr : Expr) (selector : Nat) (args : List Expr)
    (retWords : Nat) : Except String (List Instr × Ctx) := do
  let inSize := calldataSize args
  let outSize := 32 * retWords
  let (packInstr, c1) ← packCalldata ctx selector args
  let (callInstr, c2) ← emitStaticCall c1 addr inSize outSize
  let (revInstr, c3) := emitRevertIfZero c2
  .ok (packInstr ++ callInstr ++ revInstr, c3)

private def codegenStaticCallBind (ctx : Ctx) (addr : Expr) (selector : Nat)
    (args : List Expr) (bindName : Ident) : Except String (List Instr × Ctx) := do
  let inSize := calldataSize args
  let (packInstr, c1) ← packCalldata ctx selector args
  let (callInstr, c2) ← emitStaticCall c1 addr inSize 32
  let (revInstr, c3) := emitRevertIfZero c2
  let (loadInstr, c4) := emitMloadBind c3 bindName
  .ok (packInstr ++ callInstr ++ revInstr ++ loadInstr, c4)

private partial def codegenStmt (ctx : Ctx) (s : Stmt) : Except String (List Instr × Ctx) :=
  match s with
  | .skip => .ok ([], ctx)
  | .seq s1 s2 => do
    let (i1, c1) ← codegenStmt ctx s1
    let (i2, c2) ← codegenStmt c1 s2
    .ok (i1 ++ i2, c2)
  | .letBind name e => do
    let (instrs, c1) ← codegenExpr ctx e
    .ok (instrs, c1.bindLocal name (some e))
  | .sstore slot e => do
    let (instrs, c1) ← codegenExpr ctx e
    -- c1.stackDepth = ctx.stackDepth + 1 (codegenExpr pushed e).
    -- `push slot` adds 1, `SSTORE` pops 2: net from c1 is -1, so net from ctx is 0.
    .ok (instrs ++ [.push slot, .op SSTORE], c1.popStack 1)
  | .sstoreDyn slotExpr e => do
    let (valInstr, c1) ← codegenExpr ctx e
    let (slotInstr, c2) ← codegenExpr c1 slotExpr
    .ok (valInstr ++ slotInstr ++ [.op SSTORE], c2.popStack 2)
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
    let (eInstr, c1) ← codegenExpr ctx e
    let retInstrs : List Instr := [.push 0, .op MSTORE, .push 32, .push 0, .op RETURN]
    .ok (eInstr ++ retInstrs, c1.popStack 1)
  | .checkReentrancyLock =>
    let (revLbl, c1) := Ctx.freshLabel ctx "lockrev"
    let (contLbl, c2) := Ctx.freshLabel c1 "lockcont"
    let lockInstrs : List Instr := [
      .push IR.reentrancyLockSlot,
      .op TLOAD,
      .op ISZERO,
      .op ISZERO,
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
    .ok (lockInstrs, c2)
  | .setReentrancyLock held =>
    let val := if held then 1 else 0
    .ok ([.push val, .push IR.reentrancyLockSlot, .op TSTORE], ctx)
  | .externalCall addr selector args checkBoolReturn =>
    codegenExternalCall ctx addr selector args checkBoolReturn
  | .externalCallBind addr selector args bindName =>
    codegenExternalCallBind ctx addr selector args bindName
  | .staticCall addr selector args retWords =>
    codegenStaticCall ctx addr selector args retWords
  | .staticCallBind addr selector args bindName =>
    codegenStaticCallBind ctx addr selector args bindName

def stmt (ctx : Ctx) (s : IR.Stmt) : Except String (List Instr × Ctx) :=
  codegenStmt ctx s

def stmtFresh (s : IR.Stmt) : Except String (List Instr) :=
  stmt {} s |>.map Prod.fst

end Codegen
end Lsc.Compile.Bytecode
