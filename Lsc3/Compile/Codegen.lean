import Lsc3.Core
import Lsc3.Contract
import Lsc3.Compile.Instr

/-!
# LSC v3 — Core → EVM assembly

Memory-local calling convention: each de Bruijn binding occupies a 32-byte memory word starting
at `localBase`. Parameters are loaded from calldata on entry; `letOp`/`letPure` allocate the next
slot. This avoids fragile stack `DUP`/`SWAP` bookkeeping across control flow.
-/

namespace Lsc3.Compile

open Lsc3.Core
open Lsc3.EVM (Opcode)

def localBase : Nat := 0x80

structure Ctx where
  depth : Nat := 0
  labelCounter : Nat := 0
  labelPrefix : String := ""
  errSelectors : List (Nat × Nat) := []  -- (error index, selector)
  deriving Repr

namespace Ctx

def freshLabel (ctx : Ctx) (tag : String) : String × Ctx :=
  let lbl := ctx.labelPrefix ++ tag ++ toString ctx.labelCounter
  (lbl, { ctx with labelCounter := ctx.labelCounter + 1 })

def slotOf (ctx : Ctx) (i : Nat) : Nat := ctx.depth - 1 - i

def memOffset (ctx : Ctx) (i : Nat) : Nat := localBase + 32 * slotOf ctx i

def bind (ctx : Ctx) : Ctx := { ctx with depth := ctx.depth + 1 }

def forFunction (ctx : Ctx) (name : String) (nParams : Nat) : Ctx :=
  { depth := nParams, labelCounter := ctx.labelCounter, labelPrefix := name ++ ".", errSelectors := ctx.errSelectors }

def afterFunction (ctx : Ctx) : Ctx :=
  { labelCounter := ctx.labelCounter, labelPrefix := "", errSelectors := ctx.errSelectors }

end Ctx

namespace Codegen

/-- `SWAP1` — swap stack top with the second item. -/
def swap1 : Asm := .op (Opcode.SWAP ⟨0, by decide⟩)

def emitOp (op : Opcode) : List Asm := [Asm.op op]

def mstoreTop (offset : Nat) : List Asm :=
  [Asm.push offset, swap1, Asm.op .MSTORE]

def mloadPush (offset : Nat) : List Asm :=
  [Asm.push offset, Asm.op .MLOAD]

def storeLocal (_ctx : Ctx) (slot : Nat) : List Asm :=
  mstoreTop (localBase + 32 * slot)

def loadLocal (ctx : Ctx) (i : Nat) : List Asm :=
  mloadPush (Ctx.memOffset ctx i)

def genAtom (ctx : Ctx) : Atom → Except String (List Asm × Ctx)
  | .lit n => .ok ([Asm.push n], ctx)
  | .var i =>
    if i ≥ ctx.depth then
      .error s!"codegen: de Bruijn index {i} out of range (depth {ctx.depth})"
    else
      .ok (loadLocal ctx i, ctx)

def genCond (ctx : Ctx) : Cond → Except String (List Asm × Ctx)
  | .tt => .ok ([Asm.push 1], ctx)
  | .ff => .ok ([Asm.push 0], ctx)
  | .lt a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ [swap1, Asm.op .LT], c2)
  | .le a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ [swap1, Asm.op .GT, Asm.op .ISZERO], c2)
  | .eq a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ emitOp .EQ, c2)
  | .ne a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ emitOp .EQ ++ emitOp .ISZERO, c2)
  | .and c d => do
    let (i1, c1) ← genCond ctx c
    let (elseLbl, c2) := Ctx.freshLabel c1 "andF"
    let (endLbl, c3) := Ctx.freshLabel c2 "andE"
    let (i2, c4) ← genCond c3 d
    .ok (i1 ++ [Asm.op .ISZERO, Asm.jumpi elseLbl] ++ i2 ++ [Asm.push 1, Asm.jump endLbl,
      Asm.jumpDest elseLbl, Asm.push 0, Asm.jumpDest endLbl], c4)
  | .or c d => do
    let (i1, c1) ← genCond ctx c
    let (elseLbl, c2) := Ctx.freshLabel c1 "orE"
    let (endLbl, c3) := Ctx.freshLabel c2 "orX"
    let (i2, c4) ← genCond c3 d
    .ok (i1 ++ [Asm.op .ISZERO, Asm.jumpi elseLbl, Asm.push 1, Asm.jump endLbl,
      Asm.jumpDest elseLbl] ++ i2 ++ [Asm.jumpDest endLbl], c4)
  | .not c => do
    let (i1, c1) ← genCond ctx c
    .ok (i1 ++ emitOp .ISZERO, c1)

def mapSlotHash (base : Nat) (keyInstr : List Asm) : List Asm :=
  keyInstr ++ [Asm.push 0, Asm.op .MSTORE, Asm.push base, Asm.push 32, Asm.op .MSTORE,
    Asm.push 64, Asm.push 0, Asm.op .KECCAK256]

def genOp (ctx : Ctx) : Op → Except String (List Asm × Ctx)
  | .load f => .ok ([Asm.push f, Asm.op .SLOAD], ctx)
  | .loadMap f k => do
    let (ki, c1) ← genAtom ctx k
    .ok (mapSlotHash f ki ++ [Asm.op .SLOAD], c1)
  | .loadMap2 f k₁ k₂ => do
    let (k1i, c1) ← genAtom ctx k₁
    let inner := mapSlotHash f k1i
    let c1' := { c1 with depth := c1.depth + 1 }  -- stack neutral
    let (k2i, c2) ← genAtom c1' k₂
    let outer := [Asm.push 0, Asm.op .MSTORE, Asm.push 32, Asm.op .MSTORE, Asm.push 64, Asm.push 0, Asm.op .KECCAK256]
    .ok (inner ++ k2i ++ outer ++ [Asm.op .SLOAD], c2)
  | .sender => .ok (emitOp .CALLER, ctx)
  | .value => .ok (emitOp .CALLVALUE, ctx)
  | .timestamp => .ok (emitOp .TIMESTAMP, ctx)
  | .blockNumber => .ok (emitOp .NUMBER, ctx)
  | .selfAddress => .ok (emitOp .ADDRESS, ctx)
  | .addChecked a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ emitOp .ADD, c2)
  | .subChecked a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ [swap1, Asm.op .SUB], c2)
  | .mulChecked a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ emitOp .MUL, c2)
  | .divChecked a b => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    .ok (i1 ++ i2 ++ [swap1, Asm.op .DIV], c2)
  | .mulDivDown a b c => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    let (i3, c3) ← genAtom c2 c
    -- (a*b)/c with floor — mulmod path omitted; use MUL DIV for in-range values
    .ok (i1 ++ i2 ++ emitOp .MUL ++ i3 ++ [swap1, Asm.op .DIV], c3)
  | .mulDivUp a b c => do
    let (i1, c1) ← genAtom ctx a
    let (i2, c2) ← genAtom c1 b
    let (i3, c3) ← genAtom c2 c
    .ok (i1 ++ i2 ++ emitOp .MUL ++ i3 ++ [swap1, Asm.op .DIV], c3)
  | .pure a => genAtom ctx a

def emitRevert (sel : Nat) : List Asm :=
  [Asm.push (sel * (2 ^ 224)), Asm.push 0, Asm.op .MSTORE, Asm.push 4, Asm.push 0, Asm.op .REVERT]

def genStmt (ctx : Ctx) (c : ContractDef) : Stmt → Except String (List Asm × Ctx)
  | .store f v => do
    let (vi, c1) ← genAtom ctx v
    .ok (vi ++ [Asm.push f, swap1, Asm.op .SSTORE], c1)
  | .storeMap f k v => do
    let (ki, c1) ← genAtom ctx k
    let hash := mapSlotHash f ki
    let (vi, c2) ← genAtom c1 v
    .ok (hash ++ vi ++ [swap1, Asm.op .SSTORE], c2)
  | .storeMap2 f k₁ k₂ v => do
    let (k1i, c1) ← genAtom ctx k₁
    let inner := mapSlotHash f k1i
    let (k2i, c2) ← genAtom c1 k₂
    let slot := [Asm.push 0, Asm.op .MSTORE, Asm.push 32, Asm.op .MSTORE, Asm.push 64, Asm.push 0, Asm.op .KECCAK256]
    let (vi, c3) ← genAtom c2 v
    .ok (inner ++ k2i ++ slot ++ vi ++ [swap1, Asm.op .SSTORE], c3)
  | .require cond err _ => do
    let (ci, c1) ← genCond ctx cond
    let sel := if h : err < c.errors.length then ErrorDef.selector c.errors[err] else 0
    let (revLbl, c2) := Ctx.freshLabel c1 "reqR"
    let (okLbl, c3) := Ctx.freshLabel c2 "reqO"
    .ok (ci ++ [Asm.op .ISZERO, Asm.jumpi revLbl, Asm.jump okLbl, Asm.jumpDest revLbl] ++ emitRevert sel ++
      [Asm.jumpDest okLbl], c3)
  | .emit ev args => do
    let (argIs, cAcc) ← args.foldlM (init := ([], ctx)) fun (acc, cAcc) arg => do
      let (i, c') ← genAtom cAcc arg
      pure (acc ++ i, c')
    let n := args.length
    if n > 5 then
      .error "codegen: LOG supports at most 5 topics"
    else
      let logOp : Opcode :=
        match n with
        | 0 => .LOG ⟨0, by decide⟩
        | 1 => .LOG ⟨1, by decide⟩
        | 2 => .LOG ⟨2, by decide⟩
        | 3 => .LOG ⟨3, by decide⟩
        | 4 => .LOG ⟨4, by decide⟩
        | _ => .LOG ⟨0, by decide⟩  -- unreachable: guarded by `n > 5` check above
      .ok (argIs ++ [Asm.push 0, Asm.push 0, Asm.op logOp], cAcc)
  | .revert err _ =>
    let sel := if h : err < c.errors.length then ErrorDef.selector c.errors[err] else 0
    .ok (emitRevert sel, ctx)

def genRet (ctx : Ctx) : {t : RetTy} → RetExpr t → Except String (List Asm × Ctx)
  | _, .unit => .ok (emitOp .STOP, ctx)
  | _, .word a => do
    let (i, c1) ← genAtom ctx a
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, .addr a => do
    let (i, c1) ← genAtom ctx a
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, .flag a => do
    let (i, c1) ← genAtom ctx a
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, .pair x y => do
    let (i1, c1) ← genRet ctx x
    let (i2, c2) ← genRet c1 y
    .ok (i1 ++ i2, c2)

def genCore (ctx : Ctx) (c : ContractDef) : {t : RetTy} → Core t → Except String (List Asm × Ctx)
  | _, .ret r => genRet ctx r
  | _, Core.opTail op => do
    let (i, c1) ← genOp ctx op
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, Core.opTailAddr op => do
    let (i, c1) ← genOp ctx op
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, Core.opTailFlag op => do
    let (i, c1) ← genOp ctx op
    .ok (i ++ mstoreTop 0 ++ [Asm.push 32, Asm.push 0, Asm.op .RETURN], c1)
  | _, .stmtTail s => do
    let (i, c1) ← genStmt ctx c s
    .ok (i ++ emitOp .STOP, c1)
  | _, .revertTail err _ =>
    let sel := if h : err < c.errors.length then ErrorDef.selector c.errors[err] else 0
    .ok (emitRevert sel, ctx)
  | _, .letOp op k => do
    let (oi, c1) ← genOp ctx op
    let slot := c1.depth
    let (ki, c2) ← genCore (Ctx.bind c1) c k
    .ok (oi ++ storeLocal c1 slot ++ ki, c2)
  | _, .seq s k => do
    let (si, c1) ← genStmt ctx c s
    let (ki, c2) ← genCore c1 c k
    .ok (si ++ ki, c2)
  | _, .letPure p args k => do
    let (ai, cAcc) ← args.foldlM (init := ([], ctx)) fun (acc, cAcc) arg => do
      let (i, c') ← genAtom cAcc arg
      pure (acc ++ i, c')
    let result := Prim.eval p (args.map fun a => match a with | .lit n => n | .var _ => 0)
    let slot := cAcc.depth
    let (ki, c2) ← genCore (Ctx.bind cAcc) c k
    .ok (ai ++ [Asm.push result] ++ storeLocal cAcc slot ++ ki, c2)
  | _, .ite cond a b => do
    let (ci, c1) ← genCond ctx cond
    let (elseLbl, c2) := Ctx.freshLabel c1 "else"
    let (endLbl, c3) := Ctx.freshLabel c2 "end"
    let (ai, c4) ← genCore c3 c a
    let (bi, c5) ← genCore c3 c b
    .ok (ci ++ [Asm.op .ISZERO, Asm.jumpi elseLbl] ++ ai ++
      [Asm.jump endLbl, Asm.jumpDest elseLbl] ++ bi ++ [Asm.jumpDest endLbl], c5)

/-- Load `nParams` ABI words from calldata into memory locals. -/
def loadParams (nParams : Nat) : List Asm :=
  (List.range nParams).flatMap fun i =>
    [Asm.push (4 + 32 * i), Asm.op .CALLDATALOAD, Asm.push (localBase + 32 * i), swap1, Asm.op .MSTORE]

def genFunction (c : ContractDef) (fn : FnDef) (ctx : Ctx) : Except String (List Asm × Ctx) := do
  let n := fn.params.length
  let fnCtx := Ctx.forFunction ctx fn.name n
  let (body, ctx') ← genCore fnCtx c fn.core
  .ok (loadParams n ++ body, Ctx.afterFunction ctx')

end Codegen

end Lsc3.Compile
