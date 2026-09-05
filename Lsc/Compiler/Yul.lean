import Lsc.Lang.Contract
import YulSemantics.Ast
import YulSemantics.Dialect.EVMOp
import YulSemantics.PrettyPrint
import KeccakEngine.Sponge

/-!
# Core → Yul (call-free fragment)

`toYulFn` compiles one `FnDef` to a powdr `YulSemantics` block. The call-free fragment is
everything in `Core` except the external ERC20 ops (`erc20Transfer`, `erc20TransferFrom`,
`erc20BalanceOf`), which need `call` and are deferred to S2. Those constructors make
`toYulFn` / `runtimeBlock` / `deployObject` return `none`.

Not emitted in this slice: `tload`/`tstore` (reentrancy lock), `gas()`, `for`, `delegatecall`,
`selfdestruct`, `create`. `ite` is `switch` (Yul `if` has no else). Dispatcher is
`switch shr(224, calldataload(0))`. Nested expressions are flattened to `let`s, and each
Core step is wrapped in `{ … }` so those temps die (powdr cannot DUP/SWAP past slot 16).
-/

namespace Lsc.Compiler

abbrev YOp := YulSemantics.EVM.Op
abbrev YExpr := YulSemantics.Expr YulSemantics.EVM.Op
abbrev YStmt := YulSemantics.Stmt YulSemantics.EVM.Op
abbrev YBlock := YulSemantics.Block YulSemantics.EVM.Op
abbrev YIdent := YulSemantics.Ident
abbrev YObject := YulSemantics.Object YulSemantics.EVM.Op

/-! ## Layout / ABI bytes (also used by tests and `toYul_correct`) -/

/-- Big-endian 32-byte encoding of a word. -/
def wordBytes (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat ((n >>> (8 * (31 - i))) % 256)

/-- Big-endian 4-byte encoding (selectors). -/
def selectorBytes (n : Nat) : List UInt8 :=
  (List.range 4).map fun i => UInt8.ofNat ((n >>> (8 * (3 - i))) % 256)

/-- Solidity `Panic(uint256)` selector. -/
def panicSelector : Nat :=
  selectorOf "Panic" [{ name := "code", ty := .uint256 }]

/-- ABI encoding of `Panic(code)` (4 + 32 bytes). -/
def panicBytes (code : Nat) : List UInt8 :=
  selectorBytes panicSelector ++ wordBytes code

/-- ABI encoding of a user error by index into `c.errors`. -/
def customErrorBytes (c : ContractDef) (err : Nat) (args : List Nat) : List UInt8 :=
  match c.errors[err]? with
  | none => []
  | some e => selectorBytes e.selector ++ args.flatMap wordBytes

/-- Calldata for a runtime call: 4-byte selector, then ABI words. -/
def fnCalldata (f : FnDef) (args : List Nat) : List UInt8 :=
  selectorBytes f.selector ++ args.flatMap wordBytes

/-- Constructor calldata: ABI words, no selector. -/
def ctorCalldata (args : List Nat) : List UInt8 :=
  args.flatMap wordBytes

/-- Solidity mapping slot: `keccak256(key ‖ slot)` as a 64-byte concatenation. -/
def mapSlot1 (keccakOf : List UInt8 → YulSemantics.EVM.U256) (slot key : Nat) :
    YulSemantics.EVM.U256 :=
  keccakOf (wordBytes key ++ wordBytes slot)

/-- Nested mapping: `keccak256(k₂ ‖ keccak256(k₁ ‖ slot))`. -/
def mapSlot2 (keccakOf : List UInt8 → YulSemantics.EVM.U256) (slot k₁ k₂ : Nat) :
    YulSemantics.EVM.U256 :=
  keccakOf (wordBytes k₂ ++ wordBytes (mapSlot1 keccakOf slot k₁).toNat)

/-- Panic codes matching `Tx.ArithError`. -/
def arithPanicCode : ArithError → Nat
  | .overflow | .underflow => 0x11
  | .divByZero => 0x12

/-- Flatten a `RetExpr` to ABI words. -/
def retAtoms : {t : RetTy} → RetExpr t → List Atom
  | _, .unit => []
  | _, .word a => [a]
  | _, .addr a => [a]
  | _, .flag a => [a]
  | _, .pair x y => retAtoms x ++ retAtoms y

/-- ABI words of a denoted return value. -/
def retWords : {t : RetTy} → t.denote → List Nat
  | .unit, _ => []
  | .word, n => [n]
  | .addr, n => [n]
  | .flag, n => [n]
  | .pair _ _, p => retWords p.1 ++ retWords p.2

def abiBytes (words : List Nat) : List UInt8 :=
  words.flatMap wordBytes

def listBytes (bs : List UInt8) : ByteArray :=
  bs.foldl ByteArray.push ByteArray.empty

/-- Concrete keccak-256 as a Yul word (KeccakEngine). Used as `EvmState.env.keccakOf`. -/
def keccakOf (bs : List UInt8) : YulSemantics.EVM.U256 :=
  BitVec.ofNat 256 (bytesToNat (KeccakEngine.keccak256 (listBytes bs)))

/-! ## Call-free fragment -/

/-- External ERC20 ops (need `call`) are excluded from this slice. -/
def opCallFree : Lsc.Op → Bool
  | .erc20TransferFrom .. | .erc20Transfer .. | .erc20BalanceOf .. => false
  | _ => true

def coreCallFree : {t : RetTy} → Core t → Bool
  | _, .ret _ => true
  | _, .opTail op => opCallFree op
  | _, .opTailAddr op => opCallFree op
  | _, .opTailFlag op => opCallFree op
  | _, .stmtTail _ => true
  | _, .revertTail .. => true
  | _, .letOp op k => opCallFree op && coreCallFree k
  | _, .seq _ k => coreCallFree k
  | _, .letPure _ _ k => coreCallFree k
  | _, .ite _ a b => coreCallFree a && coreCallFree b

/-! ## AST helpers -/

def lit (n : Nat) : YExpr := YulSemantics.Expr.lit (YulSemantics.Literal.number n)
def var (x : YIdent) : YExpr := YulSemantics.Expr.var x
def bop (op : YulSemantics.EVM.Op) (args : List YExpr) : YExpr :=
  YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args

def identV (i : Nat) : YIdent := s!"v_{i}"
def identT (i : Nat) : YIdent := s!"t_{i}"

/-- De Bruijn `i` at environment length `depth` is `v_{depth-1-i}`.
Parameters occupy `v_0 … v_{n-1}` in ABI order (first parameter first). -/
def atomE (depth : Nat) : Atom → YExpr
  | .var i => if i < depth then var (identV (depth - 1 - i)) else lit 0
  | .lit n => lit n

def revert00 : YStmt :=
  YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.revert [lit 0, lit 0])

def stopStmt : YStmt :=
  YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.stop [])

/-- Canonical constructor from `YulSemantics.EVM.constructorCode`. Nested `dataoffset` /
`datasize` are required by powdr's object layout. -/
def constructorCode (n : YIdent) : YBlock :=
  [ YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.datacopy
      [lit 0, bop YulSemantics.EVM.Op.dataoffset [ YulSemantics.Expr.lit (YulSemantics.Literal.string n) ],
        bop YulSemantics.EVM.Op.datasize [ YulSemantics.Expr.lit (YulSemantics.Literal.string n) ]]),
    YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.ret [lit 0,
      bop YulSemantics.EVM.Op.datasize [ YulSemantics.Expr.lit (YulSemantics.Literal.string n) ]]) ]

/-! ## Flattening emitter -/

structure Emit where
  tmp : Nat := 0
  acc : List YStmt := []

def Emit.push (e : Emit) (s : YStmt) : Emit :=
  { e with acc := s :: e.acc }

def Emit.fresh (e : Emit) : YIdent × Emit :=
  (identT e.tmp, { e with tmp := e.tmp + 1 })

def Emit.stmts (e : Emit) : YBlock := e.acc.reverse

mutual
  /-- Bind a (possibly nested) expression to a `let`, leaving only vars/lits as builtin args. -/
  def flatten (e : Emit) : YExpr → YExpr × Emit
    | .var x => (.var x, e)
    | .lit l => (.lit l, e)
    | .builtin op args =>
      let (args', e) := flattenRev e args
      let (t, e) := e.fresh
      (.var t, e.push (.letDecl [t] (some (YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args'))))
    | .call fn args =>
      let (args', e) := flattenRev e args
      let (t, e) := e.fresh
      (.var t, e.push (.letDecl [t] (some (.call fn args'))))

  /-- Flatten arguments **right-to-left**, matching Yul evaluation order. -/
  def flattenRev (e : Emit) : List YExpr → List YExpr × Emit
    | [] => ([], e)
    | x :: xs =>
      let (xs', e) := flattenRev e xs
      let (x', e) := flatten e x
      (x' :: xs', e)
end

/-- Assign an already-declared `name`. Nested builtins are flattened into `name`. -/
def emitAssign (e : Emit) (name : YIdent) (x : YExpr) : Emit :=
  match x with
  | .var _ | .lit _ => e.push (.assign [name] x)
  | .builtin op args =>
    let (args', e) := flattenRev e args
    e.push (.assign [name] (YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args'))
  | .call fn args =>
    let (args', e) := flattenRev e args
    e.push (.assign [name] (.call fn args'))

/-- Wrap `inner`'s statements in `{ … }` so its `let`s drop off the EVM stack (DUP16 limit). -/
def nest (e : Emit) (inner : Emit) : Emit :=
  match inner.acc with
  | [] => e
  | _ => e.push (YulSemantics.Stmt.block inner.stmts)

def emitDo (e : Emit) (op : YulSemantics.EVM.Op) (args : List YExpr) : Emit :=
  let (args', e) := flattenRev e args
  e.push (.exprStmt (YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args'))

/-- `if lt(calldatasize(), n) { revert(0,0) }` as a nested expression (no live temps). -/
def emitGuardLt (e : Emit) (n : Nat) : Emit :=
  e.push (.cond (bop YulSemantics.EVM.Op.lt [bop YulSemantics.EVM.Op.calldatasize [], lit n])
    [revert00])

/-- ABI-decode word `i` from calldata; one live `v_i`, no extra temp. -/
def emitParams (e : Emit) (offset n : Nat) : Emit :=
  (List.range n).foldl (fun e i =>
    e.push (.letDecl [identV i]
      (some (bop YulSemantics.EVM.Op.calldataload [lit (offset + 32 * i)])))) e

/-- `mstore(0x80 + 4, …)` packing after the selector word at `0x80`. -/
def abiPtr : Nat := 0x80
def abiAfterSel : Nat := 0x84

def emitPanic (e : Emit) (code : Nat) : Emit :=
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit panicSelector]]
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit abiAfterSel, lit code]
  emitDo e YulSemantics.EVM.Op.revert [lit abiPtr, lit 36]

def emitCustomError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr) : Emit :=
  let sel :=
    match c.errors[err]? with
    | some ed => ed.selector
    | none => 0
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]]
  let (e, _) := args.foldl (fun (e, i) a =>
    (emitDo e YulSemantics.EVM.Op.mstore [lit (abiAfterSel + 32 * i), a], i + 1)) (e, 0)
  emitDo e YulSemantics.EVM.Op.revert [lit abiPtr, lit (4 + 32 * args.length)]

def emitReturnWords (e : Emit) (xs : List YExpr) : Emit :=
  match xs with
  | [] => e.push stopStmt
  | _ =>
    let (e, _) := xs.foldl (fun (e, i) x =>
      (emitDo e YulSemantics.EVM.Op.mstore [lit (abiPtr + 32 * i), x], i + 1)) (e, 0)
    emitDo e YulSemantics.EVM.Op.ret [lit abiPtr, lit (32 * xs.length)]

def emitReturnUnit (e : Emit) (haltUnit : Bool) : Emit :=
  if haltUnit then e.push stopStmt else e

def emitLog1 (e : Emit) (topic : Nat) (args : List YExpr) : Emit :=
  let (e, _) := args.foldl (fun (e, i) a =>
    (emitDo e YulSemantics.EVM.Op.mstore [lit (abiPtr + 32 * i), a], i + 1)) (e, 0)
  emitDo e YulSemantics.EVM.Op.log1 [lit abiPtr, lit (32 * args.length), lit topic]

def emitMapSlot (e : Emit) (slot : Nat) (k : YExpr) : YExpr × Emit :=
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 0, k]
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 32, lit slot]
  flatten e (bop YulSemantics.EVM.Op.keccak256 [lit 0, lit 64])

/-- Nested mapping slot: `keccak256(k₂ ‖ keccak256(k₁ ‖ slot))`. -/
def emitMap2Slot (e : Emit) (slot : Nat) (k₁ k₂ : YExpr) : YExpr × Emit :=
  let (inner, e) := emitMapSlot e slot k₁
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 0, k₂]
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 32, inner]
  flatten e (bop YulSemantics.EVM.Op.keccak256 [lit 0, lit 64])

def emitIf (e : Emit) (cnd : YExpr) (body : YBlock) : Emit :=
  e.push (.cond cnd body)

/-- Overflow check for wrapping `add`: `lt(sum, a)`. -/
def emitAddChecked (e : Emit) (a b : YExpr) : YExpr × Emit :=
  let (s, e) := flatten e (bop YulSemantics.EVM.Op.add [a, b])
  let (cnd, e) := flatten e (bop YulSemantics.EVM.Op.lt [s, a])
  let eP := emitPanic { e with acc := [] } 0x11
  (s, emitIf { e with tmp := eP.tmp } cnd eP.stmts)

/-- Underflow check: `lt(a, b)` then `sub`. -/
def emitSubChecked (e : Emit) (a b : YExpr) : YExpr × Emit :=
  let (cnd, e) := flatten e (bop YulSemantics.EVM.Op.lt [a, b])
  let eP := emitPanic { e with acc := [] } 0x11
  flatten (emitIf { e with tmp := eP.tmp } cnd eP.stmts) (bop YulSemantics.EVM.Op.sub [a, b])

/-- `a = 0 ∨ div(mul(a,b), a) = b`. -/
def emitMulOverflowGuard (e : Emit) (a b p : YExpr) : Emit :=
  let (z, e) := flatten e (bop YulSemantics.EVM.Op.iszero [a])
  let (q, e) := flatten e (bop YulSemantics.EVM.Op.div [p, a])
  let (eq, e) := flatten e (bop YulSemantics.EVM.Op.eq [q, b])
  let (ok, e) := flatten e (bop YulSemantics.EVM.Op.or [z, eq])
  let (bad, e) := flatten e (bop YulSemantics.EVM.Op.iszero [ok])
  let eP := emitPanic { e with acc := [] } 0x11
  emitIf { e with tmp := eP.tmp } bad eP.stmts

def emitMulChecked (e : Emit) (a b : YExpr) : YExpr × Emit :=
  let (p, e) := flatten e (bop YulSemantics.EVM.Op.mul [a, b])
  (p, emitMulOverflowGuard e a b p)

/-- `c = 0` panics `0x12`. -/
def emitDivChecked (e : Emit) (a b : YExpr) : YExpr × Emit :=
  let (z, e) := flatten e (bop YulSemantics.EVM.Op.iszero [b])
  let eP := emitPanic { e with acc := [] } 0x12
  flatten (emitIf { e with tmp := eP.tmp } z eP.stmts) (bop YulSemantics.EVM.Op.div [a, b])

def emitMulDivDown (e : Emit) (a b c : YExpr) : YExpr × Emit :=
  let (z, e) := flatten e (bop YulSemantics.EVM.Op.iszero [c])
  let eP := emitPanic { e with acc := [] } 0x12
  let e := emitIf { e with tmp := eP.tmp } z eP.stmts
  let (p, e) := flatten e (bop YulSemantics.EVM.Op.mul [a, b])
  let e := emitMulOverflowGuard e a b p
  flatten e (bop YulSemantics.EVM.Op.div [p, c])

def emitMulDivUp (e : Emit) (a b c : YExpr) : YExpr × Emit :=
  let (q, e) := emitMulDivDown e a b c
  let (p, e) := flatten e (bop YulSemantics.EVM.Op.mul [a, b])
  let (r, e) := flatten e (bop YulSemantics.EVM.Op.mod [p, c])
  let (qn, e) :=
    match q with
    | .var n => (n, e)
    | _ =>
      let (n, e) := e.fresh
      (n, e.push (.letDecl [n] (some q)))
  (var qn, e.push (.cond r [.assign [qn] (bop YulSemantics.EVM.Op.add [.var qn, lit 1])]))

def emitOpVal (e : Emit) (depth : Nat) : Lsc.Op → Option (YExpr × Emit)
  | .load f => some (flatten e (bop YulSemantics.EVM.Op.sload [lit f]))
  | .loadMap f k =>
    let (slot, e) := emitMapSlot e f (atomE depth k)
    some (flatten e (bop YulSemantics.EVM.Op.sload [slot]))
  | .loadMap2 f k₁ k₂ =>
    let (slot, e) := emitMap2Slot e f (atomE depth k₁) (atomE depth k₂)
    some (flatten e (bop YulSemantics.EVM.Op.sload [slot]))
  | .sender => some (flatten e (bop YulSemantics.EVM.Op.caller []))
  | .value => some (flatten e (bop YulSemantics.EVM.Op.callvalue []))
  | .timestamp => some (flatten e (bop YulSemantics.EVM.Op.timestamp []))
  | .blockNumber => some (flatten e (bop YulSemantics.EVM.Op.number []))
  | .selfAddress => some (flatten e (bop YulSemantics.EVM.Op.address []))
  | .addChecked a b => some (emitAddChecked e (atomE depth a) (atomE depth b))
  | .subChecked a b => some (emitSubChecked e (atomE depth a) (atomE depth b))
  | .mulChecked a b => some (emitMulChecked e (atomE depth a) (atomE depth b))
  | .divChecked a b => some (emitDivChecked e (atomE depth a) (atomE depth b))
  | .mulDivDown a b c =>
    some (emitMulDivDown e (atomE depth a) (atomE depth b) (atomE depth c))
  | .mulDivUp a b c =>
    some (emitMulDivUp e (atomE depth a) (atomE depth b) (atomE depth c))
  | .pure a => some (atomE depth a, e)
  | .erc20TransferFrom .. | .erc20Transfer .. | .erc20BalanceOf .. => none

def emitPrim (e : Emit) (depth : Nat) (p : Prim) (args : List Atom) : YExpr × Emit :=
  match p, args with
  | .id, [a] => (atomE depth a, e)
  | .addWrap, [a, b] => flatten e (bop YulSemantics.EVM.Op.add [atomE depth a, atomE depth b])
  | .subWrap, [a, b] => flatten e (bop YulSemantics.EVM.Op.sub [atomE depth a, atomE depth b])
  | .mulWrap, [a, b] => flatten e (bop YulSemantics.EVM.Op.mul [atomE depth a, atomE depth b])
  | _, _ => (lit 0, e)

def emitCond (e : Emit) (depth : Nat) : Cond → YExpr × Emit
  | .lt a b => flatten e (bop YulSemantics.EVM.Op.lt [atomE depth a, atomE depth b])
  | .le a b =>
    let (t, e) := flatten e (bop YulSemantics.EVM.Op.lt [atomE depth b, atomE depth a])
    flatten e (bop YulSemantics.EVM.Op.iszero [t])
  | .eq a b => flatten e (bop YulSemantics.EVM.Op.eq [atomE depth a, atomE depth b])
  | .ne a b =>
    let (t, e) := flatten e (bop YulSemantics.EVM.Op.eq [atomE depth a, atomE depth b])
    flatten e (bop YulSemantics.EVM.Op.iszero [t])
  | .and c d =>
    let (x, e) := emitCond e depth c
    let (y, e) := emitCond e depth d
    flatten e (bop YulSemantics.EVM.Op.and [x, y])
  | .or c d =>
    let (x, e) := emitCond e depth c
    let (y, e) := emitCond e depth d
    flatten e (bop YulSemantics.EVM.Op.or [x, y])
  | .not c =>
    let (x, e) := emitCond e depth c
    flatten e (bop YulSemantics.EVM.Op.iszero [x])
  | .tt => (lit 1, e)
  | .ff => (lit 0, e)

def emitStmt (c : ContractDef) (e : Emit) (depth : Nat) : Lsc.Stmt → Emit
  | .store f v => emitDo e YulSemantics.EVM.Op.sstore [lit f, atomE depth v]
  | .storeMap f k v =>
    let (slot, e) := emitMapSlot e f (atomE depth k)
    emitDo e YulSemantics.EVM.Op.sstore [slot, atomE depth v]
  | .storeMap2 f k₁ k₂ v =>
    let (slot, e) := emitMap2Slot e f (atomE depth k₁) (atomE depth k₂)
    emitDo e YulSemantics.EVM.Op.sstore [slot, atomE depth v]
  | .require cond err args =>
    let (cv, e) := emitCond e depth cond
    let (z, e) := flatten e (bop YulSemantics.EVM.Op.iszero [cv])
    let eE := emitCustomError c { e with acc := [] } err (args.map (atomE depth))
    let e := { e with tmp := eE.tmp }
    e.push (.cond z eE.stmts)
  | .emit ev args =>
    let topic :=
      match c.events[ev]? with
      | some ed => ed.topic0
      | none => 0
    emitLog1 e topic (args.map (atomE depth))
  | .revert err args =>
    emitCustomError c e err (args.map (atomE depth))

def emitRet (e : Emit) (depth : Nat) (haltUnit : Bool) : {t : RetTy} → RetExpr t → Emit
  | _, .unit => emitReturnUnit e haltUnit
  | _, r => emitReturnWords e ((retAtoms r).map (atomE depth))

/-- Fresh inner emitter. Temps restart at `t_0`; they live only inside the next `nest`. -/
def innerEmit : Emit := { tmp := 0, acc := [] }

def emitCore (c : ContractDef) (e : Emit) (depth : Nat) (haltUnit : Bool) :
    {t : RetTy} → Core t → Option Emit
  | _, .ret r => some (nest e (emitRet innerEmit depth haltUnit r))
  | _, .opTail op => do
      let (x, inner) ← emitOpVal innerEmit depth op
      some (nest e (emitReturnWords inner [x]))
  | _, .opTailAddr op => do
      let (x, inner) ← emitOpVal innerEmit depth op
      some (nest e (emitReturnWords inner [x]))
  | _, .opTailFlag op => do
      let (x, inner) ← emitOpVal innerEmit depth op
      some (nest e (emitReturnWords inner [x]))
  | _, .stmtTail s =>
      some (nest e (emitReturnUnit (emitStmt c innerEmit depth s) haltUnit))
  | _, .revertTail err args =>
      some (nest e (emitCustomError c innerEmit err (args.map (atomE depth))))
  | _, .letOp op k => do
      -- Declare `v_d` in the outer scope, compute in a nested block (temps die).
      let e := e.push (.letDecl [identV depth] none)
      let (x, inner) ← emitOpVal innerEmit depth op
      let e := e.push (.block (emitAssign inner (identV depth) x).stmts)
      emitCore c e (depth + 1) haltUnit k
  | _, .seq s k =>
      emitCore c (nest e (emitStmt c innerEmit depth s)) depth haltUnit k
  | _, .letPure p args k =>
      let e := e.push (.letDecl [identV depth] none)
      let (x, inner) := emitPrim innerEmit depth p args
      let e := e.push (.block (emitAssign inner (identV depth) x).stmts)
      emitCore c e (depth + 1) haltUnit k
  | _, .ite cond a b => do
      let (cv, eC) := emitCond innerEmit depth cond
      let eA ← emitCore c innerEmit depth haltUnit a
      let eB ← emitCore c innerEmit depth haltUnit b
      -- `switch c case 0 { else } default { then }`
      let eC := eC.push (.switch cv
        [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))
      some (e.push (.block eC.stmts))

/-- Compile one function. Parameters are ABI-decoded from calldata (`offset = 4` for
runtime entrypoints, `0` for constructors). A constructor's `ret ()` falls through
(no `stop()`), so `deployObject` can append `constructorCode "runtime"`. -/
def toYulFn (c : ContractDef) (f : FnDef) : Option YBlock :=
  if !coreCallFree f.core then none
  else
    let offset := if f.kind = .constructor then 0 else 4
    let haltUnit := f.kind ≠ .constructor
    let e := emitParams {} offset f.params.length
    (emitCore c e f.params.length haltUnit f.core).map Emit.stmts

/-- `if lt(calldatasize(), 4+32n) { revert(0,0) }` in its own block so those temps are
dead before the function body (DUP16). -/
def entryCase (c : ContractDef) (f : FnDef) : Option (YulSemantics.Literal × YBlock) := do
  let body ← toYulFn c f
  let min := 4 + 32 * f.params.length
  let guard := (emitGuardLt {} min).stmts
  some (YulSemantics.Literal.number f.selector,
    [YulSemantics.Stmt.block guard, YulSemantics.Stmt.block body])

/-- Dispatcher + every non-constructor function. Size-check is its own block; the
selector is a nested expression so it does not occupy a live stack slot in the cases. -/
def runtimeBlock (c : ContractDef) : Option YBlock := do
  let cases ← c.functions.mapM (entryCase c)
  let guard := (emitGuardLt {} 4).stmts
  let sel := bop YulSemantics.EVM.Op.shr
    [lit 224, bop YulSemantics.EVM.Op.calldataload [lit 0]]
  some [YulSemantics.Stmt.block guard,
    YulSemantics.Stmt.switch sel cases (some [revert00])]

/-- Deploy object: ctor body (if any) then `constructorCode "runtime"`, nested `"runtime"`. -/
def deployObject (c : ContractDef) : Option YObject := do
  let rt ← runtimeBlock c
  let ctor ←
    match c.ctor with
    | none => some (constructorCode "runtime")
    | some f =>
      let body ← toYulFn c f
      some (body ++ constructorCode "runtime")
  some (YulSemantics.Object.mk c.name ctor [YulSemantics.Object.mk "runtime" rt [] []] [])

/-- Pretty-printer (powdr's `EVM.print`); feed to `solc --strict-assembly`. -/
def printYul (b : YBlock) : String :=
  YulSemantics.EVM.print (b : YulSemantics.Block YulSemantics.EVM.Op)

def printYulObject (o : YObject) : String :=
  YulSemantics.EVM.printObject (o : YulSemantics.Object YulSemantics.EVM.Op)

end Lsc.Compiler
