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
`switch shr(224, calldataload(0))`. Sub-expressions are nested Yul builtins (no flatten /
`t_i` temps); `{ … }` only wraps `if` bodies and `switch` cases. `toYulFn` requires
`coreWF` and `Nodup` `identV` names; `runtimeBlock` requires unique selectors.
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

/-! ## Well-formedness (decidable; `toYulFn` / `runtimeBlock` return `none` otherwise) -/

def atomWF : Atom → Bool
  | .var _ => true
  | .lit n => decide (n < wordBound)

def atomsWF (as : List Atom) : Bool := as.all atomWF

def condWF : Cond → Bool
  | .lt a b | .le a b | .eq a b | .ne a b => atomWF a && atomWF b
  | .and c d | .or c d => condWF c && condWF d
  | .not c => condWF c
  | .tt | .ff => true

def fieldKindOK (c : ContractDef) (idx : Nat) (k : FieldKind) : Bool :=
  match c.fields[idx]? with
  | some fd => decide (fd.kind = k)
  | none => false

def eventOK (c : ContractDef) (ev n : Nat) : Bool :=
  match c.events[ev]? with
  | some ed => decide (ed.params.length = n)
  | none => false

def errorOK (c : ContractDef) (err n : Nat) : Bool :=
  match c.errors[err]? with
  | some ed => decide (ed.params.length = n)
  | none => false

def opWF (c : ContractDef) : Lsc.Op → Bool
  | .load f => fieldKindOK c f .scalar
  | .loadMap f k => fieldKindOK c f .map1 && atomWF k
  | .loadMap2 f k₁ k₂ => fieldKindOK c f .map2 && atomWF k₁ && atomWF k₂
  | .sender | .value | .timestamp | .blockNumber | .selfAddress => true
  | .addChecked a b | .subChecked a b | .mulChecked a b | .divChecked a b =>
      atomWF a && atomWF b
  | .mulDivDown a b d | .mulDivUp a b d => atomWF a && atomWF b && atomWF d
  | .erc20TransferFrom a b d e => atomsWF [a, b, d, e]
  | .erc20Transfer a b d => atomsWF [a, b, d]
  | .erc20BalanceOf a b => atomWF a && atomWF b
  | .pure a => atomWF a

def stmtWF (c : ContractDef) : Lsc.Stmt → Bool
  | .store f v => fieldKindOK c f .scalar && atomWF v
  | .storeMap f k v => fieldKindOK c f .map1 && atomWF k && atomWF v
  | .storeMap2 f k₁ k₂ v => fieldKindOK c f .map2 && atomWF k₁ && atomWF k₂ && atomWF v
  | .require cond err args => condWF cond && errorOK c err args.length && args.all atomWF
  | .emit ev args => eventOK c ev args.length && args.all atomWF
  | .revert err args => errorOK c err args.length && args.all atomWF

def retWF : {t : RetTy} → RetExpr t → Bool
  | _, .unit => true
  | _, .word a => atomWF a
  | _, .addr a => atomWF a
  | _, .flag a => atomWF a
  | _, .pair x y => retWF x && retWF y

def coreWF (c : ContractDef) : {t : RetTy} → Core t → Bool
  | _, .ret r => retWF r
  | _, .opTail op => opWF c op
  | _, .opTailAddr op => opWF c op
  | _, .opTailFlag op => opWF c op
  | _, .stmtTail s => stmtWF c s
  | _, .revertTail err args => errorOK c err args.length && args.all atomWF
  | _, .letOp op k => opWF c op && coreWF c k
  | _, .seq s k => stmtWF c s && coreWF c k
  | _, .letPure _ args k => args.all atomWF && coreWF c k
  | _, .ite cond a b => condWF cond && coreWF c a && coreWF c b

/-- Extra `let`s under `f` (`opTail` desugars to one). `maxDepth f = params + extra`. -/
def coreExtraDepth : {t : RetTy} → Core t → Nat
  | _, .ret _ => 0
  | _, .opTail _ => 1
  | _, .opTailAddr _ => 1
  | _, .opTailFlag _ => 1
  | _, .stmtTail _ => 0
  | _, .revertTail .. => 0
  | _, .letOp _ k => coreExtraDepth k + 1
  | _, .seq _ k => coreExtraDepth k
  | _, .letPure _ _ k => coreExtraDepth k + 1
  | _, .ite _ a b => max (coreExtraDepth a) (coreExtraDepth b)

def maxDepth (f : FnDef) : Nat := f.params.length + coreExtraDepth f.core

def identsNodup (n : Nat) : Bool :=
  decide (((List.range n).map identV).Pairwise (fun a b => a ≠ b))

def selectorsNodup (c : ContractDef) : Bool :=
  decide ((c.functions.map (fun f => f.selector)).Pairwise (fun a b => a ≠ b))

theorem atomWF_iff (a : Atom) :
    atomWF a = true ↔ match a with | .var _ => True | .lit n => n < wordBound := by
  cases a <;> simp [atomWF, decide_eq_true_eq]

theorem fieldKindOK_iff (c : ContractDef) (idx : Nat) (k : FieldKind) :
    fieldKindOK c idx k = true ↔ ∃ fd, c.fields[idx]? = some fd ∧ fd.kind = k := by
  simp only [fieldKindOK]
  cases c.fields[idx]? <;> simp [decide_eq_true_eq]

theorem eventOK_iff (c : ContractDef) (ev n : Nat) :
    eventOK c ev n = true ↔ ∃ ed, c.events[ev]? = some ed ∧ ed.params.length = n := by
  simp only [eventOK]
  cases c.events[ev]? <;> simp [decide_eq_true_eq]

theorem errorOK_iff (c : ContractDef) (err n : Nat) :
    errorOK c err n = true ↔ ∃ ed, c.errors[err]? = some ed ∧ ed.params.length = n := by
  simp only [errorOK]
  cases c.errors[err]? <;> simp [decide_eq_true_eq]

theorem identsNodup_iff (n : Nat) :
    identsNodup n = true ↔ ((List.range n).map identV).Pairwise (fun a b => a ≠ b) := by
  simp [identsNodup, decide_eq_true_eq]

theorem selectorsNodup_iff (c : ContractDef) :
    selectorsNodup c = true ↔
      (c.functions.map (fun f => f.selector)).Pairwise (fun a b => a ≠ b) := by
  simp [selectorsNodup, decide_eq_true_eq]

/-! ## Temp-free emitter (nested expressions; result variable as scratch) -/

structure Emit where
  acc : List YStmt := []

def Emit.push (e : Emit) (s : YStmt) : Emit :=
  { e with acc := s :: e.acc }

def Emit.stmts (e : Emit) : YBlock := e.acc.reverse

def emitDo (e : Emit) (op : YulSemantics.EVM.Op) (args : List YExpr) : Emit :=
  e.push (.exprStmt (YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args))

def emitLet (e : Emit) (name : YIdent) (x : YExpr) : Emit :=
  e.push (.letDecl [name] (some x))

def emitIf (e : Emit) (cnd : YExpr) (body : YBlock) : Emit :=
  e.push (.cond cnd body)

/-- `if lt(calldatasize(), n) { revert(0,0) }`. -/
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

def keccak064 : YExpr := bop YulSemantics.EVM.Op.keccak256 [lit 0, lit 64]

def emitPanic (e : Emit) (code : Nat) : Emit :=
  let e := emitDo e YulSemantics.EVM.Op.mstore
    [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit panicSelector]]
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit abiAfterSel, lit code]
  emitDo e YulSemantics.EVM.Op.revert [lit abiPtr, lit 36]

def emitCustomError (c : ContractDef) (e : Emit) (err : Nat) (args : List YExpr) : Emit :=
  let sel :=
    match c.errors[err]? with
    | some ed => ed.selector
    | none => 0
  let e := emitDo e YulSemantics.EVM.Op.mstore
    [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]]
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

/-- `mstore(0, k) mstore(32, slot)` so a subsequent nested `keccak256(0,64)` is the map slot. -/
def emitMapSlotPrep (e : Emit) (slot : Nat) (k : YExpr) : Emit :=
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 0, k]
  emitDo e YulSemantics.EVM.Op.mstore [lit 32, lit slot]

/-- Nested mapping. `keccak256(0,64)` reads `[0,64)`, so the inner hash must be written to
`[32]` *before* `mstore(0, k₂)` overwrites `[0]`: `mstore(32, keccak256(0,64)); mstore(0, k₂)`. -/
def emitMap2SlotPrep (e : Emit) (slot : Nat) (k₁ k₂ : YExpr) : Emit :=
  let e := emitMapSlotPrep e slot k₁
  let e := emitDo e YulSemantics.EVM.Op.mstore [lit 32, keccak064]
  emitDo e YulSemantics.EVM.Op.mstore [lit 0, k₂]

/-- Overflow: `a = 0 ∨ div(p, a) = b`. Nested; `p` is the product variable. -/
def emitMulOverflowGuard (e : Emit) (a b p : YExpr) : Emit :=
  emitIf e
    (bop YulSemantics.EVM.Op.iszero
      [bop YulSemantics.EVM.Op.or
        [bop YulSemantics.EVM.Op.iszero [a],
          bop YulSemantics.EVM.Op.eq [bop YulSemantics.EVM.Op.div [p, a], b]]])
    (emitPanic {} 0x11).stmts

/-- `let name := add(a,b)` then `if lt(name, a) { panic }`. -/
def emitAddChecked (e : Emit) (name : YIdent) (a b : YExpr) : Emit :=
  let e := emitLet e name (bop YulSemantics.EVM.Op.add [a, b])
  emitIf e (bop YulSemantics.EVM.Op.lt [var name, a]) (emitPanic {} 0x11).stmts

/-- `if lt(a, b) { panic }` then `let name := sub(a,b)`. -/
def emitSubChecked (e : Emit) (name : YIdent) (a b : YExpr) : Emit :=
  let e := emitIf e (bop YulSemantics.EVM.Op.lt [a, b]) (emitPanic {} 0x11).stmts
  emitLet e name (bop YulSemantics.EVM.Op.sub [a, b])

def emitMulChecked (e : Emit) (name : YIdent) (a b : YExpr) : Emit :=
  let e := emitLet e name (bop YulSemantics.EVM.Op.mul [a, b])
  emitMulOverflowGuard e a b (var name)

/-- `if iszero(b) { panic 0x12 }` then `let name := div(a,b)`. -/
def emitDivChecked (e : Emit) (name : YIdent) (a b : YExpr) : Emit :=
  let e := emitIf e (bop YulSemantics.EVM.Op.iszero [b]) (emitPanic {} 0x12).stmts
  emitLet e name (bop YulSemantics.EVM.Op.div [a, b])

/-- `let name := mul(a,b)` + overflow guard + `name := div(name,c)`. -/
def emitMulDivDown (e : Emit) (name : YIdent) (a b c : YExpr) : Emit :=
  let e := emitIf e (bop YulSemantics.EVM.Op.iszero [c]) (emitPanic {} 0x12).stmts
  let e := emitLet e name (bop YulSemantics.EVM.Op.mul [a, b])
  let e := emitMulOverflowGuard e a b (var name)
  e.push (.assign [name] (bop YulSemantics.EVM.Op.div [var name, c]))

/-- Same product/guard, then `switch mod(name,c)` to round up. -/
def emitMulDivUp (e : Emit) (name : YIdent) (a b c : YExpr) : Emit :=
  let e := emitIf e (bop YulSemantics.EVM.Op.iszero [c]) (emitPanic {} 0x12).stmts
  let e := emitLet e name (bop YulSemantics.EVM.Op.mul [a, b])
  let e := emitMulOverflowGuard e a b (var name)
  e.push (.switch (bop YulSemantics.EVM.Op.mod [var name, c])
    [(YulSemantics.Literal.number 0,
      [.assign [name] (bop YulSemantics.EVM.Op.div [var name, c])])]
    (some [.assign [name]
      (bop YulSemantics.EVM.Op.add [bop YulSemantics.EVM.Op.div [var name, c], lit 1])]))

def emitLetOp (e : Emit) (depth : Nat) : Lsc.Op → Option Emit
  | .load f => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.sload [lit f]))
  | .loadMap f k =>
    let e := emitMapSlotPrep e f (atomE depth k)
    some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.sload [keccak064]))
  | .loadMap2 f k₁ k₂ =>
    let e := emitMap2SlotPrep e f (atomE depth k₁) (atomE depth k₂)
    some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.sload [keccak064]))
  | .sender => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.caller []))
  | .value => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.callvalue []))
  | .timestamp => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.timestamp []))
  | .blockNumber => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.number []))
  | .selfAddress => some (emitLet e (identV depth) (bop YulSemantics.EVM.Op.address []))
  | .addChecked a b =>
      some (emitAddChecked e (identV depth) (atomE depth a) (atomE depth b))
  | .subChecked a b =>
      some (emitSubChecked e (identV depth) (atomE depth a) (atomE depth b))
  | .mulChecked a b =>
      some (emitMulChecked e (identV depth) (atomE depth a) (atomE depth b))
  | .divChecked a b =>
      some (emitDivChecked e (identV depth) (atomE depth a) (atomE depth b))
  | .mulDivDown a b c =>
      some (emitMulDivDown e (identV depth) (atomE depth a) (atomE depth b) (atomE depth c))
  | .mulDivUp a b c =>
      some (emitMulDivUp e (identV depth) (atomE depth a) (atomE depth b) (atomE depth c))
  | .pure a => some (emitLet e (identV depth) (atomE depth a))
  | .erc20TransferFrom .. | .erc20Transfer .. | .erc20BalanceOf .. => none

def emitPrim (depth : Nat) (p : Prim) (args : List Atom) : YExpr :=
  match p, args with
  | .id, [a] => atomE depth a
  | .addWrap, [a, b] => bop YulSemantics.EVM.Op.add [atomE depth a, atomE depth b]
  | .subWrap, [a, b] => bop YulSemantics.EVM.Op.sub [atomE depth a, atomE depth b]
  | .mulWrap, [a, b] => bop YulSemantics.EVM.Op.mul [atomE depth a, atomE depth b]
  | _, _ => lit 0

def emitCond (depth : Nat) : Cond → YExpr
  | .lt a b => bop YulSemantics.EVM.Op.lt [atomE depth a, atomE depth b]
  | .le a b =>
    bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.lt [atomE depth b, atomE depth a]]
  | .eq a b => bop YulSemantics.EVM.Op.eq [atomE depth a, atomE depth b]
  | .ne a b =>
    bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.eq [atomE depth a, atomE depth b]]
  | .and c d => bop YulSemantics.EVM.Op.and [emitCond depth c, emitCond depth d]
  | .or c d => bop YulSemantics.EVM.Op.or [emitCond depth c, emitCond depth d]
  | .not c => bop YulSemantics.EVM.Op.iszero [emitCond depth c]
  | .tt => lit 1
  | .ff => lit 0

def emitStmt (c : ContractDef) (e : Emit) (depth : Nat) : Lsc.Stmt → Emit
  | .store f v => emitDo e YulSemantics.EVM.Op.sstore [lit f, atomE depth v]
  | .storeMap f k v =>
    let e := emitMapSlotPrep e f (atomE depth k)
    emitDo e YulSemantics.EVM.Op.sstore [keccak064, atomE depth v]
  | .storeMap2 f k₁ k₂ v =>
    let e := emitMap2SlotPrep e f (atomE depth k₁) (atomE depth k₂)
    emitDo e YulSemantics.EVM.Op.sstore [keccak064, atomE depth v]
  | .require cond err args =>
    emitIf e (bop YulSemantics.EVM.Op.iszero [emitCond depth cond])
      (emitCustomError c {} err (args.map (atomE depth))).stmts
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

def emitCore (c : ContractDef) (e : Emit) (depth : Nat) (haltUnit : Bool) :
    {t : RetTy} → Core t → Option Emit
  | _, .ret r => some (emitRet e depth haltUnit r)
  | _, .opTail op => do
      let e ← emitLetOp e depth op
      some (emitRet e (depth + 1) haltUnit (.word (.var 0)))
  | _, .opTailAddr op => do
      let e ← emitLetOp e depth op
      some (emitRet e (depth + 1) haltUnit (.addr (.var 0)))
  | _, .opTailFlag op => do
      let e ← emitLetOp e depth op
      some (emitRet e (depth + 1) haltUnit (.flag (.var 0)))
  | _, .stmtTail s => some (emitReturnUnit (emitStmt c e depth s) haltUnit)
  | _, .revertTail err args => some (emitCustomError c e err (args.map (atomE depth)))
  | _, .letOp op k => do
      let e ← emitLetOp e depth op
      emitCore c e (depth + 1) haltUnit k
  | _, .seq s k => emitCore c (emitStmt c e depth s) depth haltUnit k
  | _, .letPure p args k =>
      emitCore c (emitLet e (identV depth) (emitPrim depth p args)) (depth + 1) haltUnit k
  | _, .ite cond a b => do
      let eA ← emitCore c {} depth haltUnit a
      let eB ← emitCore c {} depth haltUnit b
      some (e.push (.switch (emitCond depth cond)
        [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))

/-- Compile one function. Parameters are ABI-decoded from calldata (`offset = 4` for
runtime entrypoints, `0` for constructors). A constructor's `ret ()` falls through
(no `stop()`), so `deployObject` can append `constructorCode "runtime"`. -/
def toYulFn (c : ContractDef) (f : FnDef) : Option YBlock :=
  if !coreCallFree f.core then none
  else if !coreWF c f.core then none
  else if !identsNodup (maxDepth f) then none
  else
    let offset := if f.kind = .constructor then 0 else 4
    let haltUnit := f.kind ≠ .constructor
    let e := emitParams {} offset f.params.length
    (emitCore c e f.params.length haltUnit f.core).map Emit.stmts

/-- `if lt(calldatasize(), 4+32n) { revert(0,0) }` then the function body, as two blocks
inside the selector `switch` case. -/
def entryCase (c : ContractDef) (f : FnDef) : Option (YulSemantics.Literal × YBlock) := do
  let body ← toYulFn c f
  let min := 4 + 32 * f.params.length
  let guard := (emitGuardLt {} min).stmts
  some (YulSemantics.Literal.number f.selector,
    [YulSemantics.Stmt.block guard, YulSemantics.Stmt.block body])

/-- Dispatcher + every non-constructor function. Size-check is its own block; the
selector is a nested expression so it does not occupy a live stack slot in the cases. -/
def runtimeBlock (c : ContractDef) : Option YBlock :=
  if !selectorsNodup c then none
  else do
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
