import Lsc.Lang.Contract
import YulSemantics.Ast
import YulSemantics.Dialect.EVMOp
import YulSemantics.PrettyPrint
import KeccakEngine.Sponge

/-!
# Core → Yul

`toYulFn` compiles one `FnDef` to a powdr `YulSemantics` block. `Op.call` /
`Stmt.call` / `Op.view` / `Stmt.view` are emitted as a scoped Yul block: ABI
pack at `0x80` (`mstore(0x80, shl(224, sel))`, args at `0x84+`), then
`call(extCallGas, target, 0, …)` or `staticcall(extCallGas, target, …)`,
`if iszero(ok) { revert(0,0) }`, then `AbiRet` decode. Temporaries `_ok_*`
live inside the block so `restore` drops them; the Core result variable is
declared outside and assigned inside. `toYulFn` does **not** return `none` on
calls.

Every runtime entry checks `tload(0)` and reverts if the slot is set
(including `[Reentrant]` functions: the prologue is per-runtime, not
per-function). Mutating non-reentrant functions with an outgoing
CALL/STATICCALL (`locks f`) `tstore(0,1)` after the per-function size
guard and `tstore(0,0)` before each committing `return`/`stop`.
`[Reentrant]` functions, pure-read views (including those with `Op.view`),
and call-free mutators do not write the lock. Constructor (`toYulCtor`) is
unchanged. Not emitted: `for`, `delegatecall`, `selfdestruct`, `create`.
`ite` is `switch` (Yul `if` has no else). Dispatcher is
`switch shr(224, calldataload(0))`. Sub-expressions are nested Yul builtins
(no flatten / `t_i` temps); `{ … }` wraps `if` bodies, `switch` cases, and
external-call temps. `toYulFn` requires `coreWF` and `Nodup` `identV` names
(`{f.name}_{i}`, unique across the dispatcher `switch`); `runtimeBlock`
requires unique selectors.
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

/-- Gas stipend forwarded to CALL/STATICCALL. A literal, not `gas()`: the S2
dialect is `ExternalGas.none` (needed by the spill-path theorem), so `gas()`
would be stuck. The EVM still caps the forwarded amount at 63/64 of remaining
gas. -/
def extCallGas : Nat := 1_000_000

/-- ABI packing / CALL in-out / panic / custom error / `log1` / returns start here. -/
def abiPtr : Nat := 0x80
def abiAfterSel : Nat := 0x84

/-- Reserved memory size declared by `memoryguard`. Keccak scratch is `[0,64)`
and ABI packing starts at `abiPtr`. A 3-arg `transferFrom` ends at 228; a
4-word `log1` ends at 256. The marker is a discarded truthiness test
(`if memoryguard(k) {}`), so it does not write the free-memory pointer.
Constructor is not guarded (`datacopy(0, …)` would smash scratch). -/
def memoryGuardK : Nat := 256

/-- EIP-1153 transient slot for the reentrancy lock. Disjoint from persistent
storage; Lsc emits no other `tstore`. -/
def reentrancyLockSlot : Nat := 0

/-- Mutating non-reentrant functions with any outgoing CALL/STATICCALL take
the lock. `[Reentrant]` functions never acquire or release it. Pure-read
views with an outgoing `staticcall` do not: they have no inconsistent
window and must stay honest `view`s (STATICCALL-callable). -/
def locks (f : FnDef) : Bool :=
  !f.reentrant && Core.hasExtCall f.core && !Core.isPureRead f.core

/-- Aligned ABI words at `abiPtr` fit in `[0, memoryGuardK)`. Equivalent to `n ≤ 4`. -/
def fitsGuardWords (n : Nat) : Bool := decide (abiPtr + 32 * n ≤ memoryGuardK)

/-- CALL / custom-error packing (`4 + 32n` bytes from `abiPtr`) fits. Equivalent to `n ≤ 3`. -/
def fitsGuardCall (n : Nat) : Bool := decide (abiPtr + 4 + 32 * n ≤ memoryGuardK)

/-! ## AST helpers -/

def lit (n : Nat) : YExpr := YulSemantics.Expr.lit (YulSemantics.Literal.number n)
def var (x : YIdent) : YExpr := YulSemantics.Expr.var x
def bop (op : YulSemantics.EVM.Op) (args : List YExpr) : YExpr :=
  YulSemantics.Expr.builtin (Op := YulSemantics.EVM.Op) op args

section IdentV

/-- Per-function locals. `tag` is `f.name` at `toYulFn` / `toYulCtor`, so inlined
switch cases do not reuse names (`addLiquidity_0` vs `swap0for1_0`). -/
def identV (tag : String) (i : Nat) : YIdent := s!"{tag}_{i}"

/-- Join-result scratch; not an `identV` so switch-case lets can reuse `{tag}_{depth}`. -/
def identPhi (tag : String) (i : Nat) : YIdent := s!"{tag}__phi_{i}"

/-- De Bruijn `i` at environment length `depth` is `{tag}_{depth-1-i}`.
Parameters occupy `{tag}_0 … {tag}_{n-1}` in ABI order (first parameter first). -/
def atomE (tag : String) (depth : Nat) : Atom → YExpr
  | .var i => if i < depth then var (identV tag (depth - 1 - i)) else lit 0
  | .lit n => lit n

def revert00 : YStmt :=
  YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.revert [lit 0, lit 0])

def stopStmt : YStmt :=
  YulSemantics.Stmt.exprStmt (bop YulSemantics.EVM.Op.stop [])

/-- `if tload(0) { revert(0,0) }`. Every runtime entry, including views,
`[Reentrant]` functions, and the default selector. -/
def lockCheckStmt : YStmt :=
  .cond (bop YulSemantics.EVM.Op.tload [lit reentrancyLockSlot]) [revert00]

/-- `tstore(0, 1)` — acquire. Only in `entryCase` of a locking function. -/
def lockSetStmt : YStmt :=
  .exprStmt (bop YulSemantics.EVM.Op.tstore [lit reentrancyLockSlot, lit 1])

/-- `tstore(0, 0)` — release. Prefixed on every committing `return`/`stop`
of a locking function. Revert paths rely on EVM/Yul rollback. -/
def lockClearStmt : YStmt :=
  .exprStmt (bop YulSemantics.EVM.Op.tstore [lit reentrancyLockSlot, lit 0])

/-- Empty when `locks f` is false, so non-locking `entryCase` is
definitionally the historical `[block guard, block body]`. -/
def lockSetPrefix (f : FnDef) : YBlock :=
  if locks f then [lockSetStmt] else []

/-- `if callvalue() { revert(0,0) }`. Solidity non-payable: a nonzero
value reverts with empty data, same shape as the unknown-selector path. -/
def valueCheckStmt : YStmt :=
  .cond (bop YulSemantics.EVM.Op.callvalue []) [revert00]

/-- Empty when `f.payable`, so payable `entryCase` stays the historical
guard / lock / body layout. Non-payable cases insert `valueCheckStmt`
after the calldata-size guard and before lock acquire. -/
def valueCheckPrefix (f : FnDef) : YBlock :=
  if f.payable then [] else [valueCheckStmt]

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
  | some ed => decide (ed.params.length = n) && fitsGuardWords n
  | none => false

def errorOK (c : ContractDef) (err n : Nat) : Bool :=
  match c.errors[err]? with
  | some ed => decide (ed.params.length = n) && fitsGuardCall n
  | none => false

/-- Target in range and CALL/STATICCALL packing (`4 + 32n` bytes from `abiPtr`)
fits the memory guard. Equivalent to `n ≤ 3`. -/
def callWF (target : Atom) (args : List Atom) : Bool :=
  atomWF target && args.all atomWF && fitsGuardCall args.length

def opWF (c : ContractDef) : Lsc.Op → Bool
  | .load f => fieldKindOK c f .scalar
  | .loadMap f k => fieldKindOK c f .map1 && atomWF k
  | .loadMap2 f k₁ k₂ => fieldKindOK c f .map2 && atomWF k₁ && atomWF k₂
  | .sender | .value | .timestamp | .blockNumber | .selfAddress | .selfBalance => true
  | .addChecked a b | .subChecked a b | .mulChecked a b | .divChecked a b =>
      atomWF a && atomWF b
  | .mulDivDown a b d | .mulDivUp a b d => atomWF a && atomWF b && atomWF d
  | .pow10 d => atomWF d
  | .call t sel args _ => callWF t args && decide (sel < 2 ^ 32)
  | .view t sel args _ => callWF t args && decide (sel < 2 ^ 32)
  | .send t amt => atomWF t && atomWF amt
  | .pure a => atomWF a

def stmtWF (c : ContractDef) : Lsc.Stmt → Bool
  | .store f v => fieldKindOK c f .scalar && atomWF v
  | .storeMap f k v => fieldKindOK c f .map1 && atomWF k && atomWF v
  | .storeMap2 f k₁ k₂ v => fieldKindOK c f .map2 && atomWF k₁ && atomWF k₂ && atomWF v
  | .require cond err args => condWF cond && errorOK c err args.length && args.all atomWF
  | .emit ev args => eventOK c ev args.length && args.all atomWF
  | .revert err args => errorOK c err args.length && args.all atomWF
  | .call t sel args _ => callWF t args && decide (sel < 2 ^ 32)
  | .view t sel args _ => callWF t args && decide (sel < 2 ^ 32)

def retWF : {t : RetTy} → RetExpr t → Bool
  | _, .unit => true
  | _, .word a => atomWF a
  | _, .addr a => atomWF a
  | _, .flag a => atomWF a
  | _, .pair x y => retWF x && retWF y

def coreWF (c : ContractDef) : {t : RetTy} → Core t → Bool
  | _, .ret r => retWF r && fitsGuardWords (retAtoms r).length
  | _, .opTail op => opWF c op
  | _, .opTailAddr op => opWF c op
  | _, .opTailFlag op => opWF c op
  | _, .stmtTail s => stmtWF c s
  | _, .revertTail err args => errorOK c err args.length && args.all atomWF
  | _, .letOp op k => opWF c op && coreWF c k
  | _, .seq s k => stmtWF c s && coreWF c k
  | _, .letPure _ args k => args.all atomWF && coreWF c k
  | _, .ite cond a b => condWF cond && coreWF c a && coreWF c b
  | _, .seqIf (t := t) cond th el k =>
      condWF cond && coreWF c th && coreWF c el && coreWF c k &&
        match t with
        | .pair _ _ => false
        | _ => true

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
  | _, .seqIf (t := t) _ th el k =>
      let br := max (coreExtraDepth th) (coreExtraDepth el)
      match t with
      | .word | .addr | .flag => max br (coreExtraDepth k + 1)
      | .unit | .pair _ _ => max br (coreExtraDepth k)

def maxDepth (f : FnDef) : Nat := f.params.length + coreExtraDepth f.core

def identsNodup (tag : String) (n : Nat) : Bool :=
  decide (((List.range n).map (identV tag)).Pairwise (fun a b => a ≠ b))

def selectorsNodup (c : ContractDef) : Bool :=
  decide ((c.functions.map (fun f => f.selector)).Pairwise (fun a b => a ≠ b))

/-! ## `NoExternalOps`: call-free Yul (no `call`/`create`/`gas`) -/

/-- EVM ops whose open-world interpretation is not `stepOp`. -/
def noExtOp : YOp → Bool
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 | .gas
  | .selfdestruct => false
  | _ => true

mutual
def noExtExpr : YExpr → Bool
  | .lit _ | .var _ => true
  | .builtin op args => noExtOp op && noExtExprs args
  | .call _ args => noExtExprs args

def noExtExprs : List YExpr → Bool
  | [] => true
  | e :: es => noExtExpr e && noExtExprs es

def noExtStmt : YStmt → Bool
  | .block b => noExtStmts b
  | .funDef _ _ _ b => noExtStmts b
  | .letDecl _ none => true
  | .letDecl _ (some e) => noExtExpr e
  | .assign _ e => noExtExpr e
  | .cond c b => noExtExpr c && noExtStmts b
  | .switch c cases dflt =>
      noExtExpr c && noExtCases cases &&
        match dflt with
        | none => true
        | some b => noExtStmts b
  | .forLoop init c post body =>
      noExtStmts init && noExtExpr c && noExtStmts post && noExtStmts body
  | .exprStmt e => noExtExpr e
  | .«break» | .«continue» | .leave => true

def noExtStmts : List YStmt → Bool
  | [] => true
  | s :: ss => noExtStmt s && noExtStmts ss

def noExtCases : List (YulSemantics.Literal × List YStmt) → Bool
  | [] => true
  | p :: rest => noExtStmts p.2 && noExtCases rest
end

def noExtBlock (ss : YBlock) : Bool := noExtStmts ss


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

def emitAssign (e : Emit) (name : YIdent) (x : YExpr) : Emit :=
  e.push (.assign [name] x)

def emitBlock (e : Emit) (body : YBlock) : Emit :=
  e.push (.block body)

def emitIf (e : Emit) (cnd : YExpr) (body : YBlock) : Emit :=
  e.push (.cond cnd body)

/-- Per-function CALL/STATICCALL success flag. -/
def extOk (tag : String) (d : Nat) : YIdent := s!"{tag}__ok_{d}"

/-- `if lt(calldatasize(), n) { revert(0,0) }`. -/
def emitGuardLt (e : Emit) (n : Nat) : Emit :=
  e.push (.cond (bop YulSemantics.EVM.Op.lt [bop YulSemantics.EVM.Op.calldatasize [], lit n])
    [revert00])

/-- ABI-decode word `i` from calldata; one live `{tag}_i`, no extra temp. -/
def emitParams (tag : String) (e : Emit) (offset n : Nat) : Emit :=
  (List.range n).foldl (fun e i =>
    e.push (.letDecl [identV tag i]
      (some (bop YulSemantics.EVM.Op.calldataload [lit (offset + 32 * i)])))) e

/-- Solidity CREATE convention: constructor args are the last `32n` bytes of init code.
Copy them to memory at `abiPtr` (`0x80`), then `mload` into `{tag}_i`. Runtime `emitParams`
is unchanged. `n = 0` skips the copy. -/
def emitCtorCopy (e : Emit) (n : Nat) : Emit :=
  if n = 0 then e
  else
    let argsLen := 32 * n
    emitDo e YulSemantics.EVM.Op.codecopy
      [lit abiPtr,
       bop YulSemantics.EVM.Op.sub [bop YulSemantics.EVM.Op.codesize [], lit argsLen],
       lit argsLen]

def emitCtorLoads (tag : String) (e : Emit) (n : Nat) : Emit :=
  (List.range n).foldl (fun e i =>
    e.push (.letDecl [identV tag i]
      (some (bop YulSemantics.EVM.Op.mload [lit (abiPtr + 32 * i)])))) e

def emitCtorParams (tag : String) (e : Emit) (n : Nat) : Emit :=
  emitCtorLoads tag (emitCtorCopy e n) n

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

def emitLockClear (e : Emit) : Emit :=
  e.push lockClearStmt

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

/-- `if gt(d, 77) { panic 0x11 }` then `let name := exp(10, d)`. -/
def emitPow10 (e : Emit) (name : YIdent) (d : YExpr) : Emit :=
  let e := emitIf e (bop YulSemantics.EVM.Op.gt [d, lit 77]) (emitPanic {} 0x11).stmts
  emitLet e name (bop YulSemantics.EVM.Op.exp [lit 10, d])

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

/-- After a successful CALL/STATICCALL: `boolOpt` is empty returndata (true) or
exactly one ABI word (`word ≠ 0` ⇒ true); `word` requires exactly one ABI word
(`32 ≤ returndatasize < 64`). Short (1–31) and two-word (`≥ 64`) payloads
revert, matching `AbiRetType.decode none` = `callFailed`. -/
def emitCallRetCheck (e : Emit) (ret : AbiRet) : Emit :=
  match ret with
  | .boolOpt =>
    -- revert unless `returndatasize = 0 ∨ (32 ≤ returndatasize ∧ returndatasize < 64)`
    emitIf e
      (bop YulSemantics.EVM.Op.iszero
        [bop YulSemantics.EVM.Op.or
          [bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.returndatasize []],
            bop YulSemantics.EVM.Op.and
              [bop YulSemantics.EVM.Op.iszero
                [bop YulSemantics.EVM.Op.lt
                  [bop YulSemantics.EVM.Op.returndatasize [], lit 32]],
                bop YulSemantics.EVM.Op.lt
                  [bop YulSemantics.EVM.Op.returndatasize [], lit 64]]]])
      [revert00]
  | .word =>
    -- revert unless `32 ≤ returndatasize < 64` (exactly one ABI word)
    emitIf e
      (bop YulSemantics.EVM.Op.iszero
        [bop YulSemantics.EVM.Op.and
          [bop YulSemantics.EVM.Op.iszero
            [bop YulSemantics.EVM.Op.lt
              [bop YulSemantics.EVM.Op.returndatasize [], lit 32]],
            bop YulSemantics.EVM.Op.lt
              [bop YulSemantics.EVM.Op.returndatasize [], lit 64]]])
      [revert00]
  | .none => e

/-- Core word of a successful ABI decode. `boolOpt` is `1` on empty or nonzero
word (mirroring `boolBit <$> AbiRetType.decode`); `.none` is `0`. -/
def emitCallRetVal (ret : AbiRet) : YExpr :=
  match ret with
  | .boolOpt =>
    bop YulSemantics.EVM.Op.or
      [bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.returndatasize []],
        bop YulSemantics.EVM.Op.iszero
          [bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.mload [lit abiPtr]]]]
  | .word => bop YulSemantics.EVM.Op.mload [lit abiPtr]
  | .none => lit 0

/-- Forwarded gas argument: the `extCallGas` literal (not `gas()`). -/
def emitCallGas : YExpr := lit extCallGas

def emitExtCallOp (isView : Bool) (target : YExpr) (insize : Nat) : YExpr :=
  if isView then
    bop YulSemantics.EVM.Op.staticcall
      [emitCallGas, target, lit abiPtr, lit insize, lit abiPtr, lit 32]
  else
    bop YulSemantics.EVM.Op.call
      [emitCallGas, target, lit 0, lit abiPtr, lit insize, lit abiPtr, lit 32]

/-- Body of an external CALL/STATICCALL. Temps `{tag}__ok_*` live inside a Yul
block so `restore` drops them. When `assignResult` is set, that outer variable
is assigned the ABI Core word. -/
def emitExtCallBody (tag : String) (depth : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool)
    (assignResult : Option YIdent) : YBlock :=
  let ok := extOk tag depth
  let e := emitDo {} YulSemantics.EVM.Op.mstore
    [lit abiPtr, bop YulSemantics.EVM.Op.shl [lit 224, lit sel]]
  let (e, _) := args.foldl (fun (e, i) a =>
    (emitDo e YulSemantics.EVM.Op.mstore [lit (abiAfterSel + 32 * i), atomE tag depth a],
      i + 1)) (e, 0)
  let insize := 4 + 32 * args.length
  let e := emitLet e ok (emitExtCallOp isView (atomE tag depth target) insize)
  -- `view` + `.none` has no ABI payload and `Tx.viewAsNat .none` never fails,
  -- so a failed STATICCALL must not revert (Unit decode is total).
  let e :=
    if isView && decide (ret = .none) then e
    else emitIf e (bop YulSemantics.EVM.Op.iszero [var ok]) [revert00]
  let e := emitCallRetCheck e ret
  match assignResult with
  | none => e.stmts
  | some name => (emitAssign e name (emitCallRetVal ret)).stmts

/-- ABI-pack at `0x80`, `call(extCallGas, …)` / `staticcall(extCallGas, …)`, revert
on failure. Temps are scoped in `{ … }`. When `bindResult` is set:
`let v := 0 { … v := r }`. -/
def emitExtCall (tag : String) (e : Emit) (depth : Nat) (target : Atom) (sel : Nat)
    (args : List Atom) (ret : AbiRet) (isView : Bool)
    (bindResult : Option YIdent) : Emit :=
  match bindResult with
  | none => emitBlock e (emitExtCallBody tag depth target sel args ret isView none)
  | some name =>
    emitBlock (emitLet e name (lit 0))
      (emitExtCallBody tag depth target sel args ret isView (some name))

/-- `call(extCallGas, to, value, 0, 0, 0, 0)` — empty calldata, keep the
success bit. No `revert(0,0)`: `Tx.sendRaw` returns `Bool`. -/
def emitExtSendOp (target : YExpr) (value : YExpr) : YExpr :=
  bop YulSemantics.EVM.Op.call
    [emitCallGas, target, value, lit 0, lit 0, lit 0, lit 0]

def emitExtSendBody (tag : String) (depth : Nat) (target : Atom) (amount : Atom)
    (assignResult : Option YIdent) : YBlock :=
  let ok := extOk tag depth
  let e := emitLet {} ok (emitExtSendOp (atomE tag depth target) (atomE tag depth amount))
  match assignResult with
  | none => e.stmts
  | some name => (emitAssign e name (var ok)).stmts

def emitExtSend (tag : String) (e : Emit) (depth : Nat) (target : Atom)
    (amount : Atom) (bindResult : Option YIdent) : Emit :=
  match bindResult with
  | none => emitBlock e (emitExtSendBody tag depth target amount none)
  | some name =>
    emitBlock (emitLet e name (lit 0))
      (emitExtSendBody tag depth target amount (some name))

def emitLetOp (tag : String) (_c : ContractDef) (e : Emit) (depth : Nat) : Lsc.Op → Option Emit
  | .load f => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.sload [lit f]))
  | .loadMap f k =>
    let e := emitMapSlotPrep e f (atomE tag depth k)
    some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.sload [keccak064]))
  | .loadMap2 f k₁ k₂ =>
    let e := emitMap2SlotPrep e f (atomE tag depth k₁) (atomE tag depth k₂)
    some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.sload [keccak064]))
  | .sender => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.caller []))
  | .value => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.callvalue []))
  | .timestamp => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.timestamp []))
  | .blockNumber => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.number []))
  | .selfAddress => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.address []))
  | .selfBalance => some (emitLet e (identV tag depth) (bop YulSemantics.EVM.Op.selfbalance []))
  | .addChecked a b =>
      some (emitAddChecked e (identV tag depth) (atomE tag depth a) (atomE tag depth b))
  | .subChecked a b =>
      some (emitSubChecked e (identV tag depth) (atomE tag depth a) (atomE tag depth b))
  | .mulChecked a b =>
      some (emitMulChecked e (identV tag depth) (atomE tag depth a) (atomE tag depth b))
  | .divChecked a b =>
      some (emitDivChecked e (identV tag depth) (atomE tag depth a) (atomE tag depth b))
  | .mulDivDown a b d =>
      some (emitMulDivDown e (identV tag depth) (atomE tag depth a) (atomE tag depth b) (atomE tag depth d))
  | .mulDivUp a b d =>
      some (emitMulDivUp e (identV tag depth) (atomE tag depth a) (atomE tag depth b) (atomE tag depth d))
  | .pow10 d =>
      some (emitPow10 e (identV tag depth) (atomE tag depth d))
  | .pure a => some (emitLet e (identV tag depth) (atomE tag depth a))
  | .call t sel args ret =>
      some (emitExtCall tag e depth t sel args ret false (some (identV tag depth)))
  | .view t sel args ret =>
      some (emitExtCall tag e depth t sel args ret true (some (identV tag depth)))
  | .send t amt =>
      some (emitExtSend tag e depth t amt (some (identV tag depth)))

def emitPrim (tag : String) (depth : Nat) (p : Prim) (args : List Atom) : YExpr :=
  match p, args with
  | .id, [a] => atomE tag depth a
  | .addWrap, [a, b] => bop YulSemantics.EVM.Op.add [atomE tag depth a, atomE tag depth b]
  | .subWrap, [a, b] => bop YulSemantics.EVM.Op.sub [atomE tag depth a, atomE tag depth b]
  | .mulWrap, [a, b] => bop YulSemantics.EVM.Op.mul [atomE tag depth a, atomE tag depth b]
  | _, _ => lit 0

def emitCond (tag : String) (depth : Nat) : Cond → YExpr
  | .lt a b => bop YulSemantics.EVM.Op.lt [atomE tag depth a, atomE tag depth b]
  | .le a b =>
    bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.lt [atomE tag depth b, atomE tag depth a]]
  | .eq a b => bop YulSemantics.EVM.Op.eq [atomE tag depth a, atomE tag depth b]
  | .ne a b =>
    bop YulSemantics.EVM.Op.iszero [bop YulSemantics.EVM.Op.eq [atomE tag depth a, atomE tag depth b]]
  | .and c d => bop YulSemantics.EVM.Op.and [emitCond tag depth c, emitCond tag depth d]
  | .or c d => bop YulSemantics.EVM.Op.or [emitCond tag depth c, emitCond tag depth d]
  | .not c => bop YulSemantics.EVM.Op.iszero [emitCond tag depth c]
  | .tt => lit 1
  | .ff => lit 0

def emitStmt (tag : String) (c : ContractDef) (e : Emit) (depth : Nat) : Lsc.Stmt → Emit
  | .store f v => emitDo e YulSemantics.EVM.Op.sstore [lit f, atomE tag depth v]
  | .storeMap f k v =>
    let e := emitMapSlotPrep e f (atomE tag depth k)
    emitDo e YulSemantics.EVM.Op.sstore [keccak064, atomE tag depth v]
  | .storeMap2 f k₁ k₂ v =>
    let e := emitMap2SlotPrep e f (atomE tag depth k₁) (atomE tag depth k₂)
    emitDo e YulSemantics.EVM.Op.sstore [keccak064, atomE tag depth v]
  | .require cond err args =>
    emitIf e (bop YulSemantics.EVM.Op.iszero [emitCond tag depth cond])
      (emitCustomError c {} err (args.map (atomE tag depth))).stmts
  | .emit ev args =>
    let topic :=
      match c.events[ev]? with
      | some ed => ed.topic0
      | none => 0
    emitLog1 e topic (args.map (atomE tag depth))
  | .revert err args =>
    emitCustomError c e err (args.map (atomE tag depth))
  | .call t sel args ret =>
    emitExtCall tag e depth t sel args ret false none
  | .view t sel args ret =>
    emitExtCall tag e depth t sel args ret true none

def emitRet (tag : String) (e : Emit) (depth : Nat) (haltUnit : Bool)
    {t : RetTy} (r : RetExpr t) (clearLock : Bool := false) : Emit :=
  let e := if clearLock then emitLockClear e else e
  match r with
  | .unit => emitReturnUnit e haltUnit
  | _ => emitReturnWords e ((retAtoms r).map (atomE tag depth))

/-- Inner block of a word-like `seqIf`: `let phi := 0; switch; dest := phi`. -/
def seqIfWordInner (tag : String) (d : Nat) (cond : Cond)
    (eA eB : Emit) : YBlock :=
  (emitAssign
    ((emitLet {} (identPhi tag d) (lit 0)).push
      (.switch (emitCond tag d cond)
        [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))
    (identV tag d) (var (identPhi tag d))).stmts

/-- `let dest := 0 { seqIfWordInner }` so restore drops `phi` and keeps `dest`. -/
def emitSeqIfWord (tag : String) (e : Emit) (d : Nat) (cond : Cond)
    (eA eB : Emit) : Emit :=
  emitBlock (emitLet e (identV tag d) (lit 0)) (seqIfWordInner tag d cond eA eB)

def emitAssignRet (tag : String) (e : Emit) (depth : Nat) (dest : YIdent)
    {t : RetTy} (r : RetExpr t) : Option Emit :=
  match r with
  | .word a | .addr a | .flag a => some (emitAssign e dest (atomE tag depth a))
  | .unit | .pair _ _ => some e

mutual
def emitCore (tag : String) (c : ContractDef) (e : Emit) (depth : Nat)
    (haltUnit : Bool) {t : RetTy} (core : Core t) (clearLock : Bool := false) :
    Option Emit :=
  match core with
  | .ret r => some (emitRet tag e depth haltUnit r clearLock)
  | .opTail op => do
      let e ← emitLetOp tag c e depth op
      some (emitRet tag e (depth + 1) haltUnit (.word (.var 0)) clearLock)
  | .opTailAddr op => do
      let e ← emitLetOp tag c e depth op
      some (emitRet tag e (depth + 1) haltUnit (.addr (.var 0)) clearLock)
  | .opTailFlag op => do
      let e ← emitLetOp tag c e depth op
      some (emitRet tag e (depth + 1) haltUnit (.flag (.var 0)) clearLock)
  | .stmtTail s =>
      let e := emitStmt tag c e depth s
      some (emitReturnUnit (if clearLock then emitLockClear e else e) haltUnit)
  | .revertTail err args => some (emitCustomError c e err (args.map (atomE tag depth)))
  | .letOp op k => do
      let e ← emitLetOp tag c e depth op
      emitCore tag c e (depth + 1) haltUnit k clearLock
  | .seq s k => emitCore tag c (emitStmt tag c e depth s) depth haltUnit k clearLock
  | .letPure p args k =>
      emitCore tag c (emitLet e (identV tag depth) (emitPrim tag depth p args))
        (depth + 1) haltUnit k clearLock
  | .ite cond a b => do
      let eA ← emitCore tag c {} depth haltUnit a clearLock
      let eB ← emitCore tag c {} depth haltUnit b clearLock
      some (e.push (.switch (emitCond tag depth cond)
        [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))
  | .seqIf (t := tBr) cond th el k =>
    match tBr with
    | .unit => do
        let eA ← emitCore tag c {} depth false th false
        let eB ← emitCore tag c {} depth false el false
        emitCore tag c (e.push (.switch (emitCond tag depth cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))
          depth haltUnit k clearLock
    | .word | .addr | .flag => do
        let eA ← emitCoreToVar tag c {} depth (identPhi tag depth) th
        let eB ← emitCoreToVar tag c {} depth (identPhi tag depth) el
        emitCore tag c (emitSeqIfWord tag e depth cond eA eB)
          (depth + 1) haltUnit k clearLock
    | .pair _ _ => some e

/-- Compile `core` as statements that assign `dest` and fall through. -/
def emitCoreToVar (tag : String) (c : ContractDef) (e : Emit) (depth : Nat)
    (dest : YIdent) {t : RetTy} (core : Core t) : Option Emit :=
  match core with
  | .ret r => emitAssignRet tag e depth dest r
  | .opTail op => do
      let e ← emitLetOp tag c e depth op
      some (emitAssign e dest (var (identV tag depth)))
  | .opTailAddr op => do
      let e ← emitLetOp tag c e depth op
      some (emitAssign e dest (var (identV tag depth)))
  | .opTailFlag op => do
      let e ← emitLetOp tag c e depth op
      some (emitAssign e dest (var (identV tag depth)))
  | .stmtTail s => some (emitStmt tag c e depth s)
  | .revertTail err args =>
      some (emitCustomError c e err (args.map (atomE tag depth)))
  | .letOp op k => do
      let e ← emitLetOp tag c e depth op
      emitCoreToVar tag c e (depth + 1) dest k
  | .seq s k => emitCoreToVar tag c (emitStmt tag c e depth s) depth dest k
  | .letPure p args k =>
      emitCoreToVar tag c (emitLet e (identV tag depth) (emitPrim tag depth p args))
        (depth + 1) dest k
  | .ite cond a b => do
      let eA ← emitCoreToVar tag c {} depth dest a
      let eB ← emitCoreToVar tag c {} depth dest b
      some (e.push (.switch (emitCond tag depth cond)
        [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))
  | .seqIf (t := tBr) cond th el k =>
    match tBr with
    | .unit => do
        let eA ← emitCoreToVar tag c {} depth dest th
        let eB ← emitCoreToVar tag c {} depth dest el
        emitCoreToVar tag c (e.push (.switch (emitCond tag depth cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)))
          depth dest k
    | .word | .addr | .flag => do
        let eA ← emitCoreToVar tag c {} depth (identPhi tag depth) th
        let eB ← emitCoreToVar tag c {} depth (identPhi tag depth) el
        emitCoreToVar tag c (emitSeqIfWord tag e depth cond eA eB)
          (depth + 1) dest k
    | .pair _ _ => some e
end

end IdentV

/-- Compile one **runtime** function. Parameters are ABI-decoded from calldata
(`offset = 4`). Locals are `{f.name}_{i}`. The constructor branch of this
definition is unused by `deployObject` (see `toYulCtor`); it is kept so existing
`toYulFn_inv` unfolds are stable. -/
def toYulFn (c : ContractDef) (f : FnDef) : Option YBlock :=
  if !coreWF c f.core then none
  else if !identsNodup f.name (maxDepth f) then none
  else
    let offset := if f.kind = .constructor then 0 else 4
    let haltUnit := f.kind ≠ .constructor
    let e := emitParams f.name {} offset f.params.length
    (emitCore f.name c e f.params.length haltUnit f.core (locks f)).map Emit.stmts

/-- Compile a constructor: args from the init-code suffix (`emitCtorParams`), unit
`ret` falls through (no `stop()`), so `deployObject` can append `constructorCode`. -/
def toYulCtor (c : ContractDef) (f : FnDef) : Option YBlock :=
  if !coreWF c f.core then none
  else if !identsNodup f.name (maxDepth f) then none
  else
    (emitCore f.name c (emitCtorParams f.name {} f.params.length)
      f.params.length false f.core).map
      Emit.stmts

/-- `if lt(calldatasize(), 4+32n) { revert(0,0) }`, then
`if callvalue() { revert(0,0) }` when `¬f.payable`, then `tstore(0,1)`
when `locks f`, then the function body. Payable non-locking cases stay
two blocks. -/
def entryCase (c : ContractDef) (f : FnDef) : Option (YulSemantics.Literal × YBlock) := do
  let body ← toYulFn c f
  let min := 4 + 32 * f.params.length
  let guard := (emitGuardLt {} min).stmts
  some (YulSemantics.Literal.number f.selector,
    YulSemantics.Stmt.block guard ::
      (valueCheckPrefix f ++ (lockSetPrefix f ++ [YulSemantics.Stmt.block body])))

/-- Discarded `memoryguard(k)` marker (`if memoryguard(k) {}`). powdr collects
any `.call "memoryguard" [lit k]`; the dialect has no `pop`, and a truthiness
test of the literal does not write memory, so erase (`k`) and resolve
(`reserved`) leave the same machine state. -/
def memoryGuardStmt : YStmt :=
  .cond (YulSemantics.Expr.call "memoryguard" [lit memoryGuardK]) []

/-- `memoryguard(k)` erased to `if k {}` (256 ≠ 0, empty body). -/
def memoryGuardErased : YStmt :=
  .cond (lit memoryGuardK) []

/-- Dispatcher + every non-constructor function. Size-check is its own block; the
selector is a nested expression so it does not occupy a live stack slot in the cases.
The leading `memoryguard` is a compile-time marker for powdr spilling; Core→Yul
(`toYulFn`) does not emit it. The lock check sits after the marker and before the
calldata-size guard so every selector, including `default`, sees it. -/
def runtimeBlock (c : ContractDef) : Option YBlock :=
  if !selectorsNodup c then none
  else do
    let cases ← c.functions.mapM (entryCase c)
    let guard := (emitGuardLt {} 4).stmts
    let sel := bop YulSemantics.EVM.Op.shr
      [lit 224, bop YulSemantics.EVM.Op.calldataload [lit 0]]
    some (memoryGuardStmt ::
      lockCheckStmt ::
      [YulSemantics.Stmt.block guard,
        YulSemantics.Stmt.switch sel cases (some [revert00])])

/-- Constructor body (if any) followed by `constructorCode "runtime"`. -/
def deployCtorBlock (c : ContractDef) : Option YBlock :=
  match c.ctor with
  | none => some (constructorCode "runtime")
  | some f => (toYulCtor c f).map (fun body => body ++ constructorCode "runtime")

/-- Deploy object: ctor body (if any), then `constructorCode "runtime"`, with
compiled runtime bytes as `data "runtime"` (not a nested object). CREATE
therefore installs exactly `compileRuntime` — see `deploy_installs_runtime`. -/
def deployObject (c : ContractDef) (rt : List UInt8) : Option YObject :=
  (deployCtorBlock c).map fun ctor =>
    YulSemantics.Object.mk c.name ctor []
      [("runtime", YulSemantics.Data.hex rt)]

/-- Pretty-printer (powdr's `EVM.print`); feed to `solc --strict-assembly`. -/
def printYul (b : YBlock) : String :=
  YulSemantics.EVM.print (b : YulSemantics.Block YulSemantics.EVM.Op)

def printYulObject (o : YObject) : String :=
  YulSemantics.EVM.printObject (o : YulSemantics.Object YulSemantics.EVM.Op)

end Lsc.Compiler
