import Lsc.Types

namespace Lsc.Compile.IR

/-- Flat IR: storage slots resolved, linear types erased. -/
inductive Expr where
  | lit : Nat → Expr
  | local : Ident → Expr
  | sload : Nat → Expr
  /-- `keccak256(abi.encode(key, baseSlot))` — Solidity mapping slot. -/
  | mapSlot : Nat → Expr → Expr
  /-- `keccak256(abi.encode(key2, keccak256(abi.encode(key1, baseSlot))))` — Solidity's real
      nested-mapping slot formula (e.g. `allowances[owner][spender]`), applying `mapSlot`'s own
      single-key hash twice: the inner hash's result becomes the outer hash's `baseSlot`. -/
  | mapSlot2 : Nat → Expr → Expr → Expr
  /-- `sload` at a computed slot (mapping entries). -/
  | dynSload : Expr → Expr
  /-- Read the 32-byte ABI word at byte offset `offset` in `msg.data`. -/
  | calldataWord : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  | isZero : Expr → Expr
  | gt : Expr → Expr → Expr
  | shr : Expr → Expr → Expr
  | xor : Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Compiler-reserved EIP-1153 transient-storage key for the reentrancy lock. -/
def reentrancyLockSlot : Nat := 0

inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → Expr → Stmt
  | sstore : Nat → Expr → Stmt
  /-- `sstore` at a computed slot (mapping entries). -/
  | sstoreDyn : Expr → Expr → Stmt
  | ifRevertSelector : Expr → Nat → Stmt
  /-- `LOG1` with topic0 `topic` and `datas.length` contiguous 32-byte ABI words in memory
  (offsets `0`, `32`, …). Empty `datas` emits zero data bytes. -/
  | log : Nat → List Expr → Stmt
  | revertSelector : Nat → Stmt
  /-- `return e;` (`view` functions only, `Lang/AST.lean`'s `Stmt.ret`) — ABI-encodes `e`'s
      single 32-byte-word value into memory and halts with `RETURN (`Bytecode/Codegen.lean`'s
      `.ret` case). Every supported `Ty` (`uint256`/`bool`/`address`/`wei`/`wad`) is exactly one
      32-byte word wide, so no length-prefix/dynamic-ABI encoding is needed. -/
  | ret : Expr → Stmt
  /-- `Stmt.reentrancyGuard` lowering — check the transient lock; revert if already held. -/
  | checkReentrancyLock (reentrantSelector : Nat) : Stmt
  /-- Set the transient reentrancy lock (`held = true` → `TSTORE 1`, `false` → `TSTORE 0`). -/
  | setReentrancyLock (held : Bool) : Stmt
  /-- A real EVM `CALL` with mandatory success check — no unchecked `CALL` exists in this IR.
      `addr`/`selector`/`args` identify the callee; calldata is ABI-packed into memory at offset 0.
      `checkBoolReturn` optionally decodes the returned word as `bool` (ERC20 convention).
      `failSelector` is the custom-error selector emitted on CALL failure or bool-check failure. -/
  | externalCall (addr : Expr) (selector : Nat) (args : List Expr) (checkBoolReturn : Bool)
      (failSelector : Nat) : Stmt
  /-- `CALL` that copies the first 32-byte return word into `bindName` (no bool-revert guard). -/
  | externalCallBind (addr : Expr) (selector : Nat) (args : List Expr) (bindName : Ident)
      (failSelector : Nat) : Stmt
  /-- A real EVM `STATICCALL` with mandatory success check — read-only; no reentrancy lock.
      `retWords` is the number of 32-byte return words to copy (0 = discard returndata). -/
  | staticCall (addr : Expr) (selector : Nat) (args : List Expr) (retWords : Nat)
      (failSelector : Nat) : Stmt
  /-- `STATICCALL` that binds the first return word into `bindName`. -/
  | staticCallBind (addr : Expr) (selector : Nat) (args : List Expr) (bindName : Ident)
      (failSelector : Nat) : Stmt
  deriving Repr, DecidableEq

end Lsc.Compile.IR
