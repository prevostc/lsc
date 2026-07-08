import Lsc.Types

namespace Lsc.Compile.IR

/-- Flat IR: storage slots resolved, linear types erased. -/
inductive Expr where
  | lit : Nat → Expr
  | local : Ident → Expr
  | sload : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  | isZero : Expr → Expr
  deriving Repr

/-- Compiler-reserved EIP-1153 transient-storage key for the reentrancy lock. -/
def reentrancyLockSlot : Nat := 0

inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → Expr → Stmt
  | sstore : Nat → Expr → Stmt
  | ifRevert : Expr → Stmt
  | log0 : Nat → Stmt
  | log1 : Nat → Expr → Stmt
  | revert0 : Stmt
  /-- `return e;` (`view` functions only, `Lang/AST.lean`'s `Stmt.ret`) — ABI-encodes `e`'s
      single 32-byte-word value into memory and halts with `RETURN (`Bytecode/Codegen.lean`'s
      `.ret` case). Every supported `Ty` (`uint256`/`bool`/`address`/`wei`/`wad`) is exactly one
      32-byte word wide, so no length-prefix/dynamic-ABI encoding is needed. -/
  | ret : Expr → Stmt
  /-- `Stmt.reentrancyGuard` lowering — check the transient lock; revert if already held. -/
  | checkReentrancyLock : Stmt
  /-- Set the transient reentrancy lock (`held = true` → `TSTORE 1`, `false` → `TSTORE 0`). -/
  | setReentrancyLock (held : Bool) : Stmt
  /-- A real EVM `CALL` with mandatory success check — no unchecked `CALL` exists in this IR.
      `addr`/`selector`/`args` identify the callee; calldata is ABI-packed into memory at offset 0.
      `checkBoolReturn` optionally decodes the returned word as `bool` (ERC20 convention). -/
  | externalCall (addr : Expr) (selector : Nat) (args : List Expr) (checkBoolReturn : Bool) : Stmt
  /-- A real EVM `STATICCALL` with mandatory success check — read-only; no reentrancy lock.
      `retWords` is the number of 32-byte return words to copy (0 = discard returndata). -/
  | staticCall (addr : Expr) (selector : Nat) (args : List Expr) (retWords : Nat) : Stmt
  deriving Repr

end Lsc.Compile.IR
