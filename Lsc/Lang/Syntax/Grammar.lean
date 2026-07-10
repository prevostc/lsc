import Lsc.Lang.AST
import Lsc.Lang.TxM
import Lsc.Lang.Derive
import Lsc.Lib.Interfaces.IERC20
import Lean

/-!
# `lscExpr`/`lscStmt`: the `tx { ... }` grammar

The contract-author surface: a fresh `lscExpr` expression category plus `lscStmt` statement
productions (assignment, `require`/`revert`, `emit`, `if`/`else`, `let`), elaborated directly
into `Lsc.Stmt`/`Lsc.Expr` values. Reuses `Lang/Derive.lean`'s `FieldKind`/
`getStructureFieldKinds`/`elabErrorCtorName`/`getCtorFieldKind` machinery rather than
reimplementing it. See `docs/decisions/0001-txm-superseded-by-syntax.md` for why this grammar
exists instead of extending `TxM.lean`'s `do`-notation surface.

Implementation is split across `Lsc/Lang/Syntax/` modules; import `Lsc.Lang.Syntax` for the full surface.

A few mechanisms worth knowing when reading the elaborators:

- **`σ.field`** is not its own grammar production: Lean's lexer already tokenises the dotted
  identifier as one compound `Name`, so a single `ident` production in `lscExpr` covers plain
  local names, `σ.field`, and `msg.sender` alike; `elabLscExpr` dispatches on the parsed
  `Name`'s shape and resolves `σ.field`'s storage `Ty` via `Lsc.Deriving.getStructureFieldKinds`
  against the contract's real storage `structure`.
- **`let x = e;`** is implemented directly (not deferred behind a typeclass): the elaborator
  threads an explicit `locals : List (String × FieldKind)` association list through statement
  elaboration by hand, so every node's `FieldKind` is a static lookup. `let n = σ.number +? 1;`
  emits one `Stmt.letBind`; later references to `n` resolve to an `Expr.var`, not a re-evaluated
  `storageGet` — same once-evaluated semantics as `TxM.lean`'s `letWei`/`var`, without needing
  its typeclass dispatch.
- **`+?`/`-?`** pattern-match directly on the already-known left/right `FieldKind`s (no
  typeclass needed, unlike `TxM.lean`'s `WeiAddChecked`). A bare-`Nat` right-hand side (e.g.
  `σ.number +? 1`) is detected syntactically (`lscExprAsNatLit?`) before elaboration.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

/-! ## Syntax categories -/

/-- Fresh, inert-everywhere-else expression category. Nothing outside an explicit
`tx { ... }` delimiter (via `lscStmt`, below) ever parses into `lscExpr`. -/
declare_syntax_cat lscExpr

/-- Local/bound identifiers, `σ.field` storage reads, and `msg.sender` all lex as a single
(possibly dotted) `ident` token — dispatched by `Name` shape in `elabLscExpr`, not split into
separate grammar productions (see module docstring). -/
syntax:max (name := lscExprIdent) ident : lscExpr

/-- Numeric literal. Defaults to `Ty.uint256`-kind unless consumed directly by `+?`/`-?`'s
bare-`Nat` `Wei.Expr.addCheckedNat`/`.lit` handling (see `lscExprAsNatLit?`). -/
syntax:max (name := lscExprNum) num : lscExpr

/-- Boolean literal. Using plain `"true"`/`"false"` as fresh `syntax` atoms (even via
`declare_syntax_cat`-scoped rules) was verified to break their pre-existing meaning as Lean's
builtin `Bool` literal terms *everywhere else in the file* (e.g. `paused : Bool := false` in a
plain `structure` stops parsing with `unexpected token 'false'; expected term`) — `Lean.Parser
.nonReservedSymbol` is the standard fix for exactly this token-table collision: it registers
`"true"`/`"false"` as *non-reserved* symbols usable as `lscExpr` leading tokens without
shadowing/reserving them for every other parser category, so the builtin `Bool` term notation
keeps working unchanged elsewhere in this same file. -/
syntax:max (name := lscExprTrue) &"true" : lscExpr
syntax:max (name := lscExprFalse) &"false" : lscExpr

syntax:max (name := lscExprMsgSender) "msg.sender" : lscExpr

/-- `σ.field[key]` — read one entry of a `Lsc.Mapping` storage field (e.g.
`σ.balances[to]`), where `key` is `msg.sender` or a bare local identifier (a `tx` parameter or
`let`-bound `Address` value) — see `Lsc.MapKey`'s docstring for why only these two forms are
supported. `σ.field` itself lexes as one dotted `ident` token (see this file's module
docstring), so this production is `ident "[" (ident | "msg.sender") "]"`. -/
syntax:max (name := lscExprMapGet) ident "[" lscExpr "]" : lscExpr

syntax:max (name := lscExprParen) "(" lscExpr ")" : lscExpr

/-- Boolean negation, binds tighter than `==`/`+?`/`-?`. -/
syntax:75 (name := lscExprNot) "!" lscExpr:75 : lscExpr

/-- Checked addition (`Wei`-kind or `Wad`-kind only), left-associative. -/
syntax:65 (name := lscExprAdd) lscExpr:65 " +? " lscExpr:66 : lscExpr

/-- Checked subtraction (`Wei`-kind or `Wad`-kind only), left-associative. -/
syntax:65 (name := lscExprSub) lscExpr:65 " -? " lscExpr:66 : lscExpr

/-- Checked, half-up-rounding `Wad` multiplication (`Wad.mulHalfUpChecked`), left-associative.
Surface syntax per `docs/reference/AMM.md`. -/
syntax:65 (name := lscExprMul) lscExpr:65 " ⸢*⸣? " lscExpr:66 : lscExpr

/-- Checked, round-down `Wad` division (`Wad.divDownChecked`), left-associative. Surface syntax
per `docs/reference/AMM.md`. -/
syntax:65 (name := lscExprDiv) lscExpr:65 " ⌊/⌋? " lscExpr:66 : lscExpr

/-- Equality (any matching non-`Wei`/`Wad` kind). -/
syntax:50 (name := lscExprEq) lscExpr:51 " == " lscExpr:51 : lscExpr

/-- Fresh, inert-everywhere-else statement category (unchanged from the prototype, extended
with the new productions below). -/
declare_syntax_cat lscStmt

/-- `require(cond) else revert ErrCtor();` — `cond` is a real `lscExpr`; `ErrCtor` is resolved
against the contract's real `Err` inductive. Parens around `cond` (Solidity's `require(condition,
"reason")` convention), `else` (Swift's `guard cond else { ... }` precedent), and the
call-style `ErrCtor()` (matching Solidity's actual custom-error `revert Ctor();` syntax,
0.8.4+) — see the migration plan for the full rationale. -/
syntax (name := lscRequire) "require" "(" lscExpr ")" " else " "revert " ident "(" ")" ";" : lscStmt

/-- `revert ErrCtor();` — mirrors `require`'s error-resolution logic; call-style to match
Solidity's custom-error `revert Ctor();` syntax. -/
syntax (name := lscRevert) "revert " ident "(" ")" ";" : lscStmt

/-- `emit Ctor();` — 0-argument event, call-style for consistency with `emit Ctor(arg);`. -/
syntax (name := lscEmit0) "emit " ident "(" ")" ";" : lscStmt

/-- `emit Ctor(arg);` — 1-argument event. -/
syntax (name := lscEmit1) "emit " ident "(" lscExpr ")" ";" : lscStmt

/-- `σ.field = e;` — storage assignment. The left-hand side is a plain `ident` (see the
module docstring on why `σ.field` needs no dedicated production); a non-`σ.field` left-hand
side is a clear elaboration-time error, not a silent misparse. -/
syntax (name := lscAssign) ident " = " lscExpr ";" : lscStmt

/-- `σ.field[key] = e;` — write one entry of a `Lsc.Mapping` storage field
(e.g. `σ.balances[to] = newBalance;`) — see `lscExprMapGet`'s docstring for `key`'s two
supported forms. -/
syntax (name := lscMapAssign) ident "[" lscExpr "]" " = " lscExpr ";" : lscStmt

/-- `σ.field[key] +=? e;` — checked-add-and-write sugar for
`σ.field[key] = σ.field[key] +? e;` (e.g. `σ.balances[recipient] +=? amount;`, `docs/reference/
TOKEN.md`). Only ever `Wad`-kind, since a mapping field's value kind is always `Wad`
(`lscExprMapGet`'s docstring). -/
syntax (name := lscMapAssignAdd) ident "[" lscExpr "]" " +=? " lscExpr ";" : lscStmt

/-- `σ.field[key] -=? e;` — checked-sub-and-write sugar for
`σ.field[key] = σ.field[key] -? e;`, the subtraction counterpart of `lscMapAssignAdd`. -/
syntax (name := lscMapAssignSub) ident "[" lscExpr "]" " -=? " lscExpr ";" : lscStmt

/-- `σ.field +=? e;` — checked-add-and-write sugar for `σ.field = σ.field +? e;`, for a plain
(non-mapping) `Wei`- or `Wad`-kind storage field (e.g. `σ.totalSupply +=? amount;`). -/
syntax (name := lscAssignAdd) ident " +=? " lscExpr ";" : lscStmt

/-- `σ.field -=? e;` — checked-sub-and-write sugar for `σ.field = σ.field -? e;`, the
subtraction counterpart of `lscAssignAdd`. -/
syntax (name := lscAssignSub) ident " -=? " lscExpr ";" : lscStmt

/-- `let x = e;` — evaluate-once local binding (see module docstring's "`let x = e;`" section,
same semantics, Rust-shaped spelling: `let` keyword + plain `=`, chosen over `:=` since the
binding reads naturally either way and this isn't competing with `Eq`/`doReassign` the way
`TxM.lean`'s old `do`-notation attempts were). -/
syntax (name := lscLetBind) "let " ident " = " lscExpr ";" : lscStmt

/-- `let ok = exec Target.fn(args);` — bind one return word from a mutating interface call. -/
syntax (name := lscLetExec) "let " ident " = " "exec " ident " ( " ident,* " ) " ";" : lscStmt

/-- `if (cond) { ... } else { ... }`. -/
syntax (name := lscIfElse) "if" "(" lscExpr ")" "{" lscStmt* "}" "else" "{" lscStmt* "}" : lscStmt

/-- `if (cond) { ... }` — no-`else` form, compiles to `Stmt.ifThenElse cond thn Stmt.skip`. -/
syntax (name := lscIf) "if" "(" lscExpr ")" "{" lscStmt* "}" : lscStmt

/-- `return e;` — only ever valid inside a `view` function body (see `Lsc.Stmt.ret`'s docstring
in `Lang/AST.lean`); elaborating one inside an ordinary `tx` body is not itself a parse error
(`lscStmt` is one shared grammar), but `Checks.checkViewPurity`/`checkViewReturns` are only ever
run against `.view`-kind `FunctionDef`s, so a stray `return` inside a `tx` would silently compile
to a `Stmt.ret` node that `Stmt.eval`'s public entry point (`Eval.lean`) simply discards the
returned value of — harmless, but not a construct `tx` authors have any reason to reach for.
The `view` elaborator below is the only place that ever emits this node from surface syntax. -/
syntax (name := lscReturn) "return " lscExpr ";" : lscStmt

/-- `exec Target.fn(arg1, arg2);` / `read Target.fn(arg1, arg2);` — black-box cross-contract
invocations into a specific, statically-named other contract. `exec` is state-mutating; `read`
discards the callee's resulting state/log changes. Both elaborate to visible `Stmt` nodes
(`externalExec` / `externalRead`) that lower to checked `CALL` / `STATICCALL` in IR/Yul.
See `Lsc.ContractM.PairM.exec`/`PairM.read` (`Core/ContractM.lean`) for the proof-layer
semantics and `docs/decisions/0003-exec-read-black-box.md` for why they're black box;
`examples/escrow/src/Escrow.lean` has a real `exec` usage.

`Target.fn` is a single dotted identifier naming the callee's tx-derived function directly (e.g.
`Token.transfer`). Arguments must be plain identifiers — real Lean values (`tx` params or
in-scope contract-local `def`s), not arbitrary `lscExpr` sub-expressions like `amount +? 1` —
since the callee expects real Lean values, not this contract's own AST.

**`exec` txs** also emit a `PairM` Lean `def` (for `examples/escrow/test/EscrowProofs.lean`)
alongside the `Stmt` body in `ContractDef` (`flushContractTxs`). `@nonreentrant` is required
immediately by `tx`'s own elaborator on any body containing top-level `exec` (not `read` alone);
it desugars to `Stmt.reentrancyGuard`, which `Checks.checkNonReentrant` also enforces. -/
syntax (name := lscExec) "exec " ident " ( " ident,* " ) " ";" : lscStmt

/-- See `lscExec`'s docstring — the read-only counterpart. -/
syntax (name := lscRead) "read " ident " ( " ident,* " ) " ";" : lscStmt

end Lsc.Syntax
