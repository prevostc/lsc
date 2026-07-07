import Lsc.Prelude
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lang.Syntax

open Lsc Lsc.Compile
open Lsc.Deriving

/-!
# `Token` — a real, generic ERC20-shaped token

Unlike the earlier "two-party ledger" cut of this contract (`holderBalance`/`escrowBalance`,
`transferToEscrow`/`transferFromEscrow` — `Escrow`-specific, not a real token at all), `Token`
now holds a genuine address-keyed balance mapping (`Lsc.Wad.WadMap`, `Lib/Wad/Syntax.lean`) and
exposes the real ERC20 surface: `balanceOf`, `transfer`, and an owner-gated `mint`. It knows
nothing about `Escrow` (or any other caller) at all — any contract wanting to move `Token`
balances does so via a black-box `exec`/`read` cross-contract call (`Lang/Syntax.lean`), exactly
like a real, composable ERC20 would be called from Solidity.

**Scope limitation, documented (see `docs/reference/TOKEN.md`):** `approve`/`transferFrom` (the
allowance half of ERC20) need a *double*-keyed mapping (`address → address → Wad`), which is out
of scope for this pass — `Lsc.Wad.WadMap` only supports a single `Address` key (see that type's
docstring). Shipping `balanceOf`/`transfer`/`mint` as the real ERC20 core, with
`approve`/`transferFrom` tracked as a documented follow-up (`TODO.md`), is the explicit fallback
the migration plan allows for this case. -/

namespace Token

-- `Token`'s own declared unit — `Lsc.Wad.Fixed 18 Tag`, where `Tag` is a fresh, uninhabited
-- nominal marker generated just for `Token` (`declare_token_amount`, `Lsc/Lib/Wad/Syntax.lean`).
-- Named separately from the generic `Wad` purely so any caller moving `Token` balances (e.g.
-- `Escrow.release`, below) can reference *this token's own unit* rather than the generic
-- fixed-point math type — and, unlike a plain `abbrev Amount := Wad`, this is a **genuinely
-- different Lean type** from every other token's own `Amount`, even one with the exact same `18`
-- decimals: passing one where the other is expected (at the one place that matters, an `exec`/
-- `read` cross-contract call site) is a compile error, not a silent "which token is this really
-- for" bug. A future token declared with a genuinely different decimals count (e.g. a 6-decimals,
-- USDC-shaped token) would additionally get a different `Fixed d`, compounding both protections
-- (see `Lsc.Wad.Fixed`'s docstring and `Fixed.convert` for the one sanctioned, explicit way to
-- cross between two different decimals of the *same* token). Only `Fixed 18`-shaped aliases are
-- accepted by this DSL's `tx`/storage-field grammar today (see `Lsc.Deriving.fieldKindOfExpr`'s
-- docstring) — a genuinely different-decimals token needs to be authored as a hand-written
-- `ContractM` contract instead, tracked as a follow-up in `TODO.md`.
declare_token_amount Amount

structure TokenStorage where
  owner : Address := 0
  totalSupply : Amount := ⟨0⟩
  /-- Per-holder balances — every address reads as `0` until written (see `Wad.WadMap`'s
      docstring: a total function, not a partial map, exactly like real EVM storage). -/
  balances : Wad.WadMap := fun _ => ⟨0⟩
  deriving ContractStorage

inductive TokenError where
  | Overflow
  | Underflow
  | NotOwner
  deriving Repr, DecidableEq, ContractError

/-- Event payloads are limited to `Ty`'s five DSL-level kinds, 0-or-1 arguments each (see
`Lang/Derive.lean`'s `getCtorFieldKind`) — the real ERC20 `Transfer(from, to, amount)`/
`Mint(to, amount)` (2-3 args) don't fit that yet, so these carry only `amount` for now
(documented limitation, `docs/reference/TOKEN.md`; widening event payloads to more than one
field is tracked as a follow-up in `TODO.md`). -/
inductive TokenEvent where
  | Transfer (amount : Amount)
  | Mint (amount : Amount)
  deriving Repr, DecidableEq, ContractEvent

derive_contract_dsl TokenStorage TokenError TokenEvent

-- `balanceOf(who)` — a read-only query, declared with the `view` DSL grammar
-- (`Lang/Syntax.lean`) rather than hand-written `ContractM`: `view`'s generated `balanceOf`
-- is exactly the shape `PairM.read`'s callee argument expects (`Lsc/Core/ContractM.lean`), so
-- `read Token.balanceOf(who);` (from another contract) works directly. Never reverts: every
-- address has some balance (`0` if never written), matching `Wad.WadMap`'s total-function
-- model — `σ.balances[who]` alone, with no `require`, already reflects that.
view balanceOf(who : Address) : Amount => σ.balances[who];

-- `transfer(to, amount)` — the real ERC20 transfer: checked-subtract from the caller
-- (`msg.sender`)'s own balance, checked-add to `to`'s. The checked `-?`/`+?` ops themselves
-- enforce "can't transfer more than you have" (raises `Underflow`) — no separate `require`
-- needed (this grammar has no `>=`/`<=` yet, only `==`).
tx transfer(recipient : Address, amount : Amount) {
  σ.balances[msg.sender] -=? amount;
  σ.balances[recipient] +=? amount;
  emit Transfer(amount);
}

-- `mint(to, amount)` — owner-gated issuance (no real ERC20 standardizes minting access
-- control, but every practical token needs *some* way to bring supply into existence; gating on
-- a fixed `owner`, exactly like `Counter`'s `pause`/`unpause`, is the simplest faithful choice).
tx mint(recipient : Address, amount : Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  σ.totalSupply +=? amount;
  σ.balances[recipient] +=? amount;
  emit Mint(amount);
}

/-! ## DSL wiring + compilation: `ContractDef` + Yul/bytecode emission -/

derive_contract_def "Token" TokenStorage TokenError TokenEvent

-- Smoke-checks
#check Token.TokenStorage
#check Token.TokenError
#check Token.TokenEvent
#check Token.TokenM
#check (Token.balanceOf : Address → TokenM (Val Ty.wad))
#check (Token.transfer : Address → Wad → Stmt)
#check (Token.mint : Address → Wad → Stmt)
#check Token.contractDef
#check Token.bytecodeHex
#check Token.deployHex

end Token
