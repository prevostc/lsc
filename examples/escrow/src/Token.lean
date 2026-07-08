import Lsc.Prelude
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lang.Syntax

open Lsc Lsc.Compile
open Lsc.Deriving

/-!
# `Token` — a generic ERC20-shaped token

An address-keyed balance mapping (`Wad.WadMap`) with `balanceOf`, `transfer`, and an
owner-gated `mint`. `Token` knows nothing about `Escrow` or any other caller — any contract
moves `Token` balances via a black-box `exec`/`read` cross-contract call
(see [`docs/reference/TOKEN.md`](../../../docs/reference/TOKEN.md)).

`approve`/`transferFrom` are not implemented yet — tracked in
[`docs/todo/backlog.md`](../../../docs/todo/backlog.md). -/

namespace Token

-- `Token`'s own declared unit. Nominally distinct from `Wad` and from any other token's
-- `Amount`, so passing the wrong token's amount into a cross-contract call is a compile error.
declare_token_amount Amount

structure TokenStorage where
  owner : Address := 0
  totalSupply : Amount := ⟨0⟩
  /-- Every address reads as `0` until written (a total function, like real EVM storage). -/
  balances : Wad.WadMap := fun _ => ⟨0⟩
  deriving ContractStorage

inductive TokenError where
  | Overflow
  | Underflow
  | NotOwner
  deriving Repr, DecidableEq, ContractError

/-- Only carries `amount`, not the full ERC20 `Transfer(from, to, amount)` shape — event payloads
are currently limited to `Ty`'s five DSL-level kinds with 0-or-1 arguments each (see
[`docs/reference/TOKEN.md`](../../../docs/reference/TOKEN.md)). -/
inductive TokenEvent where
  | Transfer (amount : Amount)
  | Mint (amount : Amount)
  deriving Repr, DecidableEq, ContractEvent

-- Read-only query; `view` makes this callable via `read Token.balanceOf(who);` from another
-- contract. Never reverts, since every address has some balance (`0` if never written).
view balanceOf(who : Address) : Amount => σ.balances[who];

-- The checked `-?`/`+?` ops enforce "can't transfer more than you have" on their own (raising
-- `Underflow`), so no separate `require` is needed.
tx transfer(recipient : Address, amount : Amount) {
  σ.balances[msg.sender] -=? amount;
  σ.balances[recipient] +=? amount;
  emit Transfer(amount);
}

-- Owner-gated issuance.
tx mint(recipient : Address, amount : Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  σ.totalSupply +=? amount;
  σ.balances[recipient] +=? amount;
  emit Mint(amount);
}

/-! ## DSL wiring + compilation: `ContractDef` + Yul/bytecode emission -/

-- Public functions, event topics, deploy step, and the `TokenM` monad abbreviation are all
-- inferred from the declarations above; see `derive_contract`'s docstring for defaults.
derive_contract "Token" TokenStorage TokenError TokenEvent

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
