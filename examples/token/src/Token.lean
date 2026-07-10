import Lsc.Prelude
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Lang.Syntax

open Lsc Lsc.Compile
open Lsc.Deriving

/-!
# `Token` — minimal IERC20-shaped reference token

A simple address-keyed balance mapping with `balanceOf`, `transfer`, and owner-gated `mint`.
ABI surface matches [`Lsc.Interfaces.IERC20`](../../../Lsc/Lib/Interfaces/IERC20.lean); proofs show
[`HonestERC20`](../../../Lsc/Lib/Interfaces/IERC20.lean) is satisfiable via
[`test/TokenTheorem.lean`](../test/TokenTheorem.lean) (`token_honest_erc20`).

See [`docs/reference/TOKEN.md`](../../../docs/reference/TOKEN.md). Independent of the Escrow example
— callers treat this as any other on-chain ERC20 at an address. -/

namespace Token

declare_token_amount Amount

structure TokenStorage where
  owner : Address
  totalSupply : Amount := ⟨0⟩
  balances : Mapping Address Amount := Mapping.empty
  /-- `allowances[owner][spender]` — how much `spender` may still `transferFrom` out of `owner`'s
      balance. Keyed by the pair `(owner, spender)` via `Lsc.Mapping`'s generic `[DecidableEq K]`
      key parameter (see `Lsc.Deriving.FieldKind.mapping2`'s docstring) — no bespoke nested
      `Mapping Address (Mapping Address Amount)` machinery needed. Standard ERC20 semantics:
      finite approvals only (no "infinite approval" special-casing), decremented by exactly the
      transferred amount on every `transferFrom` (see `transferFrom`'s body below). -/
  allowances : Mapping (Address × Address) Amount := Mapping.empty
  deriving ContractStorage

inductive TokenError where
  | Overflow
  | Underflow
  | NotOwner
  deriving Repr, DecidableEq, ContractError

inductive TokenEvent where
  | Transfer (amount : Amount)
  | Mint (amount : Amount)
  | Approval (amount : Amount)
  deriving Repr, DecidableEq, ContractEvent

constructor (owner_ : Address) {
  σ.owner = owner_;
}

view balanceOf(who : Address) : Amount => σ.balances[who];

view allowance(owner : Address, spender : Address) : Amount => σ.allowances[owner][spender];

tx transfer(recipient : Address, amount : Amount) {
  σ.balances[msg.sender] -=? amount;
  σ.balances[recipient] +=? amount;
  emit Transfer(amount);
}

tx mint(recipient : Address, amount : Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  σ.totalSupply +=? amount;
  σ.balances[recipient] +=? amount;
  emit Mint(amount);
}

-- Standard ERC20 `approve`: sets (not adds to) `msg.sender`'s allowance for `spender` to
-- exactly `amount`, overwriting any prior allowance — the same semantics OpenZeppelin's
-- `ERC20.approve` has (the well-known "approval front-running" race is out of scope, matching
-- plain ERC20, not e.g. `increaseAllowance`/`decreaseAllowance`).
tx approve(spender : Address, amount : Amount) {
  σ.allowances[msg.sender][spender] = amount;
  emit Approval(amount);
}

-- Standard ERC20 `transferFrom`: moves `amount` from `sender`'s balance to `recipient`,
-- provided `msg.sender` (the caller, typically a contract like a future `CPAMM`) has a sufficient
-- `allowances[sender][msg.sender]` — decremented by exactly `amount` (finite-approval semantics,
-- no "infinite approval" special-casing, see `TokenStorage.allowances`'s docstring). Allowance
-- *and* balance sufficiency are both enforced the same way `transfer` already enforces balance
-- sufficiency: via `-=?`'s checked subtraction, which reverts with the framework's `Underflow`
-- arith error (no bespoke `<`/`≤` comparison operator needed — none exists at the `Wad.Expr`
-- level today, see this migration's scope notes).
tx transferFrom(sender : Address, recipient : Address, amount : Amount) {
  σ.allowances[sender][msg.sender] -=? amount;
  σ.balances[sender] -=? amount;
  σ.balances[recipient] +=? amount;
  emit Transfer(amount);
}

derive_contract "Token" TokenStorage TokenError TokenEvent

/-! ## Bytecode

`derive_contract` emits `bytecodeHex` / `deployHex` for the runtime and deploy payloads.
After `lake build Token`, `#eval` the block below.
-/

example : Token.bytecodeHex.startsWith "0x" ∧ Token.bytecodeHex.length > 10 := by native_decide

#eval IO.println s!"Token.bytecodeHex ({Token.bytecodeHex.length} chars)"
#eval IO.println Token.bytecodeHex

end Token
