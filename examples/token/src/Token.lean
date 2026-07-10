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
  owner : Address := 0
  totalSupply : Amount := ⟨0⟩
  balances : Wad.WadMap := fun _ => ⟨0⟩
  deriving ContractStorage

inductive TokenError where
  | Overflow
  | Underflow
  | NotOwner
  deriving Repr, DecidableEq, ContractError

inductive TokenEvent where
  | Transfer (amount : Amount)
  | Mint (amount : Amount)
  deriving Repr, DecidableEq, ContractEvent

view balanceOf(who : Address) : Amount => σ.balances[who];

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

derive_contract "Token" TokenStorage TokenError TokenEvent

/-! ## Bytecode

`derive_contract` emits `bytecodeHex` / `deployHex` for the runtime and deploy payloads.
After `lake build Token`, `#eval` the block below.
-/

example : Token.bytecodeHex.startsWith "0x" ∧ Token.bytecodeHex.length > 10 := by native_decide

#eval IO.println s!"Token.bytecodeHex ({Token.bytecodeHex.length} chars)"
#eval IO.println Token.bytecodeHex

end Token
