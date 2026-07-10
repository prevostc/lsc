import Lsc.Prelude
import Lsc.Lang.Syntax
import Lsc.Lib.Interfaces.IERC20

/-!
# `SafeERC20` — inlined library for checked IERC20 `transfer`

OpenZeppelin-style wrapper: `let ok = exec token.transfer(..); require (ok) else revert ..`.
Registered via `derive_library` and inlined at `exec SafeERC20.safeTransfer(..)` call sites. -/

namespace SafeERC20

open Lsc Lsc.Interfaces Lsc.Deriving

structure SafeERC20Storage where
  deriving ContractStorage

inductive SafeERC20Error where
  | ExternalCallFailed
  deriving Repr, DecidableEq, ContractError

inductive SafeERC20Event where
  deriving Repr, DecidableEq, ContractEvent

@nonreentrant
tx safeTransfer(token : IERC20, recipient : Address, amount : Wad) {
  let ok = exec token.transfer(recipient, amount);
  require (ok) else revert ExternalCallFailed();
}

derive_library "SafeERC20" SafeERC20Storage SafeERC20Error SafeERC20Event

end SafeERC20
