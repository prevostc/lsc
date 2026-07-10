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

-- OpenZeppelin-style checked wrapper for `IERC20.approve` — used by a caller (e.g. a future
-- `CPAMM`) that needs to pre-approve a spender before that spender later pulls tokens via
-- `transferFrom` (see `safeTransferFrom` below).
@nonreentrant
tx safeApprove(token : IERC20, spender : Address, amount : Wad) {
  let ok = exec token.approve(spender, amount);
  require (ok) else revert ExternalCallFailed();
}

-- OpenZeppelin-style checked wrapper for `IERC20.transferFrom` — the "pull" counterpart of
-- `safeTransfer`'s "push": lets a contract (e.g. a future `CPAMM`'s `swap`/`addLiquidity`) move
-- tokens *out of* `from`'s balance into `to`, provided `from` has already `approve`d this caller
-- for at least `amount` (standard ERC20 allowance flow).
@nonreentrant
tx safeTransferFrom(token : IERC20, sender : Address, recipient : Address, amount : Wad) {
  let ok = exec token.transferFrom(sender, recipient, amount);
  require (ok) else revert ExternalCallFailed();
}

derive_library "SafeERC20" SafeERC20Storage SafeERC20Error SafeERC20Event

end SafeERC20
