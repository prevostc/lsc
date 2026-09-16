import Lsc.Security.WealthTheorems
import Examples.WETH.Spec
import Examples.WETH.Proofs.Tx

/-!
Wrapped-token claim is storage-only (`Claim.ofSelf`). Wealth therefore
covers unauthorised *token* extraction the same way as Token.

Native ETH of `self` is `World.nativeBalance`. The framework does not
treat it as a `Claim`: `env` steps can change `ext` balances, and
`Native.send`'s post-`ext` is the oracle's. The trace `step` credits
`ctx.value` onto `selfBalance` before `Tx.run`. Native-ETH extraction
is not a Wealth claim.
-/

open Lsc Lsc.Security WETH

namespace WETH

namespace Proof

theorem weth_backed {w : World Storage ExtState Event} (h : Inv w) :
    w.self.totalSupply.raw ≤ World.nativeBalance w :=
  h.2

end Proof

end WETH
