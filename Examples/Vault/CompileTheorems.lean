import Examples.Vault.CompileProof
import Examples.Vault.Contract
import Stdlib.ERC20

/-!
Vault's compiler instance: every runtime function, including
`deposit` and `withdraw` which CALL the asset token, compiles to Yul
that matches the high-level Vault model.

The callee address is the `asset` slot. Shared assumptions: the
compiler accepted the function, the asset behaves like a conforming
ERC-20 at an address other than the vault, and the EVM frame matches
the starting world. Constructors that CALL are out of scope.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc.Stdlib

/-- If the compiler accepted a Vault runtime function, every execution of
the emitted Yul is predicted by the high-level Vault model under some
choice of which external calls fail: success agrees on storage, shares,
and token balances; a revert rolls our storage back. The asset token
must behave like a conforming ERC-20 at an address other than the vault.
Constructors are excluded — Vault's constructor CALLs `decimals` and is
outside this theorem. -/
theorem vault_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Vault.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Vault.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Vault.contract f = some yul)
    (ctx : Ctx) (w : World Vault.Storage Vault.Ext Vault.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Vault.contract Vault.schema κ w st0)
    (hRX : RX α Vault.assetB w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α) :
    ToYulFnCorrectExt α Vault.assetB Vault.contract Vault.schema κ calls f yul ctx w st0 :=
  Proof.vault_correct_ext α κ hκ calls f hf _hk yul hyul ctx w st0 hctx hR hRX hign hBindNe hconf

end Lsc.Compiler
