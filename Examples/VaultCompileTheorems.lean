import Examples.VaultCompileProof
import Examples.Vault
import Lsc.Stdlib.ERC20

/-!
Vault is the one-binding S2 instance: every runtime function (including
`deposit`/`withdraw`, which `CALL` the asset token) compiles with
`toYulFn_correct_ext`. The callee address lives in storage field `asset`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc.Stdlib

/-- Every Vault runtime function matches `Core.denote` on the external Yul
dialect under some fault oracle. The asset token must `Conforms` to IERC20
at the bound address (not `self`), and `RX` ties the ERC20 ghost to that
account's EVM storage. Constructors with CALL are out of scope. -/
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
