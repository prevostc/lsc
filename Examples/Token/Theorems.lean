import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Stdlib.ERC20
import Examples.Token.Spec
import Examples.Token.Proofs.Tx
import Examples.Token.Proofs.Security
import Examples.Token.Proofs.Compile
import Examples.Token.Proofs.Implements
import Examples.Token.Contract

set_option linter.unusedVariables false

/-!
Token theorems: local conservation of `transfer` / `transferFrom`, `approve`
sets allowance, the ERC20 conformance theorem, spec-level anti-extraction and
solvency, and the call-free compiler instance. Per-contract bytecode theorems
are not stated; the compiler theorems carry that.
-/

open Lsc Lsc.Stdlib Token

namespace Token

variable (ctx : Ctx) (w : World Storage ExtState Event)

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged: no tokens are created or destroyed by the send. This
includes a self-transfer, which is a no-op on those two balances. Success
already implies the sender had the funds and the recipient's balance plus
the amount fit in a 256-bit word. This is the local conservation fact
behind Token's global "balances sum to supply" invariant. -/
theorem transfer_conserves (dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transfer dst amount) ctx w = .ok (true, w')) :
    w'.self.balances ctx.sender + w'.self.balances dst =
      w.self.balances ctx.sender + w.self.balances dst :=
  Proof.transfer_conserves ctx w dst amount h

/-- A successful `transferFrom` leaves the sum of the source's and recipient's
balances unchanged, including a self-transfer. Success already implies the
allowance and balance checks and that the credit fit in a word. -/
theorem transferFrom_conserves (src dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transferFrom src dst amount) ctx w = .ok (true, w')) :
    w'.self.balances src + w'.self.balances dst =
      w.self.balances src + w.self.balances dst :=
  Proof.transferFrom_conserves ctx w src dst amount h

/-- A successful `transferFrom` spends exactly `amount` of `src`'s allowance
for the caller: the remaining allowance plus `amount` equals the allowance
before the call. This includes self-spend (`sender = src`); the ERC20 spec
only requires the fact when `sender ≠ src`. -/
theorem transferFrom_allowance (src dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transferFrom src dst amount) ctx w = .ok (true, w')) :
    w'.self.allowances src ctx.sender + amount =
      w.self.allowances src ctx.sender :=
  Proof.transferFrom_allowance ctx w src dst amount h

/-- A successful `approve` writes `amount` as the caller's allowance for
`spender`. -/
theorem approve_sets (spender : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (approve spender amount) ctx w = .ok (true, w')) :
    w'.self.allowances ctx.sender spender = amount :=
  Proof.approve_sets ctx w spender amount h

/-- Token is a conforming ERC20: every promise in `IERC20.Spec` holds of
`Token.impl`. Named `erc20` because `lsc_contract` already generates the ABI
spec as `Token.spec`. -/
theorem erc20 : IERC20.Spec Token.impl :=
  Proof.erc20

end Token

open Lsc Lsc.Security Token

namespace Token

/-- No sequence of calls can reduce Alice's Token balance unless she authorised
one of them: she sent `transfer` or `burn` herself, or a `transferFrom` spent
an allowance she had granted, judged against the allowance stored at that
moment. Other users may transfer, mint, approve, or burn their own tokens in
any order; those actions cannot debit Alice. Views, `approve`, and `mint`
never decrease an existing balance, and a reverted call leaves every balance
unchanged. The starting balances must already sum to total supply. -/
theorem token_no_unauthorized_extraction
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv w) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.token_no_unauthorized_extraction tr w a hw hR hA

/-- After any well-formed sequence of Token calls, recorded balances still
sum to total supply on a finite support: every token is accounted for.
The starting world must already satisfy that equality. Mint raises both
sides together; burn lowers both; Token has no external asset that could
drift. The generic solvency bound (sum of balances ≤ supply) is then
immediate. -/
theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage ExtState Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Inv (run tr w) :=
  Proof.token_solvent self tr w hW hR h

end Token

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- If the compiler accepted a Token runtime function, running the emitted Yul
has the same effect on storage, return data, and halt kind as the high-level
Token model: a successful call agrees on the new balances and allowances, a
revert rolls storage back and returns the same error bytes. Token uses
mapping slots, unlike Counter's single word. Constructors are excluded;
Token never calls another contract. -/
theorem token_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (f : FnDef) (hf : f ∈ Token.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Token.contract f = some yul)
    (ctx : Ctx) (w : World Token.Storage ExtState Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    ToYulFnCorrect Token.contract Token.schema κ f yul ctx w st0 :=
  Proof.token_correct κ hκ f hf _hk yul hyul ctx w st0 hctx hR

/-- The compiled Token dispatcher agrees with the high-level model on every
calldata: a known selector runs the matching function, an unknown selector
or short calldata reverts with storage unchanged. Same compiler and layout
assumptions as `token_correct`; this is the whole ABI surface, not one
function. -/
theorem token_dispatch_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Token.contract κ)
    (yul : YBlock) (hyul : runtimeBlock Token.contract = some yul)
    (ctx : Ctx) (w : World Token.Storage ExtState Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    RuntimeBlockCorrectCallFree Token.contract Token.schema κ yul ctx w st0 :=
  Proof.token_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler
