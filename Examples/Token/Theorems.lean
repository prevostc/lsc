import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.DispatchTheorems
import Examples.Token.Spec
import Examples.Token.Proofs.Tx
import Examples.Token.Proofs.Security
import Examples.Token.Proofs.Compile
import Examples.Token.Proofs.EndToEnd
import Examples.Token.Contract

set_option linter.unusedVariables false

/-!
Token theorems: local conservation of `transfer`, spec-level anti-extraction
and solvency, the call-free compiler instance, and those facts on compiled
runtime bytecode (including deploy-then-runtime).
-/

open Lsc Token

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged: no tokens are created or destroyed by the send. This
includes a self-transfer, which is a no-op on those two balances. Success
already implies the sender had the funds and the recipient's balance plus
the amount fit in a 256-bit word. This is the local conservation fact
behind Token's global "balances sum to supply" invariant. -/
theorem transfer_conserves (dst : Address) (amount : Nat)
    {w' : World Storage Unit Event}
    (h : Tx.run (transfer dst amount) ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender + w'.self.balances dst =
      w.self.balances ctx.sender + w.self.balances dst :=
  Proof.transfer_conserves ctx w dst amount h

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
    (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
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
theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
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
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
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
    (ctx : Ctx) (w : World Token.Storage Unit Token.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Token.contract Token.schema κ w st0) :
    RuntimeBlockCorrectCallFree Token.contract Token.schema κ yul ctx w st0 :=
  Proof.token_dispatch_correct κ hκ yul hyul ctx w st0 hctx hR

end Lsc.Compiler

open Lsc Lsc.Compiler Lsc.Security Token
open YulSemantics.EVM
open YulEvmCompiler (compile Instr)

namespace Token

/-- Whatever sequence of calls an adversary sends to the deployed Token
bytecode, Alice's balance in EVM storage never falls unless she authorised
a decoded call in that sequence — she sent `transfer` or `burn`, or a
`transferFrom` spent an allowance she had granted. Unknown selectors and
short calldata are ignored. The compiler must have accepted the contract,
storage keys must not collide, Alice's address and stored values must fit
in a 256-bit word, and the starting storage must match a Token world whose
balances already sum to supply. This carries the spec-level anti-extraction
fact down to the bytecode. -/
theorem token_bytecode_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (a : Address) (σ : U256 → U256)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (ha : Nat.lt a wordBound) :
    ∀ σ', EvmTraceRunAll is calls σ σ' →
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat :=
  Proof.token_bytecode_no_unauthorized_extraction rt hrt is hcomp hκ self calls w a
    σ hw hlog hWF hA hs hwf ha

/-- If Alice never authorised any call in a given Token trace, there is an
EVM execution of the encoded calldata that leaves her balance slot no
lower than it started. Use this when you already have a high-level call
sequence rather than raw calldata; `token_bytecode_no_unauthorized_extraction`
is the matching fact for every halted run of arbitrary calldata. Encoded
arguments must fit in a word; other assumptions match that theorem. -/
theorem token_bytecode_no_unauthorized_extraction_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (a : Address) (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hlog : w.log = [])
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : EncodeBounded (mkTokenSetup hκ rt hrt is hcomp) tr)
    (ha : Nat.lt a wordBound) :
    ∃ σ', EvmTraceRun is
        (encodeCalls (mkTokenSetup hκ rt hrt is hcomp) tr) σ σ' ∧
      (σ (mapSlot1 evmKeccak 2 a)).toNat ≤ (σ' (mapSlot1 evmKeccak 2 a)).toNat :=
  Proof.token_bytecode_no_unauthorized_extraction_exists rt hrt is hcomp hκ self tr w a
    σ hw hW hlog hA hs hwf hb ha

/-- After any halted EVM execution of a well-formed call sequence against
compiled Token, recorded balances still do not exceed total supply, and
the ending EVM storage still matches that Token world. Unknown selectors
are ignored. Unlike the anti-extraction theorem this concludes solvency
and a full storage match, not a single balance slot. Same compiler and
layout assumptions. -/
theorem token_bytecode_solvent
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w) :
    ∀ σ', EvmTraceRunAll is calls σ σ' →
      Solvent claim holdings self
        (run (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w) ∧
      storageRel Token.contract Token.schema evmKeccak
        (run (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w).self σ' :=
  Proof.token_bytecode_solvent rt hrt is hcomp hκ self calls w σ hw hlog hWF hs hwf

/-- Given a well-formed Token trace, some EVM execution of the encoded
calldata ends in a solvent Token world whose storage matches. Dual of
`token_bytecode_solvent` when you start from a high-level trace rather
than raw calldata; encoded arguments must fit in a word. -/
theorem token_bytecode_solvent_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (σ : U256 → U256)
    (hw : Inv w) (hW : Wf self tr) (hlog : w.log = [])
    (hs : storageRel Token.contract Token.schema evmKeccak w.self σ)
    (hwf : WorldWF Token.contract Token.schema w)
    (hb : EncodeBounded (mkTokenSetup hκ rt hrt is hcomp) tr) :
    ∃ σ', EvmTraceRun is (encodeCalls (mkTokenSetup hκ rt hrt is hcomp) tr) σ σ' ∧
      Solvent claim holdings self (run (callsOf tr) w) ∧
      storageRel Token.contract Token.schema evmKeccak
        (run (callsOf tr) w).self σ' :=
  Proof.token_bytecode_solvent_exists rt hrt is hcomp hκ self tr w σ hw hW hlog hs hwf hb

/-- After Token's constructor has run — CREATE arguments as a suffix of
init code — and left a matching solvent world, Alice's balance slot still
cannot fall under any subsequent runtime call sequence she did not
authorise. This is the deploy-then-runtime story: it starts from a
post-constructor EVM state, because the plain EVM deploy theorem does not
model trailing constructor arguments. -/
theorem token_deploy_then_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compileErased rt = some is)
    (hκ : KeccakSep Token.contract evmKeccak)
    (self : Address) (calls : List EvmCall) (w : World Storage Unit Event)
    (a : Address) (st : EvmState)
    (hw : Inv w) (hlog : w.log = [])
    (hWF : CallsWF (mkTokenSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkTokenSetup hκ rt hrt is hcomp) calls) w)
    (hR : R Token.contract Token.schema evmKeccak w st)
    (hwf : WorldWF Token.contract Token.schema w)
    (ha : Nat.lt a wordBound) :
    ∀ σ', EvmDeployThenTrace is st.storage calls σ' →
      (st.storage (mapSlot1 evmKeccak 2 a)).toNat ≤
        (σ' (mapSlot1 evmKeccak 2 a)).toNat :=
  Proof.token_deploy_then_no_unauthorized_extraction rt hrt is hcomp hκ self calls w a
    st hw hlog hWF hA hR hwf ha

end Token
