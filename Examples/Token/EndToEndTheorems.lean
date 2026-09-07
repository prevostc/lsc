import Examples.Token.EndToEnd
import Examples.Token.EndToEndProof

set_option linter.unusedVariables false

/-!
Token on compiled runtime bytecode: Alice's balance slot cannot fall
without her authorisation, and recorded supply still covers all balances,
after any halted sequence of EVM calls.

The compiler must have accepted the contract; storage keys must not
collide; starting storage must match a solvent Token world. Unknown
selectors and short calldata are ignored.

The `_exists` variants start from a high-level call sequence rather than
raw calldata. Deploy-then covers the constructor-then-runtime path.
-/

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
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
    (is : List Instr) (hcomp : compileBlock rt = some is)
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
