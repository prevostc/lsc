import Examples.Token.EndToEnd
import Examples.Token.EndToEndProof

set_option linter.unusedVariables false

/-!
Token bytecode security: Core-level anti-extraction and solvency, read
back from EVM storage of the compiled runtime.
-/

open Lsc Lsc.Compiler Lsc.Security Token
open YulSemantics.EVM
open YulEvmCompiler (compile Instr)

namespace Token

/-- Every halted EVM execution of a well-formed call sequence against
compiled Token, whose decoded Core trace never authorised `a`, does not
decrease `a`'s balance slot. Assumes `Inv`, `storageRel` of the starting
world, keccak-separated keys, and the compiler accepted the contract.
This is the S1 end-to-end anti-extraction theorem. -/
theorem token_bytecode_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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

/-- The same anti-extraction fact for a Security-layer trace that is
encoded into calldata (`_exists`): some EVM run realises the encoded
calls and `a`'s balance slot does not fall. Use this when you start from
a Core trace rather than raw calldata. -/
theorem token_bytecode_no_unauthorized_extraction_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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

/-- Every halted EVM execution of a well-formed call sequence leaves a
solvent Token world (`Σ balances ≤ totalSupply`) whose storage still
matches `storageRel`. Same compiler and layout hypotheses as the
anti-extraction theorem. -/
theorem token_bytecode_solvent
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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

/-- Solvency for an encoded Security trace: some EVM run realises the
calls and the post-world is solvent with matching storage. -/
theorem token_bytecode_solvent_exists
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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

/-- Anti-extraction after a Yul constructor that established `R` (CREATE
args as a suffix of `env.code`). Does not use `compileObject_correct`,
whose init frame has no trailing constructor args. -/
theorem token_deploy_then_no_unauthorized_extraction
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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
