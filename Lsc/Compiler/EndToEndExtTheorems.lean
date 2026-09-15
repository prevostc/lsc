import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.Proof.EndToEndExtProof
import Lsc.Compiler.ExtOracleTheorems

set_option linter.unusedVariables false

/-!
Bytecode for contracts that CALL out: compiled runtime related to the
high-level model under `Oracle.ofExt`, and to EVM steps by the pinned
Yul-to-EVM compiler.

`toCall` scrubs `self` and restores storage / transient / self-logs after
an external CALL (`ExtOracle.noReentry`). A nested CALL/STATICCALL into
this runtime while the lock is held reverts (`nested_lock_reverts`).
ETH balances are not restored. Everything else about the callee is
adversarial. The compiler may have used either the erase path or powdr
spill (`compileBlock`). This is the Vault/AMM analogue of `bytecode_call_correct`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- Every Yul run of a compiled runtime that may CALL out is predicted by
the high-level model with `w.oracle = Oracle.ofExt o`, and the pinned
compiler produces matching EVM steps. Every halted matching EVM
execution agrees on our storage and on foreign storage. Reentrancy
into this contract reverts while the transient lock is held
(`ExtOracle.noReentry`); everything else about the callee is
adversarial. The compiler may have used either the erase path or powdr
spill (`compileBlock`). This is the Vault/AMM analogue of
`bytecode_call_correct`. -/
theorem bytecode_call_correct_ext {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hAgr : ExtAgree ctx.self w.ext yst0)
    (hOr : w.oracle = Oracle.ofExt o)
    (himm0 : ∀ k, yst0.env.immutable k = 0)
    (hLock : LockFree yst0) :
    BytecodeCallCorrectExt c Γ evmKeccak o ctx w yst0 rt is :=
  Proof.bytecode_call_correct_ext c Γ hΓ hκ o hCalls hctor hS2
    hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hAgr hOr himm0 hLock

/-- Given a memory-blind CALL oracle, there is a matching EVM execution of
compiled runtime whose post-storage (and foreign storage) is the unique
one the high-level model predicts. Without a total CALL oracle, "every
matching EVM execution" could hold vacuously, because the Yul-to-EVM
compiler only goes forward from a Yul run; a memory-blind oracle is
total by construction. Same callee hypothesis as
`bytecode_call_correct_ext`. The compiler may have used either compile
branch. -/
theorem evmCallRunExtAll_of_progress {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hAgr : ExtAgree ctx.self w.ext yst0)
    (hOr : w.oracle = Oracle.ofExt o)
    (himm0 : ∀ k, yst0.env.immutable k = 0)
    (hLock : LockFree yst0) :
    ∃ σ' ξ', EvmCallRunExtAll c Γ evmKeccak o ctx w is yst0 σ' ξ' :=
  Proof.evmCallRunExtAll_of_progress c Γ hΓ hκ o hCalls
    hctor hS2 hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hAgr hOr himm0 hLock

end Lsc.Compiler
