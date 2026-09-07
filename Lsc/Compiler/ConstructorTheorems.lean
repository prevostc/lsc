import Lsc.Compiler.ConstructorDefs
import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.ConstructorProof
import Lsc.Compiler.CoreDefs

set_option linter.unusedVariables false

/-!
Yul constructors: Solidity CREATE passes args as a suffix of `env.code`, not
calldata. EVM `bytecode_deploy_correct` cannot see those extra bytes.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A call-free, `ite`-free unit constructor matches `Core.denote` when
constructor args are the last `32n` bytes of `st0.env.code` (CREATE
convention). Success falls through without `halt`; revert agrees on error
bytes. Vault/AMM constructors that `CALL` are out of scope. -/
theorem constructor_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hk : f.kind = .constructor) (hret : f.ret = .unit)
    (hM1 : CallFree f.core) (hNo : NoIte f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : 32 * f.params.length < wordBound)
    (hptr : abiPtr + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulCtor c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hle : 32 * f.params.length ≤ st0.env.code.length)
    (hcode : st0.env.code.length < wordBound) :
    ConstructorCorrect c Γ κ f yul ctx w st0 :=
  Proof.constructor_correct c Γ hΓ κ hκ f hk hret hM1 hNo hlen hbound hptr
    yul hyul ctx w st0 hctx hR hle hcode

/-- Init code is the constructor body followed by `constructorCode "runtime"`.
On success the body falls through (`.normal`) and the prologue returns the
layout's `"runtime"` bytecode slice; on revert the body halts and storage
is the pre-state. -/
theorem deployBlock_correct {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hctor : c.ctor = some f)
    (hk : f.kind = .constructor) (hret : f.ret = .unit)
    (hM1 : CallFree f.core) (hNo : NoIte f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : 32 * f.params.length < wordBound)
    (hptr : abiPtr + 32 * f.params.length < wordBound)
    (body : YBlock) (hbody : toYulCtor c f = some body)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hle : 32 * f.params.length ≤ st0.env.code.length)
    (hcode : st0.env.code.length < wordBound) :
    let yul := body ++ constructorCode "runtime"
    let args := decodeCtorArgs f.params.length st0.env.code
    match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
    | .ok (_, w') =>
        ∃ st1 st2,
          Run evm body st0 [] st1 .normal ∧ R c Γ κ w' st1 ∧
          Run evm (constructorCode "runtime") st1 [] st2 .halt ∧
          st2.halted = some (.ret,
            readBytes (byteFrom st1.env.code)
              (st1.env.dataOffset (litValue (.string "runtime"))).toNat
              (st1.env.dataSize (litValue (.string "runtime"))).toNat)
    | .error e =>
        ∃ stObs bytes,
          Run evm body st0 [] stObs .halt ∧
          stObs.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes ∧ R c Γ κ w st0 :=
  Proof.deployBlock_correct c Γ hΓ κ hκ f hctor hk hret hM1 hNo hlen hbound hptr
    body hbody ctx w st0 hctx hR hle hcode

end Lsc.Compiler
