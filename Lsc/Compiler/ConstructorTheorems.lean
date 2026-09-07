import Lsc.Compiler.ConstructorDefs
import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.ConstructorProof
import Lsc.Compiler.CoreDefs

set_option linter.unusedVariables false

/-!
Yul constructors: CREATE passes arguments as a suffix of init code, not
as calldata. The EVM deploy theorem cannot see those extra bytes.

Shared assumptions: the constructor never CALLs out, has no `if` in the
unsupported shape, returns nothing, and the compiler accepted it.
Vault and AMM constructors that CALL `decimals` are out of scope.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A call-free constructor that returns nothing matches the high-level
model when its arguments are the last words of init code, as CREATE
passes them. Success falls through without halting, so the deploy
prologue can return the runtime bytecode; a revert agrees on error
bytes. Vault and AMM constructors that CALL are out of scope. -/
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

/-- Init code is the constructor body followed by the "return the runtime
bytecode" prologue. On success the body falls through and the prologue
returns the layout's runtime slice; on revert the body halts and storage
is the pre-state. Same constructor restrictions as `constructor_correct`;
this is the whole deploy object, not just the body. -/
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
