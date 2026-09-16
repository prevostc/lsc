import Lsc.Compiler.CorrectnessDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of `mkEvmStateExt` field projections. Statements live in
`CorrectnessTheorems`.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

namespace Proof

theorem mkEvmStateExt_halted (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).halted = none := rfl

theorem mkEvmStateExt_immutable (cd σ ξ κ ctx k) :
    (mkEvmStateExt cd σ ξ κ ctx).env.immutable k = 0 := rfl

theorem mkEvmStateExt_storage (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).storage = σ := rfl

theorem mkEvmStateExt_calldata (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.calldata = cd := rfl

theorem mkEvmStateExt_selfBalance_ult_callvalue (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.selfBalance.ult
      (mkEvmStateExt cd σ ξ κ ctx).env.callvalue = false := by
  simp [mkEvmStateExt, BitVec.ult]

theorem mkEvmStateExt_keccak (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.keccakOf = κ := rfl

theorem mkEvmStateExt_logs (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).logs = [] := rfl

theorem mkEvmStateExt_address (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.address = BitVec.ofNat 256 ctx.self := rfl

theorem mkEvmStateExt_foreign (cd σ ξ κ ctx addr slot) :
    evmForeign (mkEvmStateExt cd σ ξ κ ctx) addr slot =
      if accountKey addr = accountKey (BitVec.ofNat 256 ctx.self) then σ slot
      else ξ addr slot := rfl

end Proof

end Lsc.Compiler
