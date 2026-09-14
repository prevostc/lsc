import Lsc.Compiler.CorrectnessDefs
import Lsc.Compiler.Proof.CorrectnessProof

/-!
`mkEvmStateExt` field projections: halt, immutables, storage, calldata,
keccak, logs, address, and foreign storage. Used to start related EVM
frames from a Core world.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM

/-- `mkEvmStateExt` starts unhalted. -/
theorem mkEvmStateExt_halted (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).halted = none :=
  Proof.mkEvmStateExt_halted cd σ ξ κ ctx

/-- `mkEvmStateExt` has zero immutables. -/
theorem mkEvmStateExt_immutable (cd σ ξ κ ctx k) :
    (mkEvmStateExt cd σ ξ κ ctx).env.immutable k = 0 :=
  Proof.mkEvmStateExt_immutable cd σ ξ κ ctx k

/-- `mkEvmStateExt` installs the given storage map. -/
theorem mkEvmStateExt_storage (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).storage = σ :=
  Proof.mkEvmStateExt_storage cd σ ξ κ ctx

/-- `mkEvmStateExt` installs the given calldata. -/
theorem mkEvmStateExt_calldata (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.calldata = cd :=
  Proof.mkEvmStateExt_calldata cd σ ξ κ ctx

/-- `mkEvmStateExt` installs the given keccak oracle. -/
theorem mkEvmStateExt_keccak (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.keccakOf = κ :=
  Proof.mkEvmStateExt_keccak cd σ ξ κ ctx

/-- `mkEvmStateExt` starts with empty logs. -/
theorem mkEvmStateExt_logs (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).logs = [] :=
  Proof.mkEvmStateExt_logs cd σ ξ κ ctx

/-- `mkEvmStateExt` sets `env.address` from `ctx.self`. -/
theorem mkEvmStateExt_address (cd σ ξ κ ctx) :
    (mkEvmStateExt cd σ ξ κ ctx).env.address = BitVec.ofNat 256 ctx.self :=
  Proof.mkEvmStateExt_address cd σ ξ κ ctx

/-- Foreign storage is `σ` at self and `ξ` at every other account. -/
theorem mkEvmStateExt_foreign (cd σ ξ κ ctx addr slot) :
    evmForeign (mkEvmStateExt cd σ ξ κ ctx) addr slot =
      if accountKey addr = accountKey (BitVec.ofNat 256 ctx.self) then σ slot
      else ξ addr slot :=
  Proof.mkEvmStateExt_foreign cd σ ξ κ ctx addr slot

end Lsc.Compiler
