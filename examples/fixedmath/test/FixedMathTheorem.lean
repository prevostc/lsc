import FixedMath
import Lsc.Lang.Eval
import Lsc.Lib.Math.EvmProofsCompose

open Lsc FixedMath Lsc.Math.EvmProofs Lsc.Compile.Bytecode

def fourWad : Wad := Wad.mkNat (4 * Lsc.Fixed.scale 18)
def nineWad : Wad := Wad.mkNat (9 * Lsc.Fixed.scale 18)
def sixWad : Wad := Wad.mkNat (6 * Lsc.Fixed.scale 18)

example :
    Except.map (fun x => Val.wadOf x.1) (runS (sqrtProduct fourWad nineWad) mkState) = .ok sixWad := by
  native_decide

example :
    Except.map (fun x => Val.wadOf x.1) (runS (minOf fourWad nineWad) mkState) = .ok fourWad := by
  native_decide

example :
    (contractDef.functions.filter (·.kind == FunctionKind.view)).length = 2 := by
  native_decide

/-- The derived `FixedMath` contract validates and dispatches the canonical `sqrtProductFunction`. -/
theorem fixedMath_validateAll_ok :
    Checks.validateAll contractDef = .ok contractDef := by
  have : (Checks.validateAll contractDef).isOk := by native_decide
  simpa using this

theorem fixedMath_sqrtProductFunction_mem :
    sqrtProductFunction ∈ Contract.dispatchedFunctions contractDef := by
  native_decide

/-- `FixedMath` instantiation of the compositional EVM floor-sqrt theorem.

Successful production `Contract.contract` / `encode` for this package's `contractDef` and `config`,
ABI-well-formed calldata, ordinary initial machine state, `PathScopedXPrecheckSafe`, explicit
valid-jump membership for the resolved `sqrtProduct` entry, and the stated no-wrap bounds imply
`EVM.X` returns the ABI encoding of the half-up widened floor square root. -/
theorem fixedMath_sqrtProduct_X_returns
    (instrs : List Instr) (code : ByteArray)
    (validJumps : Array EvmYul.UInt256) (st : EvmYul.EVM.State)
    (nat : IRState) (a b : EvmYul.UInt256) (calldata : ByteArray)
    (hcontract : Contract.contract config contractDef = .ok instrs)
    (hencode : encode instrs = .ok code)
    (hencodable :
      ∀ resolved,
        resolveInstrs (fixpointLabels instrs) instrs = .ok resolved →
          EvmYulBridge.EncodablePlainInstrs resolved)
    (hcodeLimit : code.size + 33 < 2 ^ 64)
    (hselectorWidths :
      ∀ fn ∈ Contract.dispatchedFunctions contractDef,
        pushWidth (computeSelector fn).toNat ≤ 32)
    (hwf : AbiDispatch.WellFormed
      (computeSelector sqrtProductFunction).toNat [a, b] calldata)
    (hsafe : AbiDispatch.PathScopedXPrecheckSafe validJumps st)
    (hcode : st.executionEnv.code = code)
    (hpc : st.pc = .ofNat 0) (hstack : st.stack = [])
    (hmemory : st.memory = ByteArray.empty)
    (hcalldata : st.executionEnv.calldata = calldata)
    (hbaseAgree : (AbiDispatch.machineWordState st).Agrees nat)
    (hproduct : a.toNat * b.toNat < EvmYul.UInt256.size)
    (hsum : a.toNat * b.toNat + scale / 2 < EvmYul.UInt256.size)
    (hwidened :
      ((a.toNat * b.toNat + scale / 2) / scale) * scale < 2 ^ 256)
    (hsqrtNoWrap :
      let natAB := (nat.setLocal "a" a.toNat).setLocal "b" b.toNat
      StmtNoWrap { state := natAB } sqrtProductBody)
    (htargetJump :
      (.ofNat (AbiDispatch.resolvedSelectorTarget (fixpointLabels instrs)
          sqrtProductFunction) : EvmYul.UInt256) ∈ validJumps) :
    ∃ (fuel : Nat) (final : EvmYul.EVM.State) (r : EvmYul.UInt256),
      EvmYul.EVM.X fuel validJumps st =
        .ok (.success final r.toByteArray) ∧
      r.toNat = Nat.sqrt (((a.toNat * b.toNat + scale / 2) / scale) * scale) ∧
        r.toNat * r.toNat ≤ ((a.toNat * b.toNat + scale / 2) / scale) * scale ∧
        ((a.toNat * b.toNat + scale / 2) / scale) * scale <
          (r.toNat + 1) * (r.toNat + 1) :=
  validatedContract_sqrtProduct_X_returns config contractDef instrs code validJumps st nat
    a b calldata fixedMath_validateAll_ok fixedMath_sqrtProductFunction_mem hcontract hencode
    hencodable hcodeLimit hselectorWidths hwf hsafe hcode hpc hstack hmemory hcalldata
    hbaseAgree hproduct hsum hwidened hsqrtNoWrap htargetJump
