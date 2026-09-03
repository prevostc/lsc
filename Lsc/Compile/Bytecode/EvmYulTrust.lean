import EvmYul.Wheels

namespace Lsc.Compile.Bytecode.EvmYulTrust

/-- Exceptional trust boundary for EvmYul's `memset_zero` FFI.

EvmYul declares `ffi.ByteArray.zeroes` as an opaque external constant and provides no kernel
specification. This axiom states exactly the extensional behavior of that one FFI function:
it returns an array of the requested length whose bytes are all zero. No other FFI operation is
axiomatized in LSC. Re-evaluate this boundary if EvmYul exposes a theorem or pure reference
implementation. -/
axiom zeroes_eq_replicate (n : USize) :
  ffi.ByteArray.zeroes n = ByteArray.mk (Array.replicate n.toNat 0)

@[simp]
theorem zeroes_zero :
    ffi.ByteArray.zeroes 0 = ByteArray.empty := by
  rw [zeroes_eq_replicate]
  rfl

@[simp]
theorem size_zeroes (n : USize) :
    (ffi.ByteArray.zeroes n).size = n.toNat := by
  rw [zeroes_eq_replicate]
  exact Array.size_replicate ..

/-- Local exposure of an existing pure EvmYul fact hidden by module privacy.

`EvmYul.UInt256.toByteArray` left-pads the private `toBytes'` result to 32 bytes. EvmYul proves
the required bound internally as the private theorem `toBytes'_UInt256_le`, so downstream modules
cannot cite it. This axiom mirrors that already-kernel-proved pure serialization fact; it is not
an additional FFI assumption. Remove it once EvmYul exports the theorem. -/
axiom uint256_toByteArray_size (value : EvmYul.UInt256) :
  value.toByteArray.size = 32

end Lsc.Compile.Bytecode.EvmYulTrust
