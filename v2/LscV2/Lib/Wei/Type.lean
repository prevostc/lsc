import LscV2.Core.UInt256

namespace LscV2.Wei

structure Wei where
  raw : UInt256
  deriving Repr, DecidableEq

def mkNat (n : Nat) : Wei := ⟨BitVec.ofNat 256 n⟩

end LscV2.Wei
