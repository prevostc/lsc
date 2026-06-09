import Lsc.UInt256
import Lsc.ContractM

namespace Lsc

namespace UInt256

def addChecked {E S : Type} (a b : UInt256) : ContractM E S UInt256 :=
  if h : a.val + b.val < 2 ^ 256 then
    pure (mk (a.val + b.val) h)
  else
    ContractM.arithFail .overflow

/-- Checked add with a natural literal on the right (`n +? 1`, `n +? 42`, …). -/
def addCheckedNat {E S : Type} (a : UInt256) (n : Nat) : ContractM E S UInt256 :=
  if h : a.val + n < 2 ^ 256 then
    pure (mk (a.val + n) h)
  else
    ContractM.arithFail .overflow

macro a:term " +? " n:num : term => `(UInt256.addCheckedNat $a $n)

macro a:term " +? " b:term : term => `(UInt256.addChecked $a $b)

end UInt256

end Lsc
