import Examples.Counter.Spec
import Examples.Counter.Proofs.Tx
import Examples.Counter.Contract

/-!
Counter theorems: Tx-level deltas for the four runtime functions.
-/

open Lsc Counter

namespace Counter

variable (msg : Ctx) (w : World)

/-- A successful `increment` adds one to `count`. Success already implies the
add did not overflow a 256-bit word. -/
theorem increment_adds {w' : World}
    (h : Tx.run increment msg w = .ok ((), w')) :
    w'.self.count = w.self.count + 1 :=
  Proof.increment_adds msg w h

/-- A successful `incrementBy n` adds `n` to `count`. Success already implies
`n` is nonzero and the add did not overflow. -/
theorem incrementBy_adds (n : Nat) {w' : World}
    (h : Tx.run (incrementBy n) msg w = .ok ((), w')) :
    w'.self.count = w.self.count + n :=
  Proof.incrementBy_adds msg w n h

/-- A successful `decrement` saturates at zero: a zero counter stays zero,
otherwise it subtracts one. It does not revert on underflow. -/
theorem decrement_saturates {w' : World}
    (h : Tx.run decrement msg w = .ok ((), w')) :
    w'.self.count = if w.self.count = 0 then 0 else w.self.count - 1 :=
  Proof.decrement_saturates msg w h

/-- `get` returns the stored counter and leaves the world unchanged. -/
theorem get_returns {n : Nat} {w' : World}
    (h : Tx.run get msg w = .ok (n, w')) :
    n = w.self.count ∧ w' = w :=
  Proof.get_returns msg w h

end Counter
