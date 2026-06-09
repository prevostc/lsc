import Lsc.World
import Lsc.Word

namespace Lsc

/-- Internal field witness — offset only; authors use `get .field` / `set .field`. -/
structure Field (S : Type) (σ : Type) where
  offset : Nat
  deriving Repr, DecidableEq, BEq

/-- Contract state ↔ world bridge.
    `view` projects a `World` snapshot into the typed state struct.
    `embed` writes a state struct into a `World` (used by `runS`). -/
class ContractState (S : Type) where
  self  : Address
  view  : World → S
  embed : S → World → World

end Lsc
