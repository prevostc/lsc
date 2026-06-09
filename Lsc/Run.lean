import Lsc.ContractM
import Lsc.ContractState
import Lsc.World

namespace Lsc

/-- Run a contract function against a typed state value.
    Embeds the state into an empty `World`, applies `f`, then projects back. -/
def runS {E S α : Type} [ContractState S] (f : ContractM E S α) (s : S) :
    Except (ContractError E) (α × S) :=
  match f (ContractState.embed s World.empty) with
  | .ok (v, w') => .ok (v, ContractState.view w')
  | .error e    => .error e

-- Simp lemmas so that `simp [f, runS]` can fully reduce contract `do` blocks.

@[simp] theorem ContractM.pure_apply {E S α : Type} (a : α) (w : World) :
    (pure a : ContractM E S α) w = .ok (a, w) := rfl

@[simp] theorem ContractM.bind_apply {E S α β : Type}
    (m : ContractM E S α) (f : α → ContractM E S β) (w : World) :
    (m >>= f) w = match m w with | .ok (a, w') => f a w' | .error e => .error e := by
  simp only [bind, StateT.bind, Except.bind]
  cases m w with
  | ok p  => simp
  | error e => rfl

end Lsc
