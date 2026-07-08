import Lsc.Prelude
import Lsc.Lang.Syntax

/-!
# Nominal per-token amount tags: cross-token mixing is a compile error

Demonstrates the property `declare_token_amount` (`Lsc/Lib/Wad/Syntax.lean`) exists for: two
tokens' own `Amount`s are genuinely different Lean types, even though both are `Fixed 18 _`, so
passing one where the other is expected at an `exec` call site is rejected at compile time — not
a differently-*named* but interchangeable `abbrev` for the same underlying `Wad`. `TokenA`/
`TokenB` below are two minimal, otherwise-identical 18-decimals tokens; `Caller` is a third
contract that moves funds via `exec`, exactly like `Escrow.release` does for the real `Token` in
`examples/escrow`.
-/

open Lsc Lsc.Deriving

namespace NominalTokenTagTest

namespace TokenA

declare_token_amount Amount

structure TokenAStorage where
  bal : Amount := ⟨0⟩
  deriving ContractStorage

inductive TokenAError where
  | Dummy
  deriving Repr, DecidableEq, ContractError

inductive TokenAEvent where
  | Dummy
  deriving Repr, DecidableEq, ContractEvent

tx setBal(amount : Amount) {
  σ.bal = amount;
}

derive_contract "TokenA" TokenAStorage TokenAError TokenAEvent

end TokenA

namespace TokenB

declare_token_amount Amount

structure TokenBStorage where
  bal : Amount := ⟨0⟩
  deriving ContractStorage

inductive TokenBError where
  | Dummy
  deriving Repr, DecidableEq, ContractError

inductive TokenBEvent where
  | Dummy
  deriving Repr, DecidableEq, ContractEvent

tx setBal(amount : Amount) {
  σ.bal = amount;
}

derive_contract "TokenB" TokenBStorage TokenBError TokenBEvent

end TokenB

namespace Caller

structure CallerStorage where
  dummy : Bool := false
  deriving ContractStorage

inductive CallerError where
  | Dummy
  deriving Repr, DecidableEq, ContractError

inductive CallerEvent where
  | Dummy
  deriving Repr, DecidableEq, ContractEvent

-- Same-token use compiles fine: `TokenA.Amount` in, `exec TokenA.setBal` out.
@nonreentrant
tx moveA(amount : TokenA.Amount) {
  exec TokenA.setBal(amount);
}

derive_contract "Caller" CallerStorage CallerError CallerEvent

-- Positive control: same-token amounts really do compile and really do reach `TokenA` unchanged.
example :
    Except.map (fun x => x.2.2.1.storage.bal)
        (Lsc.ContractM.PairM.run (moveA (Lsc.Wad.mkNat 7))
          { storage := { dummy := false }
            context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
            locked := false }
          { storage := { bal := Lsc.Wad.mkNat 0 }
            context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
            locked := false })
      = .ok (Lsc.Wad.mkNat 7) := by
  native_decide

-- Negative control: the exact same call, but with `TokenB.Amount` in hand instead of
-- `TokenA.Amount`, is a genuine *type* error — not merely a differently-named `abbrev` for the
-- same `Fixed 18 Untagged`, which is exactly the gap this feature closes (see this file's module
-- docstring). `moveA`'s parameter is `TokenA.Amount` (via `TokenA.setBalTyped`'s `.Typed`
-- companion, `resolveExecReadCallee`), so `TokenB.Amount` is rejected at elaboration time.
/--
error: Application type mismatch: The argument
  b
has type
  TokenB.Amount
but is expected to have type
  TokenA.Amount
in the application
  moveA b
-/
#guard_msgs in
example (b : TokenB.Amount) := moveA b

end Caller

end NominalTokenTagTest
