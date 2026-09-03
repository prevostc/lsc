import Lean

namespace Lsc.Fixed

/-- Where the decimal scale for fixed-point ops comes from.

- `.static d`: `d` is known at elaboration (`Fixed d tag`, `Wad`, `Wei`); scale `10^d` is a
  compile-time constant in IR/codegen.
- `.runtime factor`: scale factor `10^k` is only known when the contract runs (e.g. after
  `Fixed.convert`); lowering emits a generic path without literal fold. -/
inductive ScaleMode where
  | static (decimals : Nat)
  | runtime (factor : Nat)
  deriving Repr, DecidableEq

def ScaleMode.decimals? : ScaleMode → Option Nat
  | .static d => some d
  | .runtime _ => none

def ScaleMode.scaleNat : ScaleMode → Nat
  | .static d => 10 ^ d
  | .runtime factor => factor

def ScaleMode.static? (m : ScaleMode) : Option Nat :=
  match m with
  | .static d => some d
  | .runtime _ => none

def ScaleMode.same (a b : ScaleMode) : Bool :=
  a == b

end Lsc.Fixed
