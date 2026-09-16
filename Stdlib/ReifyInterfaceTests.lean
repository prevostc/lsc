import Lsc.Lang.Reify
import Stdlib.SafeERC20

/-!
Slice-2 reify / `implements` checks: `IERC20.Ref` storage, CALL/view ops,
`C.impl`, and a negative `implements` mismatch.
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Stdlib.ReifyInterfaceTests

def toyAsset : Asset := ⟨`toyAsset, none⟩
def otherAsset : Asset := ⟨`otherAsset, none⟩

structure IHolder (a : Asset) where
  held : View (Amount a)
  pull : Fn (Amount a → Unit)
  deriving Interface

namespace Toy

structure Storage where
  token : Ref (IERC20 toyAsset)
  owner : Address
  deriving Fields

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | TransferFailed
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

def pull (n : Amount toyAsset) : M Unit := do
  let tok ← read token
  safeTransferFrom tok (← Tx.sender) (← Tx.selfAddress) n .TransferFailed
  write owner Tx.sender

def held : M (Amount toyAsset) := do
  let tok ← read token
  tok.balanceOf (← Tx.selfAddress)

end Toy

/-- try-calls are not in the compilable fragment. -/
def doTry (r : IERC20.Ref toyAsset) (to : Address) (n : Amount toyAsset) :
    Toy.M (Except (Err Toy.Error) Bool) :=
  r.try.transfer to n

namespace BadToy

structure Storage where
  token : Ref (IERC20 toyAsset)
  owner : Address
  deriving Fields

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | TransferFailed
  deriving DecidableEq, Repr, Inhabited

abbrev M := Tx Storage ExtState Event Error

def pull (_n : Amount otherAsset) : M Unit := do
  write owner Tx.sender

def held : M (Amount toyAsset) := do
  let tok ← read token
  tok.balanceOf (← Tx.selfAddress)

end BadToy

end Stdlib.ReifyInterfaceTests

open Stdlib.ReifyInterfaceTests

lsc_schema Toy
lsc_contract Toy pull held implements IHolder toyAsset

#check Toy.contract
#check Toy.pull.core_denote
#check Toy.held.core_denote
#check (Toy.impl : IHolder.Impl toyAsset (World Toy.Storage ExtState Toy.Event))
#check (Toy.impl_IHolder :
  IHolder.Impl toyAsset (World Toy.Storage ExtState Toy.Event))

#guard (Toy.pull.core.effects.calls).contains 0x23b872dd
#guard (Toy.held.core.effects.views).contains 0x70a08231
#guard Core.isPureRead Toy.held.core
#guard !Core.isPureRead Toy.pull.core

def tokAddr : Address := 9

def toyOracle : Oracle ExtState where
  call _addr sel _args ext :=
    if sel == 0x23b872dd then some ([1], ext) else none
  view _addr sel _args _ext :=
    if sel == 0x70a08231 then [42] else []

def toyWorld : World Toy.Storage ExtState Toy.Event :=
  { self := { token := ⟨tokAddr⟩, owner := 0 }, ext := default, oracle := toyOracle }

#guard
  (match Tx.run (Toy.pull (Amount.ofWord 3)) { sender := 5, self := 7 } toyWorld with
    | .ok ((), w') => w'.self.owner == 5
    | _ => false)

#guard
  (match Tx.run Toy.held { sender := 5, self := 7 } toyWorld with
    | .ok (a, w') => a.raw == 42 && w'.self.token.addr == tokAddr && w'.self.owner == 0
    | _ => false)

/--
error: reify: try-calls are not compilable yet
-/
#guard_msgs in
lsc_reify Stdlib.ReifyInterfaceTests.doTry

lsc_schema BadToy

/--
error: implements IHolder: method `pull` argument 0 has type
  Amount toyAsset
but `Stdlib.ReifyInterfaceTests.BadToy.pull` has
  Amount otherAsset
-/
#guard_msgs in
lsc_contract BadToy pull held implements IHolder toyAsset
