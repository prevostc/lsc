import Stdlib.ERC20
import Stdlib.SafeERC20

/-!
Slice-1 interface checks: derived selectors, oracle CALL/view/try, a second
interface with a colliding method name, and an `Amount a`/`Amount b` mismatch.
-/

open Lsc Lsc.Stdlib

namespace Stdlib.InterfaceTests

def testToken : Asset := ⟨`testToken, none⟩
def otherToken : Asset := ⟨`otherToken, none⟩

def sel (name : String) : Nat :=
  Interface.selector (I := IERC20 testToken) name

#guard sel "transfer" == 0xa9059cbb
#guard sel "transferFrom" == 0x23b872dd
#guard sel "balanceOf" == 0x70a08231
#guard sel "totalSupply" == 0x18160ddd
#guard sel "allowance" == 0xdd62ed3e
#guard sel "approve" == 0x095ea7b3

structure ToyExt where
  n : Nat := 0
  bal : Nat := 0

def toyOracle : Oracle ToyExt where
  call _addr sel _args ext :=
    if sel == 0xa9059cbb then some ([1], { ext with n := ext.n + 1 })
    else none
  view _addr sel _args ext :=
    if sel == 0x70a08231 then [ext.bal]
    else []

def toyWorld : World Unit ToyExt Unit :=
  { self := (), ext := { n := 0, bal := 7 }, oracle := toyOracle }

def asset : IERC20.Ref testToken := ⟨1⟩

def toyCtx : Ctx := { sender := 1 }

abbrev Run (α : Type) := Except (Err Unit) (α × World Unit ToyExt Unit)

def runTransfer : Run Bool :=
  Tx.run (asset.transfer (2 : Address) (Amount.ofWord 5)) toyCtx toyWorld

def runBalance : Run (Amount testToken) :=
  Tx.run (asset.balanceOf (0 : Address)) toyCtx toyWorld

def rejectWorld : World Unit ToyExt Unit :=
  { self := (), ext := { n := 3, bal := 0 }, oracle := {} }

def runTryReject : Run (Except (Err Unit) Bool) :=
  Tx.run (asset.try.transfer (2 : Address) (Amount.ofWord 5)) toyCtx rejectWorld

def runTransferReject : Run Bool :=
  Tx.run (asset.transfer (2 : Address) (Amount.ofWord 5)) toyCtx rejectWorld

#guard
  (match runTransfer with
    | .ok (true, w') => w'.ext.n == 1 && decide (w'.self = ())
    | _ => false)

#guard
  (match runBalance with
    | .ok (b, w') => b.raw == 7 && w'.ext.n == 0 && w'.ext.bal == 7 && decide (w'.self = ())
    | _ => false)

#guard
  (match runTryReject with
    | .ok (.error .callFailed, w') => w'.ext.n == 3 && decide (w'.self = ())
    | _ => false)

#guard
  (match runTransferReject with
    | .error .callFailed => true
    | _ => false)

/-- A second interface sharing the name `balanceOf` with IERC20. -/
structure IStrategy (want : Asset) where
  balanceOf : View (Amount want)
  deposit : Fn (Amount want → Unit)
  harvest : Fn (Amount want)
  deriving Interface

/-- Both interfaces derive `balanceOf`; the methods live on distinct `Ref` types. -/
example (tok : IERC20.Ref testToken) (s : IStrategy.Ref testToken) :
    Tx Unit ToyExt Unit Empty (Amount testToken) := do
  let _ ← tok.balanceOf (0 : Address)
  s.balanceOf

/-- Explicit spelling on the generated `Ref` structure. -/
example (r : IERC20.Ref testToken) (to : Address) (n : Amount testToken) :
    Tx Unit ToyExt Unit Empty Bool :=
  IERC20.Ref.transfer r to n

/-- `Ref (IERC20 a)` macro, `asset.impl`, and `IERC20.Spec` on a `WorldView`. -/
structure ToyStorage where
  dummy : Nat := 0

example (r : Ref (IERC20 testToken))
    (_hT : IERC20.Spec
      (r.impl : IERC20.Impl testToken (WorldView ToyExt))) : True :=
  trivial

/-- Spec fields are `Option` success (`some`), not `Except.ok`. -/
example (T : IERC20.Impl testToken (WorldView ToyExt))
    (_hT : IERC20.Spec T) (to : Address) (n : Amount testToken)
    (ctx : Ctx) (v v' : WorldView ToyExt)
    (_h : T.transfer to n ctx v = some (true, v')) : True :=
  trivial

example (r : IERC20.Ref testToken) (to : Address) (n : Amount testToken) (err : Unit) :
    Tx Unit ToyExt Unit Unit Unit :=
  safeTransfer r to n err

/--
error: Application type mismatch: The argument
  n
has type
  Amount otherToken
but is expected to have type
  Amount testToken
in the application
  r.transfer 0 n
-/
#guard_msgs in
example (r : IERC20.Ref testToken) (n : Amount otherToken) :
    Tx Unit ToyExt Unit Unit Bool :=
  r.transfer (0 : Address) n

end Stdlib.InterfaceTests
