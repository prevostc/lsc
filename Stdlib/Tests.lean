import Lsc.Lang.Reify
import Stdlib.SafeERC20
import Stdlib.Scales

/-!
# Stdlib compile tests — `@[lsc_inline]` helpers, including mid-`do`

Whole-function helpers still certify (often by `rfl`). `doSafeTransferFromMid`
puts a compound helper between other binds so the certificate must use the
`Tx` monad laws (`bind` is not definitionally associative).
-/

open Lsc Lsc.Syntax Lsc.Stdlib Stdlib

namespace StdlibTests

def testToken : Asset := ⟨`testToken, none⟩
def asset0 : Asset := ⟨`asset0, none⟩
def asset1 : Asset := ⟨`asset1, none⟩

structure Storage where
  dummy : Nat
  token : IERC20.Ref testToken

structure Ext where
  token : Ghost

instance : Inhabited Ext := ⟨⟨{}⟩⟩

def tokenB : Binding IERC20 Storage Ext :=
  ⟨(·.token.addr), (·.token), fun x g => { x with token := g }⟩

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

def doCheckOk (dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.checkOk (Binding.transfer tokenB dst amt) .TransferFailed

def doSafeTransfer (dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.safeTransfer tokenB dst amt .TransferFailed

def doSafeTransferFrom (src dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.safeTransferFrom tokenB src dst amt .TransferFailed

/-- Compound helper mid-`do`. Typechecks; Amount-returning CALL sequences are
not yet in the `lsc_reify` certificate fragment (see `doQuote` for Amount
`mulDiv`/`+?` sequences). -/
def doSafeTransferFromMid (src dst : Address) (amt : Amount testToken) : M (Amount testToken) := do
  let _ ← Binding.balanceOf (a := testToken) tokenB src
  Binding.safeTransferFrom tokenB src dst amt .TransferFailed
  Binding.balanceOf (a := testToken) tokenB dst

def doSafeApprove (dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.safeApprove (Binding.transfer tokenB dst amt) .TransferFailed

def doTransfer (dst : Address) (amt : Amount testToken) : M Nat :=
  Binding.transfer tokenB dst amt

def doTransferFrom (src dst : Address) (amt : Amount testToken) : M Nat :=
  Binding.transferFrom tokenB src dst amt

def doBalanceOf (owner : Address) : M (Amount testToken) :=
  Binding.balanceOf (a := testToken) tokenB owner

def doDecimals : M Word :=
  Binding.decimals tokenB

def doTransferUnit (dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.transferUnit tokenB dst amt

def doTransferFromUnit (src dst : Address) (amt : Amount testToken) : M Unit :=
  Binding.transferFromUnit tokenB src dst amt

def doMulDown (a x : Fixed 18) : M (Fixed 18) := Fixed.mulDown (d := 18) a x
def doMulUp (a x : Fixed 18) : M (Fixed 18) := Fixed.mulUp (d := 18) a x
def doDivDown (a x : Fixed 18) : M (Fixed 18) := Fixed.divDown (d := 18) a x
def doDivUp (a x : Fixed 18) : M (Fixed 18) := Fixed.divUp (d := 18) a x
def doRescaleDown (x : Amount testToken) : M (Fixed 6) :=
  Amount.rescale 18 6 .down x
def doRescaleUp (x : Amount testToken) : M (Fixed 6) :=
  Amount.rescale 18 6 .up x
def doPow10 (d : Word) : M Word := Tx.pow10 d
def doAdd (x y : Amount testToken) : M (Amount testToken) := x +? y
def doQuote (r0 : Amount asset0) (r1 : Amount asset1) (dx : Amount asset0) :
    M (Amount asset1) := do
  let dxF ← Amount.mulDivDown dx (Amount.ofWord (a := asset0) 9970)
    (Amount.ofWord (a := asset0) 10000)
  let den ← r0 +? dxF
  Amount.mulDivDown r1 dxF den

end StdlibTests

lsc_schema StdlibTests
lsc_reify StdlibTests.doCheckOk StdlibTests.doSafeTransfer StdlibTests.doSafeTransferFrom
  StdlibTests.doSafeApprove
lsc_reify StdlibTests.doTransfer StdlibTests.doTransferFrom StdlibTests.doBalanceOf
  StdlibTests.doDecimals StdlibTests.doTransferUnit StdlibTests.doTransferFromUnit
lsc_reify StdlibTests.doMulDown StdlibTests.doMulUp StdlibTests.doDivDown StdlibTests.doDivUp
lsc_reify StdlibTests.doRescaleDown StdlibTests.doRescaleUp StdlibTests.doPow10
lsc_reify StdlibTests.doAdd StdlibTests.doQuote

#check StdlibTests.doCheckOk.core_denote
#check StdlibTests.doSafeTransfer.core_denote
#check StdlibTests.doSafeTransferFrom.core_denote
#check StdlibTests.doSafeApprove.core_denote
#check StdlibTests.doTransfer.core_denote
#check StdlibTests.doTransferFrom.core_denote
#check StdlibTests.doBalanceOf.core_denote
#check StdlibTests.doDecimals.core_denote
#check StdlibTests.doTransferUnit.core_denote
#check StdlibTests.doTransferFromUnit.core_denote
#check StdlibTests.doMulDown.core_denote
#check StdlibTests.doMulUp.core_denote
#check StdlibTests.doDivDown.core_denote
#check StdlibTests.doDivUp.core_denote
#check StdlibTests.doRescaleDown.core_denote
#check StdlibTests.doRescaleUp.core_denote
#check StdlibTests.doPow10.core_denote
#check StdlibTests.doAdd.core_denote
#check StdlibTests.doQuote.core_denote

example : Nat.pow 10 18 = WAD := rfl
example : Nat.pow 10 27 = RAY := rfl
example : Nat.pow 10 6 = USDC_SCALE := rfl

open Lsc.Syntax

-- Mixed-asset add is a type error.
example : True := by
  fail_if_success
    exact (fun (x : Amount StdlibTests.asset0) (y : Amount StdlibTests.asset1) =>
      (x +? y : StdlibTests.M (Amount StdlibTests.asset0)))
  trivial

-- Swapped quote (`r1 +? dxF`) is a type error.
example : True := by
  fail_if_success
    exact (fun (r1 : Amount StdlibTests.asset1) (dxF : Amount StdlibTests.asset0) =>
      (Amount.mulDivDown r1 dxF (r1 +? dxF) :
        StdlibTests.M (Amount StdlibTests.asset1)))
  trivial
