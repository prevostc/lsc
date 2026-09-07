import Lsc.Lang.Reify
import Stdlib.SafeERC20
import Stdlib.Scales

/-!
# Stdlib compile tests — `@[lsc_inline]` helpers as whole functions

Each helper is the entire reified function so `core_denote` stays `rfl`
(Tx bind does not associate definitionally; a helper in the middle of a
`do` block cannot be certified that way).
-/

open Lsc Lsc.Syntax Lsc.Stdlib Stdlib

namespace StdlibTests

structure DAI
structure USDC
abbrev Dai := Amount DAI WAD

structure Storage where
  dummy : Nat
  token : IERC20.Ref

structure Ext where
  token : Ghost

instance : Inhabited Ext := ⟨⟨{}⟩⟩

def tokenB : Binding IERC20 Storage Ext :=
  ⟨(·.token), (·.token), fun x g => { x with token := g }⟩

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage Ext Event Error

def doCheckOk (dst : Address) (amt : Nat) : M Unit :=
  Binding.checkOk (Binding.transfer tokenB dst amt) .TransferFailed

def doSafeTransfer (dst : Address) (amt : Nat) : M Unit :=
  Binding.safeTransfer tokenB dst amt .TransferFailed

def doSafeTransferFrom (src dst : Address) (amt : Nat) : M Unit :=
  Binding.safeTransferFrom tokenB src dst amt .TransferFailed

def doSafeApprove (dst : Address) (amt : Nat) : M Unit :=
  Binding.safeApprove (Binding.transfer tokenB dst amt) .TransferFailed

def doTransfer (dst : Address) (amt : Nat) : M Nat :=
  Binding.transfer tokenB dst amt

def doTransferFrom (src dst : Address) (amt : Nat) : M Nat :=
  Binding.transferFrom tokenB src dst amt

def doBalanceOf (owner : Address) : M Nat :=
  Binding.balanceOf tokenB owner

def doDecimals : M Nat :=
  Binding.decimals tokenB

def doTransferUnit (dst : Address) (amt : Nat) : M Unit :=
  Binding.transferUnit tokenB dst amt

def doTransferFromUnit (src dst : Address) (amt : Nat) : M Unit :=
  Binding.transferFromUnit tokenB src dst amt

def doMulDown (a : Dai) (x : Fixed WAD) : M Dai := Amount.mulDown a x
def doMulUp (a : Dai) (x : Fixed WAD) : M Dai := Amount.mulUp a x
def doDivDown (a : Dai) (x : Fixed WAD) : M Dai := Amount.divDown a x
def doDivUp (a : Dai) (x : Fixed WAD) : M Dai := Amount.divUp a x
def doRatioDown (a b : Dai) : M (Fixed WAD) := Amount.ratioDown a b
def doRatioUp (a b : Dai) : M (Fixed WAD) := Amount.ratioUp a b
def doRescaleDown (a : Dai) : M (Amount DAI USDC_SCALE) :=
  Amount.rescale WAD USDC_SCALE .down a
def doRescaleUp (a : Dai) : M (Amount DAI USDC_SCALE) :=
  Amount.rescale WAD USDC_SCALE .up a
def doConvertDown (p : Price DAI USDC WAD) (a : Dai) : M (Amount USDC WAD) :=
  Amount.convert p WAD .down a
def doConvertUp (p : Price DAI USDC WAD) (a : Dai) : M (Amount USDC WAD) :=
  Amount.convert p WAD .up a

end StdlibTests

lsc_schema StdlibTests
lsc_reify StdlibTests.doCheckOk StdlibTests.doSafeTransfer StdlibTests.doSafeTransferFrom
  StdlibTests.doSafeApprove
lsc_reify StdlibTests.doTransfer StdlibTests.doTransferFrom StdlibTests.doBalanceOf
  StdlibTests.doDecimals StdlibTests.doTransferUnit StdlibTests.doTransferFromUnit
lsc_reify StdlibTests.doMulDown StdlibTests.doMulUp StdlibTests.doDivDown StdlibTests.doDivUp
lsc_reify StdlibTests.doRatioDown StdlibTests.doRatioUp
lsc_reify StdlibTests.doRescaleDown StdlibTests.doRescaleUp
  StdlibTests.doConvertDown StdlibTests.doConvertUp

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
#check StdlibTests.doRatioDown.core_denote
#check StdlibTests.doRatioUp.core_denote
#check StdlibTests.doRescaleDown.core_denote
#check StdlibTests.doRescaleUp.core_denote
#check StdlibTests.doConvertDown.core_denote
#check StdlibTests.doConvertUp.core_denote
