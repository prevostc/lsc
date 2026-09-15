import Lsc.Lang.Reify
import Stdlib.SafeERC20
import Stdlib.Scales
import Stdlib.Shares

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

inductive Event
  | Dummy
  deriving DecidableEq, Repr

inductive Error
  | TransferFailed
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

def doCheckOk (r : IERC20.Ref testToken) (dst : Address) (amt : Amount testToken) :
    M Unit := do
  let ok ← r.transfer dst amt
  Tx.require (ok = true) .TransferFailed

def doSafeTransfer (r : IERC20.Ref testToken) (dst : Address) (amt : Amount testToken) :
    M Unit :=
  safeTransfer r dst amt .TransferFailed

def doSafeTransferFrom (r : IERC20.Ref testToken) (src dst : Address)
    (amt : Amount testToken) : M Unit :=
  safeTransferFrom r src dst amt .TransferFailed

/-- Compound helper mid-`do`. -/
def doSafeTransferFromMid (r : IERC20.Ref testToken) (src dst : Address)
    (amt : Amount testToken) : M (Amount testToken) := do
  let _ ← r.balanceOf src
  safeTransferFrom r src dst amt .TransferFailed
  r.balanceOf dst

def doSafeApprove (r : IERC20.Ref testToken) (dst : Address) (amt : Amount testToken) :
    M Unit :=
  safeApprove r dst amt .TransferFailed

def doTransfer (r : IERC20.Ref testToken) (dst : Address) (amt : Amount testToken) :
    M Bool :=
  r.transfer dst amt

def doTransferFrom (r : IERC20.Ref testToken) (src dst : Address)
    (amt : Amount testToken) : M Bool :=
  r.transferFrom src dst amt

def doBalanceOf (r : IERC20.Ref testToken) (owner : Address) : M (Amount testToken) :=
  r.balanceOf owner

def doTransferUnit (r : IERC20.Ref testToken) (dst : Address) (amt : Amount testToken) :
    M Unit := do
  let _ ← r.transfer dst amt

def doTransferFromUnit (r : IERC20.Ref testToken) (src dst : Address)
    (amt : Amount testToken) : M Unit := do
  let _ ← r.transferFrom src dst amt

def doMulDown (a x : Fixed 18) : M (Fixed 18) := a *?↓ x
def doMulUp (a x : Fixed 18) : M (Fixed 18) := a *?↑ x
def doDivDown (a x : Fixed 18) : M (Fixed 18) := Fixed.divDown (d := 18) a x
def doDivUp (a x : Fixed 18) : M (Fixed 18) := Fixed.divUp (d := 18) a x
def doRescaleDown (x : Amount testToken) : M (Fixed 6) :=
  Amount.rescale 18 6 .down x
def doRescaleUp (x : Amount testToken) : M (Fixed 6) :=
  Amount.rescale 18 6 .up x
def doPow10 (d : Word) : M Word := Tx.pow10 d
def doAdd (x y : Amount testToken) : M (Amount testToken) := x +? y
def doMulFixed (x : Amount testToken) (r : Wad) : M (Amount testToken) := x *?↓ r
def doQuote (r0 : Amount asset0) (r1 : Amount asset1) (dx : Amount asset0) :
    M (Amount asset1) := do
  let dxF ← dx mulDiv↓ 9970 / 10000
  let den ← r0 +? dxF
  Amount.mulDivDown r1 dxF den

/-- Inline helper returning a pair; consumed by `let (out, dxF) ← …`. -/
@[lsc_inline] def quotePair (r0 : Amount asset0) (r1 : Amount asset1)
    (dx : Amount asset0) : M (Amount asset1 × Amount asset0) := do
  let dxF ← dx mulDiv↓ 9970 / 10000
  let den ← r0 +? dxF
  let out ← Amount.mulDivDown r1 dxF den
  return (out, dxF)

/-- Inline helper returning a triple; consumed by `let (out, fee, dxF) ← …`. -/
@[lsc_inline] def quoteTriple (r0 : Amount asset0) (r1 : Amount asset1)
    (dx : Amount asset0) : M (Amount asset1 × Amount asset0 × Amount asset0) := do
  let dxF ← dx mulDiv↓ 9970 / 10000
  let den ← r0 +? dxF
  let out ← Amount.mulDivDown r1 dxF den
  let fee ← dx -? dxF
  return (out, fee, dxF)

def doQuotePair (r0 : Amount asset0) (r1 : Amount asset1) (dx : Amount asset0) :
    M (Amount asset1) := do
  let (out, dxF) ← quotePair r0 r1 dx
  Amount.mulDivDown out dxF r0

def doQuoteTriple (r0 : Amount asset0) (r1 : Amount asset1) (dx : Amount asset0) :
    M (Amount asset1) := do
  let (out, fee, dxF) ← quoteTriple r0 r1 dx
  let t ← fee +? dxF
  Amount.mulDivDown out t r0

/-- Word-`ite` bound by a pure `let` and consumed by `*?↓`. -/
def doIteCoeff (x : Amount testToken) (ft : Address) (ps : Bps) :
    M (Amount testToken) := do
  let coeff : Bps := if ft = 0 then 0 else ps
  x *?↓ coeff

/-- Same-asset `as` (equal `decimals?`) is a 1:1 retag. -/
def doAs (x : Amount testToken) : M (Amount testToken) := do
  x.as testToken

/-- Cross-scale relabel: `none` vs `some 18`, justified as a compile test. -/
def doAsUnchecked (x : Amount testToken) : M (Amount asset1) := do
  x.asUnchecked asset1

def shareAsset : Asset := ⟨`shareAsset, some 18⟩

/-- Virtual-offset share mint; `1000000` is `10^6` (offset `⟨6⟩`).
`Shares.toShares` is the spec/proof helper; compiling a direct call currently
fails the reification certificate (`simp [toShares, bind_assoc]`), so tests
and examples expand the three binds with a folded literal. -/
def doToShares (assets totalAssets : Amount testToken)
    (totalShares : Amount shareAsset) : M (Amount shareAsset) := do
  let ts' ← Amount.add totalShares (⟨1000000⟩ : Amount shareAsset)
  let ta' ← Amount.add totalAssets (1 : Amount testToken)
  Amount.mulDivDown ts' assets ta'

def doToAssets (shares : Amount shareAsset) (totalAssets : Amount testToken)
    (totalShares : Amount shareAsset) : M (Amount testToken) := do
  let ta' ← Amount.add totalAssets (1 : Amount testToken)
  let ts' ← Amount.add totalShares (⟨1000000⟩ : Amount shareAsset)
  Amount.mulDivDown ta' shares ts'

end StdlibTests

lsc_schema StdlibTests
lsc_reify StdlibTests.doCheckOk StdlibTests.doSafeTransfer StdlibTests.doSafeTransferFrom
  StdlibTests.doSafeApprove
lsc_reify StdlibTests.doTransfer StdlibTests.doTransferFrom StdlibTests.doBalanceOf
  StdlibTests.doTransferUnit StdlibTests.doTransferFromUnit
lsc_reify StdlibTests.doMulDown StdlibTests.doMulUp StdlibTests.doDivDown StdlibTests.doDivUp
lsc_reify StdlibTests.doRescaleDown StdlibTests.doRescaleUp StdlibTests.doPow10
lsc_reify StdlibTests.doAdd StdlibTests.doQuote StdlibTests.doMulFixed
lsc_reify StdlibTests.doSafeTransferFromMid
lsc_reify StdlibTests.doQuotePair StdlibTests.doQuoteTriple
lsc_reify StdlibTests.doIteCoeff
lsc_reify StdlibTests.doAs StdlibTests.doAsUnchecked
lsc_reify StdlibTests.doToShares StdlibTests.doToAssets

#check StdlibTests.doCheckOk.core_denote
#check StdlibTests.doSafeTransfer.core_denote
#check StdlibTests.doSafeTransferFrom.core_denote
#check StdlibTests.doSafeApprove.core_denote
#check StdlibTests.doTransfer.core_denote
#check StdlibTests.doTransferFrom.core_denote
#check StdlibTests.doBalanceOf.core_denote
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
#check StdlibTests.doMulFixed.core_denote
#check StdlibTests.doSafeTransferFromMid.core_denote
#check StdlibTests.doQuotePair.core_denote
#check StdlibTests.doQuoteTriple.core_denote
#check StdlibTests.doIteCoeff.core_denote
#check StdlibTests.doAs.core_denote
#check StdlibTests.doAsUnchecked.core_denote
#check StdlibTests.doToShares.core_denote
#check StdlibTests.doToAssets.core_denote

example : Nat.pow 10 18 = WAD.raw := rfl
example : Nat.pow 10 27 = RAY.raw := rfl
example : Nat.pow 10 6 = USDC_SCALE := rfl
example : Nat.pow 10 4 = BPS.raw := rfl

open Lsc.Syntax

-- Mixed-asset add is a type error.
example : True := by
  fail_if_success
    exact (fun (x : Amount StdlibTests.asset0) (y : Amount StdlibTests.asset1) =>
      (x +? y : StdlibTests.M (Amount StdlibTests.asset0)))
  trivial

-- `*?↓` against a non-fixed amount is a type error.
example : True := by
  fail_if_success
    exact (fun (x : Amount StdlibTests.asset0) (y : Amount StdlibTests.asset1) =>
      (x *?↓ y : StdlibTests.M (Amount StdlibTests.asset0)))
  trivial

-- Swapped quote (`r1 +? dxF`) is a type error.
example : True := by
  fail_if_success
    exact (fun (r1 : Amount StdlibTests.asset1) (dxF : Amount StdlibTests.asset0) =>
      (Amount.mulDivDown r1 dxF (r1 +? dxF) :
        StdlibTests.M (Amount StdlibTests.asset1)))
  trivial

def usdc6 : Lsc.Asset := ⟨`USDC, some 6⟩
def dai18 : Lsc.Asset := ⟨`DAI, some 18⟩
def dynNone : Lsc.Asset := ⟨`dyn, none⟩

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: Amount.as: decimals? must be equal (use asUnchecked)
x : Amount usdc6
⊢ usdc6.decimals? = dai18.decimals?
-/
#guard_msgs in
example (x : Amount usdc6) : Amount dai18 := x.as dai18

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: Amount.as: decimals? must be equal (use asUnchecked)
x : Amount dynNone
⊢ dynNone.decimals? = dai18.decimals?
-/
#guard_msgs in
example (x : Amount dynNone) : Amount dai18 := x.as dai18
