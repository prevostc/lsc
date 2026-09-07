import Lsc.Lang.Reify

/-!
# AmountDemo — unit-typed storage, maps, and returns

Tiny contract used to pin down `Amount` reification: two phantom units, Amount
scalars, an Amount mapping, and functions that `add`/`sub`/`shareDown`,
`read`/`write`, `require`, and `emit`. Certificates must close by `rfl`.
-/

open Lsc Lsc.Syntax

namespace AmountDemo

/-- Phantom marker for a WAD-scaled token. -/
structure DAI where
/-- Phantom marker for a 6-decimal token. -/
structure USDC where

abbrev Dai := Amount DAI WAD
abbrev Usdc := Amount USDC USDC_SCALE

structure Storage where
  dai : Dai
  usdc : Usdc
  balances : Mapping Address Dai

inductive Event
  | Moved (who : Address) (a : Dai)
  deriving DecidableEq, Repr

inductive Error
  | Zero
  | Insufficient
  deriving DecidableEq, Repr

abbrev M := Tx Storage Unit Event Error

/-- View: Amount scalar read. -/
def getDai : M Dai := read dai

/-- View: Amount mapping read. -/
def balanceOf (who : Address) : M Dai := read balances[who]

/-- View: tail `Amount.add`. -/
def addAmt (a b : Dai) : M Dai := Amount.add a b

/-- View: `shareDown` after reading a scalar. -/
def previewShare (a b : Dai) : M Dai := do
  let t ← read dai
  Amount.shareDown a b t

/-- Unit: require, scalar read/write, add, emit. -/
def deposit (a : Dai) : M Unit := do
  Tx.require (0 < a) .Zero
  let t ← read dai
  write dai (← Amount.add t a)
  let who ← Tx.sender
  Tx.emit (.Moved who a)

/-- Unit: sub + mapping write. -/
def credit (a : Dai) : M Unit := do
  Tx.require (0 < a) .Zero
  let who ← Tx.sender
  let b ← read balances[who]
  write balances[who] (← Amount.add b a)
  let t ← read dai
  write dai (← Amount.add t a)
  Tx.emit (.Moved who a)

/-- Unit: sub of a scalar. -/
def withdraw (a : Dai) : M Unit := do
  Tx.require (0 < a) .Zero
  let t ← read dai
  Tx.require (a ≤ t) .Insufficient
  write dai (← Amount.sub t a)

/-- Cross-unit: touch the second scale (no mixed arithmetic). -/
def setUsdc (u : Usdc) : M Unit := write usdc u

end AmountDemo

lsc_schema AmountDemo
lsc_reify AmountDemo.getDai AmountDemo.balanceOf AmountDemo.addAmt AmountDemo.previewShare
lsc_reify AmountDemo.deposit AmountDemo.credit AmountDemo.withdraw AmountDemo.setUsdc
lsc_contract AmountDemo getDai balanceOf addAmt previewShare deposit credit withdraw setUsdc

-- Certificates: `denoteAWord`/`denoteAUnit` with `toNat` on Amount parameters, by `rfl`.
#check AmountDemo.getDai.core_denote
#check AmountDemo.addAmt.core_denote
#check AmountDemo.deposit.core_denote
#check AmountDemo.setUsdc.core_denote
