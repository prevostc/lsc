import Lsc.Lang.Tx
import Lsc.Lang.Amount
import Lsc.Lang.Capability
import Lsc.Lang.Inline

/-!
# Chain profile and native-asset primitives

A contract picks one `Chain` (which native asset, if any). `none` means the
chain has no gas token: `Chain.native` and payable/`Native.send` are compile
errors. `Tx.value` is the incoming call value, typed by the inferred asset
(authors use `Chain.native chain`). `Native.send` is a value-carrying CALL
with empty calldata.
-/

namespace Lsc

/-- Chain profile: which native asset (if any) the contract is compiled for. -/
structure Chain where
  native? : Option Asset
  deriving Repr, DecidableEq

/-- Ethereum: 18-decimal ETH. -/
def Chain.ethereum : Chain := ⟨some ⟨`ETH, some 18⟩⟩

/-- The native asset of `c`. Fails to elaborate when `c.native? = none`. -/
def Chain.native (c : Chain) (h : c.native?.isSome := by decide) : Asset :=
  c.native?.get h

namespace Tx

variable {S X E ε : Type}

/-- Incoming call value, typed by asset `a` (the contract's `Chain.native`).
A non-payable function reading value is a type error. -/
def value [Payable] {a : Asset} : Tx S X E ε (Amount a) :=
  Amount.ofWord <$> valueRaw

/-- Native balance of `self`, typed by asset `a`. -/
def selfBalance {a : Asset} [HasSelfBalance X] : Tx S X E ε (Amount a) :=
  Amount.ofWord <$> selfBalanceRaw

end Tx

namespace Native

variable {S X E ε : Type} {a : Asset}

/-- CALL with `amount` wei and empty calldata. Reverts with `err` on failure. -/
@[lsc_inline]
def send (to : Address) (amount : Amount a) (err : ε) : Tx S X E ε Unit := do
  let ok ← Tx.sendRaw to amount.raw
  Tx.require (ok = true) err

namespace «try»

/-- Non-reverting native send. `false` leaves the world unchanged. -/
def send (to : Address) (amount : Amount a) : Tx S X E ε Bool :=
  Tx.sendRaw to amount.raw

end «try»

end Native

end Lsc
