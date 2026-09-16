import Lsc.Lang.Interface
import Lsc.Lang.Inline
import Stdlib.ERC20

/-!
# ERC20 base — storage lenses, mint/burn, and the six IERC20 entrypoints

A contract `extends ERC20.Storage a` (or holds a parent lens) and re-exports
the six functions. `mint` / `burn` are `@[internal]` (no access control).
-/

open Lsc Lsc.Syntax

namespace Lsc.Stdlib
namespace ERC20

/-- Token books: balances, nested allowances, recorded supply. -/
structure Storage (a : Asset) where
  balances    : Address ↦ Amount a
  allowances  : Address ↦ Address ↦ Amount a
  totalSupply : Amount a
  deriving Fields, Inhabited

/-- The three storage lenses a token needs; obtained for free from any
`Storage extends ERC20.Storage a`. -/
structure Fields (S : Type) (a : Asset) where
  balances   : Field S (Address ↦ Amount a)
  allowances : Field S (Address ↦ Address ↦ Amount a)
  totalSupply : Field S (Amount a)

/-- Compose a parent `ERC20.Storage` lens into the three field lenses. -/
def Fields.ofParent {S : Type} {a : Asset} (p : Field S (Storage a)) :
    Fields S a where
  balances := Field.comp p Storage.Fields.balances
  allowances := Field.comp p Storage.Fields.allowances
  totalSupply := Field.comp p Storage.Fields.totalSupply

/-- The three lenses are lawful and pairwise independent. Generic ERC20
proofs take this; `deriving Fields` plus `ofParent` synthesise it. -/
class Fields.Lawful {S : Type} {a : Asset} (F : Fields S a) : Prop where
  lawful_balances : Field.Lawful F.balances
  lawful_allowances : Field.Lawful F.allowances
  lawful_totalSupply : Field.Lawful F.totalSupply
  indep_ts_bal : Field.Independent F.totalSupply F.balances
  indep_ts_all : Field.Independent F.totalSupply F.allowances
  indep_bal_all : Field.Independent F.balances F.allowances
  indep_all_bal : Field.Independent F.allowances F.balances
  indep_bal_ts : Field.Independent F.balances F.totalSupply
  indep_all_ts : Field.Independent F.allowances F.totalSupply

attribute [instance] Fields.Lawful.lawful_balances
attribute [instance] Fields.Lawful.lawful_allowances
attribute [instance] Fields.Lawful.lawful_totalSupply
attribute [instance] Fields.Lawful.indep_ts_bal
attribute [instance] Fields.Lawful.indep_ts_all
attribute [instance] Fields.Lawful.indep_bal_all
attribute [instance] Fields.Lawful.indep_all_bal
attribute [instance] Fields.Lawful.indep_bal_ts
attribute [instance] Fields.Lawful.indep_all_ts

instance {S : Type} {a : Asset} {p : Field S (Storage a)} [Field.Lawful p] :
    Fields.Lawful (Fields.ofParent p) where
  lawful_balances :=
    show Field.Lawful (Field.comp p Storage.Fields.balances) from inferInstance
  lawful_allowances :=
    show Field.Lawful (Field.comp p Storage.Fields.allowances) from inferInstance
  lawful_totalSupply :=
    show Field.Lawful (Field.comp p Storage.Fields.totalSupply) from inferInstance
  indep_ts_bal :=
    show Field.Independent (Field.comp p Storage.Fields.totalSupply)
      (Field.comp p Storage.Fields.balances) from inferInstance
  indep_ts_all :=
    show Field.Independent (Field.comp p Storage.Fields.totalSupply)
      (Field.comp p Storage.Fields.allowances) from inferInstance
  indep_bal_all :=
    show Field.Independent (Field.comp p Storage.Fields.balances)
      (Field.comp p Storage.Fields.allowances) from inferInstance
  indep_all_bal :=
    show Field.Independent (Field.comp p Storage.Fields.allowances)
      (Field.comp p Storage.Fields.balances) from inferInstance
  indep_bal_ts :=
    show Field.Independent (Field.comp p Storage.Fields.balances)
      (Field.comp p Storage.Fields.totalSupply) from inferInstance
  indep_all_ts :=
    show Field.Independent (Field.comp p Storage.Fields.allowances)
      (Field.comp p Storage.Fields.totalSupply) from inferInstance

/-- The contract's `Event` type must provide the two ERC-20 events. -/
class Events (E : Type) (a : Asset) where
  transfer : Address → Address → Amount a → E
  approval : Address → Address → Amount a → E

/-- User errors the base reverts with on a failed require. -/
class Errors (ε : Type) where
  insufficientBalance : ε
  insufficientAllowance : ε

variable {S X E ε : Type} {a : Asset}

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer [Events E a] [Errors ε] (F : Fields S a)
    (to : Address) (amount : Amount a) : Tx S X E ε Bool := do
  let src ← Tx.sender
  let b ← read F.balances[src]
  Tx.require (amount ≤ b) Errors.insufficientBalance
  write F.balances[src] (b -? amount)
  write F.balances[to] (read F.balances[to] +? amount)
  Tx.emit (Events.transfer src to amount)
  return true

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve [Events E a] (F : Fields S a)
    (spender : Address) (amount : Amount a) : Tx S X E ε Bool := do
  let owner ← Tx.sender
  write F.allowances[owner, spender] amount
  Tx.emit (Events.approval owner spender amount)
  return true

/-- Move `amount` from `src` to `to`, spending `allowances src sender`.
Self-spend still requires and decrements that allowance. -/
def transferFrom [Events E a] [Errors ε] (F : Fields S a)
    (src to : Address) (amount : Amount a) : Tx S X E ε Bool := do
  let spender ← Tx.sender
  let al ← read F.allowances[src, spender]
  Tx.require (amount ≤ al) Errors.insufficientAllowance
  let b ← read F.balances[src]
  Tx.require (amount ≤ b) Errors.insufficientBalance
  write F.allowances[src, spender] (al -? amount)
  write F.balances[src] (b -? amount)
  write F.balances[to] (read F.balances[to] +? amount)
  Tx.emit (Events.transfer src to amount)
  return true

/-- `who`'s token balance. -/
def balanceOf (F : Fields S a) (who : Address) : Tx S X E ε (Amount a) :=
  read F.balances[who]

/-- Remaining allowance of `spender` over `owner`'s tokens. -/
def allowance (F : Fields S a) (owner spender : Address) :
    Tx S X E ε (Amount a) :=
  read F.allowances[owner, spender]

/-- Recorded total supply. -/
def totalSupply (F : Fields S a) : Tx S X E ε (Amount a) :=
  read F.totalSupply

/-- Credit `amount` to `to` and raise supply. No access control. -/
@[internal] def mint [Events E a] (F : Fields S a) (to : Address)
    (amount : Amount a) : Tx S X E ε Unit := do
  write F.totalSupply (read F.totalSupply +? amount)
  write F.balances[to] (read F.balances[to] +? amount)
  Tx.emit (Events.transfer 0 to amount)

/-- Burn `amount` from `src` and lower supply. No access control. -/
@[internal] def burn [Events E a] [Errors ε] (F : Fields S a)
    (src : Address) (amount : Amount a) : Tx S X E ε Unit := do
  let b ← read F.balances[src]
  if amount ≤ b then
    write F.balances[src] (b -? amount)
    write F.totalSupply (read F.totalSupply -? amount)
  else
    Tx.revert Errors.insufficientBalance
  Tx.emit (Events.transfer src 0 amount)

/-- `IERC20.Impl` whose methods are the base functions at `F`. -/
def impl [Events E a] [Errors ε] (F : Fields S a) :
    IERC20.Impl a (World S X E) where
  totalSupply w := F.totalSupply.get w.self
  balanceOf who w := F.balances.get w.self who
  allowance owner spender w := F.allowances.get w.self owner spender
  transfer to amount ctx w :=
    (Tx.run (ERC20.transfer (ε := ε) F to amount) ctx w).toOption
  transferFrom src to amount ctx w :=
    (Tx.run (ERC20.transferFrom (ε := ε) F src to amount) ctx w).toOption
  approve spender amount ctx w :=
    (Tx.run (ERC20.approve (ε := ε) F spender amount) ctx w).toOption
  step ctx w w' :=
    (∃ to amount r,
      Tx.run (ERC20.transfer (ε := ε) F to amount) ctx w = .ok (r, w')) ∨
    (∃ src to amount r,
      Tx.run (ERC20.transferFrom (ε := ε) F src to amount) ctx w = .ok (r, w')) ∨
    (∃ spender amount r,
      Tx.run (ERC20.approve (ε := ε) F spender amount) ctx w = .ok (r, w')) ∨
    (∃ who r, Tx.run (ERC20.balanceOf (ε := ε) F who) ctx w = .ok (r, w')) ∨
    (∃ owner spender r,
      Tx.run (ERC20.allowance (ε := ε) F owner spender) ctx w = .ok (r, w')) ∨
    (∃ r, Tx.run (ERC20.totalSupply (ε := ε) F) ctx w = .ok (r, w'))

end ERC20
end Lsc.Stdlib
