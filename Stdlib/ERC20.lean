import Lsc.Lang.InterfaceDeriving
import Lsc.Lang.Word

/-!
# IERC20 — ABI signatures and the promises a well-behaved token makes

`IERC20` is the functions you can call. `IERC20.Spec T` is what every
well-behaved ERC20 promises of an implementation `T` (success as hypothesis,
state delta as conclusion). There is no may-model: the callee is the world's
oracle, and a `Spec` hypothesis restricts it.
-/

namespace Lsc.Stdlib

open Lsc

/-- The ERC20 interface: the functions you can call. Field types are the ABI. -/
structure IERC20 (a : Asset) where
  totalSupply  : View (Amount a)
  balanceOf    : View (Address → Amount a)
  allowance    : View (Address → Address → Amount a)
  transfer     : Fn (Address → Amount a → Bool)
  transferFrom : Fn (Address → Address → Amount a → Bool)
  approve      : Fn (Address → Amount a → Bool)
  deriving Interface

variable {a : Asset} {W : Type}

/-- What every well-behaved ERC20 promises. -/
structure IERC20.Spec (T : IERC20.Impl a W) : Prop where
  /-- A successful transfer moves `amount` from the sender to `to` and touches
  no one else. -/
  transfer_moves : T.transfer to amount ctx w = some (true, w') →
      T.balanceOf to w' + T.balanceOf ctx.sender w' =
        T.balanceOf to w + T.balanceOf ctx.sender w ∧
      (ctx.sender ≠ to → T.balanceOf to w' = T.balanceOf to w + amount) ∧
      ∀ x, x ≠ ctx.sender → x ≠ to → T.balanceOf x w' = T.balanceOf x w
  /-- Transfers never create or destroy supply. -/
  transfer_supply : T.transfer to amount ctx w = some (r, w') →
      T.totalSupply w' = T.totalSupply w
  /-- A successful `transferFrom` moves `amount` from `src` to `to` and
  touches no one else. -/
  transferFrom_moves : T.transferFrom src to amount ctx w = some (true, w') →
      T.balanceOf to w' + T.balanceOf src w' =
        T.balanceOf to w + T.balanceOf src w ∧
      (src ≠ to → T.balanceOf to w' = T.balanceOf to w + amount) ∧
      ∀ x, x ≠ src → x ≠ to → T.balanceOf x w' = T.balanceOf x w
  /-- `transferFrom` spends `amount` of `src`'s allowance for the sender,
  except when the sender *is* `src` (no allowance is required). -/
  transferFrom_allowance : T.transferFrom src to amount ctx w = some (true, w') →
      ctx.sender ≠ src →
      T.allowance src ctx.sender w' + amount = T.allowance src ctx.sender w
  /-- `approve` sets the allowance. -/
  approve_sets : T.approve spender amount ctx w = some (true, w') →
      T.allowance ctx.sender spender w' = amount
  /-- Nobody can lower your balance except you, or a spender you approved. -/
  balance_protected : T.step ctx w w' → ctx.sender ≠ x →
      T.balanceOf x w' + T.allowance x ctx.sender w ≥ T.balanceOf x w

/-- Exact-transfer token. `IERC20.Spec` already conserves the pair-sum and
leaves `totalSupply` unchanged on transfer; `Exact` names the per-account
deltas and the remaining supply facts. There is no generic finite-support
balance view, so `supply_is_sum` is omitted (that equation lives on the
contract `Inv`). Vault/Cpamm stay on `.toSpec`. -/
class IERC20.Exact {a : Asset} {W : Type} (T : IERC20.Impl a W)
    extends IERC20.Spec T where
  /-- A successful `transfer` subtracts `amount` from the sender and adds it
  to `to` when they differ, and leaves the sender's balance unchanged when
  `from = to`. -/
  transfer_exact : T.transfer to amount ctx w = some (true, w') →
      (ctx.sender ≠ to →
        T.balanceOf ctx.sender w' + amount = T.balanceOf ctx.sender w ∧
        T.balanceOf to w' = T.balanceOf to w + amount) ∧
      (ctx.sender = to → T.balanceOf ctx.sender w' = T.balanceOf ctx.sender w)
  /-- A successful `transfer` changes no balance except sender and `to`. -/
  transfer_others : T.transfer to amount ctx w = some (true, w') →
      ∀ x, x ≠ ctx.sender → x ≠ to → T.balanceOf x w' = T.balanceOf x w
  /-- A successful `transferFrom` subtracts `amount` from `src` and adds it
  to `to` when they differ, and leaves `src`'s balance unchanged when
  `src = to`. -/
  transferFrom_exact : T.transferFrom src to amount ctx w = some (true, w') →
      (src ≠ to →
        T.balanceOf src w' + amount = T.balanceOf src w ∧
        T.balanceOf to w' = T.balanceOf to w + amount) ∧
      (src = to → T.balanceOf src w' = T.balanceOf src w)
  /-- A successful `transferFrom` changes no balance except `src` and `to`. -/
  transferFrom_others : T.transferFrom src to amount ctx w = some (true, w') →
      ∀ x, x ≠ src → x ≠ to → T.balanceOf x w' = T.balanceOf x w
  /-- `transfer` does not change `totalSupply`. -/
  transfer_supply_constant : T.transfer to amount ctx w = some (r, w') →
      T.totalSupply w' = T.totalSupply w
  /-- `transferFrom` does not change `totalSupply`. -/
  transferFrom_supply_constant : T.transferFrom src to amount ctx w = some (r, w') →
      T.totalSupply w' = T.totalSupply w
  /-- `approve` does not change `totalSupply`. -/
  approve_supply_constant : T.approve spender amount ctx w = some (r, w') →
      T.totalSupply w' = T.totalSupply w

end Lsc.Stdlib
