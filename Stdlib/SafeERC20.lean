import Stdlib.ERC20

/-!
# SafeERC20 — spec-level bool-checked IERC20 wrappers

OpenZeppelin-style `safe*` helpers: a successful CALL whose returned word is `0`
(`false`) reverts, and a failed CALL already reverts (`Err.callFailed`). There are
no fee-on-transfer or post-call balance-delta checks.

**Spec-level only; not compilable today.** Reify recognizes `Binding.transfer` /
`Tx.call` as primitives and does not inline user or library `Tx` functions. A
contract that writes `SafeERC20.safeTransfer b dst amt` is outside the reifiable
fragment until Reify inlines library calls (or grows a `checkOk` primitive).
Compiled code uses `Binding.transferUnit` / `transferFromUnit` instead (call
failure reverts; this IERC20 may-model never returns `0`, only `none` →
`callFailed`).

`safeApprove` uses the same `checkOk` shape. This IERC20 has no `approve` method
(allowances are not ghosted; `transferFrom` ignores them), so the wrapper takes
any `Tx … Nat` call — pass `Binding.approve` once that method exists.
-/

namespace Lsc.Binding

open Lsc Lsc.Stdlib

variable {S X E ε : Type}

/-- Revert on `false` (`0`) after a successful CALL; keep `callFailed` on fault/`none`. -/
def checkOk (x : Tx S X E ε Nat) : Tx S X E ε Unit :=
  fun ctx w =>
    match Tx.run x ctx w with
    | .error e => .error e
    | .ok (ok, w') => if ok = 0 then .error .callFailed else .ok ((), w')

/-- Spec-level only; compilable once Reify inlines library calls. -/
def safeTransfer (b : Binding IERC20 S X) (dst : Address) (amt : Nat) : Tx S X E ε Unit :=
  checkOk (transfer b dst amt)

/-- Spec-level only; compilable once Reify inlines library calls. -/
def safeTransferFrom (b : Binding IERC20 S X) (src dst : Address) (amt : Nat) :
    Tx S X E ε Unit :=
  checkOk (transferFrom b src dst amt)

/-- Spec-level only. Same bool-check as `safeTransfer`; `x` is the approve-shaped
CALL (`Binding.approve` when that method exists). -/
def safeApprove (x : Tx S X E ε Nat) : Tx S X E ε Unit :=
  checkOk x

@[simp] theorem run_checkOk (x : Tx S X E ε Nat) (ctx : Ctx) (w : World S X E) :
    Tx.run (checkOk (ε := ε) x) ctx w =
      match Tx.run x ctx w with
      | .error e => .error e
      | .ok (ok, w') => if ok = 0 then .error .callFailed else .ok ((), w') :=
  rfl

@[simp] theorem run_safeTransfer (b : Binding IERC20 S X) (dst : Address) (amt : Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransfer (E := E) (ε := ε) b dst amt) ctx w =
      Tx.run (checkOk (ε := ε) (transfer b dst amt)) ctx w :=
  rfl

@[simp] theorem run_safeTransferFrom (b : Binding IERC20 S X) (src dst : Address) (amt : Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransferFrom (E := E) (ε := ε) b src dst amt) ctx w =
      Tx.run (checkOk (ε := ε) (transferFrom b src dst amt)) ctx w :=
  rfl

@[simp] theorem run_safeApprove (x : Tx S X E ε Nat) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeApprove (ε := ε) x) ctx w =
      Tx.run (checkOk (ε := ε) x) ctx w :=
  rfl

end Lsc.Binding
