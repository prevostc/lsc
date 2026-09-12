import Stdlib.ERC20
import Lsc.Lang.Inline

/-!
# SafeERC20 — bool-checked IERC20 wrappers

OpenZeppelin-style `safe*` helpers: "safe" = call fault, revert, **and** a `false`
return word all revert; **nothing** about fee-on-transfer or balance deltas.

Each wrapper takes the contract's `ε` error value so examples stay readable.
`@[lsc_inline]` lets Reify delta-unfold an applied helper into `call` + `require`.

`safeApprove` uses the same `checkOk` shape. This IERC20 has no `approve` method
(allowances are not ghosted; `transferFrom` ignores them), so the wrapper takes
any `Tx … Nat` call — pass `Binding.approve` once that method exists.
-/

namespace Lsc.Binding

open Lsc Lsc.Stdlib

variable {S X E ε : Type} {a : Asset}

/-- Revert on `false` (`0`) after a successful CALL; keep `callFailed` on fault/`none`. -/
@[lsc_inline]
def checkOk (x : Tx S X E ε Nat) (err : ε) : Tx S X E ε Unit := do
  let ok ← x
  Tx.require (ok ≠ 0) err

/-- Pull `amt` to `dst`; revert unless the CALL returns a non-zero word. -/
@[lsc_inline]
def safeTransfer (b : Binding IERC20 S X) (dst : Address) (amt : Amount a) (err : ε) :
    Tx S X E ε Unit :=
  checkOk (transfer b dst amt) err

/-- Pull `amt` from `src` to `dst`; revert unless the CALL returns a non-zero word. -/
@[lsc_inline]
def safeTransferFrom (b : Binding IERC20 S X) (src dst : Address) (amt : Amount a)
    (err : ε) : Tx S X E ε Unit :=
  checkOk (transferFrom b src dst amt) err

/-- Same bool-check as `safeTransfer`; `x` is the approve-shaped CALL. -/
@[lsc_inline]
def safeApprove (x : Tx S X E ε Nat) (err : ε) : Tx S X E ε Unit :=
  checkOk x err

/-- `checkOk` reverts with `.user err` when the CALL returns `0`. -/
@[simp] theorem run_checkOk (x : Tx S X E ε Nat) (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (checkOk x err) ctx w =
      match Tx.run x ctx w with
      | .error e => .error e
      | .ok (ok, w') => if ok = 0 then .error (.user err) else .ok ((), w') := by
  simp [checkOk]
  cases Tx.run x ctx w <;> rfl

@[simp] theorem run_safeTransfer (b : Binding IERC20 S X) (dst : Address) (amt : Amount a)
    (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransfer (E := E) b dst amt err) ctx w =
      Tx.run (checkOk (transfer b dst amt) err) ctx w :=
  rfl

@[simp] theorem run_safeTransferFrom (b : Binding IERC20 S X) (src dst : Address)
    (amt : Amount a) (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransferFrom (E := E) b src dst amt err) ctx w =
      Tx.run (checkOk (transferFrom b src dst amt) err) ctx w :=
  rfl

@[simp] theorem run_safeApprove (x : Tx S X E ε Nat) (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeApprove x err) ctx w =
      Tx.run (checkOk x err) ctx w :=
  rfl

end Lsc.Binding
