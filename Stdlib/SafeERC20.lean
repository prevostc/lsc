import Stdlib.ERC20
import Lsc.Lang.Inline

/-!
# SafeERC20 — bool-checked IERC20 wrappers

OpenZeppelin-style `safe*` helpers: the CALL must succeed **and** return
`true`; a revert or a `false` return both become `.user err`.

Each wrapper takes the contract's `ε` error value so examples stay readable.
`@[lsc_inline]` lets Reify delta-unfold an applied helper into `call` + `require`.
-/

namespace Lsc.Stdlib

open Lsc

variable {S X E ε : Type} {a : Asset}

/-- Pull `amt` to `to`; revert unless the CALL returns `true`. -/
@[lsc_inline]
def safeTransfer (r : IERC20.Ref a) (to : Address) (amt : Amount a) (err : ε) :
    Tx S X E ε Unit := do
  let ok ← r.transfer to amt
  Tx.require (ok = true) err

/-- Pull `amt` from `src` to `to`; revert unless the CALL returns `true`. -/
@[lsc_inline]
def safeTransferFrom (r : IERC20.Ref a) (src to : Address) (amt : Amount a)
    (err : ε) : Tx S X E ε Unit := do
  let ok ← r.transferFrom src to amt
  Tx.require (ok = true) err

/-- Set `spender`'s allowance to `amt`; revert unless the CALL returns `true`. -/
@[lsc_inline]
def safeApprove (r : IERC20.Ref a) (spender : Address) (amt : Amount a) (err : ε) :
    Tx S X E ε Unit := do
  let ok ← r.approve spender amt
  Tx.require (ok = true) err

@[simp] theorem run_safeTransfer (r : IERC20.Ref a) (to : Address) (amt : Amount a)
    (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransfer (E := E) r to amt err) ctx w =
      match Tx.run (r.transfer to amt) ctx w with
      | .error e => .error e
      | .ok (ok, w') => if ok = true then .ok ((), w') else .error (.user err) := by
  simp [safeTransfer]
  cases Tx.run (r.transfer to amt) ctx w <;> rfl

@[simp] theorem run_safeTransferFrom (r : IERC20.Ref a) (src to : Address)
    (amt : Amount a) (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeTransferFrom (E := E) r src to amt err) ctx w =
      match Tx.run (r.transferFrom src to amt) ctx w with
      | .error e => .error e
      | .ok (ok, w') => if ok = true then .ok ((), w') else .error (.user err) := by
  simp [safeTransferFrom]
  cases Tx.run (r.transferFrom src to amt) ctx w <;> rfl

@[simp] theorem run_safeApprove (r : IERC20.Ref a) (spender : Address)
    (amt : Amount a) (err : ε) (ctx : Ctx) (w : World S X E) :
    Tx.run (safeApprove (E := E) r spender amt err) ctx w =
      match Tx.run (r.approve spender amt) ctx w with
      | .error e => .error e
      | .ok (ok, w') => if ok = true then .ok ((), w') else .error (.user err) := by
  simp [safeApprove]
  cases Tx.run (r.approve spender amt) ctx w <;> rfl

end Lsc.Stdlib
