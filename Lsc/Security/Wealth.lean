import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Invariant

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-! ### Finite sums over `Address → Nat` (Nat is not a group: avoid `sum − x`) -/

/-- Wealth of `a` attributable to this contract: token (or share) units the
protocol owes, plus native value `a` can obtain from `self`. Token-only
contracts leave `native` at 0.

`ExtState.env.balanceOf` exists for every address, but `Oracle.send` and
`env` steps may rewrite it (TRUST 8C-2 does not restore balances). The
native component is therefore the contract-defined redeemable native on
`self`'s books (WETH: wrapped `balances a`), not `ext.env.balanceOf a`.
A `Native.send` to `a` is an authorised outflow exactly when `a` is the
caller and `a`'s book claim falls by the sent amount. -/
structure Claim (S X E : Type) where
  tokens : Address → World S X E → Nat := fun _ _ => 0
  native : Address → World S X E → Nat := fun _ _ => 0

namespace Claim
variable {S X E : Type}

/-- Total claim: `tokens a w + native a w`. Token-only contracts (`native = 0`)
are definitionally the old function. -/
@[coe, reducible] def eval (c : Claim S X E) (a : Address) (w : World S X E) : Nat :=
  c.tokens a w + c.native a w

instance : CoeFun (Claim S X E) (fun _ => Address → World S X E → Nat) where
  coe := eval

/-- Token-only claim; native component is 0. -/
def ofFun (f : Address → World S X E → Nat) : Claim S X E :=
  { tokens := f }

instance : Coe (Address → World S X E → Nat) (Claim S X E) where
  coe := ofFun

/-- Storage-only token claim, as Token uses: `eval a w = c a w.self`. -/
def ofSelf (c : Address → S → Nat) : Claim S X E :=
  ofFun fun a w => c a w.self

/-- Native-only claim from `self`'s books (tokens 0). WETH may use this for
wrapped balances as redeemable native, or keep them in `ofSelf` — not both. -/
def ofNative (c : Address → S → Nat) : Claim S X E :=
  { native := fun a w => c a w.self }

/-- Both components read only `w.self` (ignore `ext` / `log` / oracle). -/
def booksOnly (claim : Claim S X E) : Prop :=
  ∀ (a : Address) (w w' : World S X E),
    w.self = w'.self → claim a w = claim a w'

end Claim

/-- Permission to decrease `claim a`. Evaluated in the **pre-state**. -/
abbrev AuthPred (C : Spec S X E ε) := Address → Call C → World S X E → Prop

/-- Storage-only authorisation: `Auth a c w = A a c w.self`. -/
abbrev AuthPred.ofSelf (A : Address → Call C → S → Prop) : AuthPred C :=
  fun a c w => A a c w.self

/-- Environment steps allowed by `rely` do not decrease `claim`. Automatic
when `claim` depends only on storage (`ClaimMonoEnv.of_self`). -/
def ClaimMonoEnv (claim : Claim S X E) (rely : X → X → Prop) : Prop :=
  ∀ (w : World S X E) (x' : X) (a : Address),
    rely w.ext x' → claim a w ≤ claim a { w with ext := x' }

/-- Incoming `creditValue` does not change `claim` (book-based native). -/
def ClaimMonoCredit [HasCreditValue X] (claim : Claim S X E) : Prop :=
  ∀ (w : World S X E) (v : Nat) (a : Address),
    claim a (World.creditValue w v) = claim a w

/-- A decrease of `claim a` on a call from a world satisfying `Inv` is only possible
when `Auth a` holds in the pre-state. Relative to `Inv`: a pro-rata `claim` is only
monotone under the protocol invariant. -/
def NoUnauthorizedDecrease [HasCreditValue X] (C : Spec S X E ε)
    (Inv : World S X E → Prop)
    (claim : Claim S X E) (Auth : AuthPred C) : Prop :=
  ∀ (c : Call C) (w : World S X E) (a : Address),
    Inv w → claim a (step (.call c) w) < claim a w → Auth a c w

/-- Per-entrypoint form of `NoUnauthorizedDecrease` (unpacked args, no `Call` in the hyp).
Runs on the pre-credit world; non-payable `of_fns` rewrites `step` to `worldAfter`. -/
def NoUnauthorizedDecreaseFn (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S X E) (Auth : AuthPred C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address),
    Inv w →
    claim a (worldAfter (C.exec fn args) ctx w) < claim a w →
    Auth a (Call.ofCtx ctx fn args) w

/-- Unpacked obligation on the success path of `stepCall` (credits then
`Tx.run`). Payable contracts use this with `of_fns_credit`. A revert of
the body cannot decrease `claim` (`stepCall` restores the pre-credit world). -/
def NoUnauthorizedDecreaseCreditFn [HasCreditValue X] (C : Spec S X E ε)
    (Inv : World S X E → Prop) (claim : Claim S X E) (Auth : AuthPred C)
    (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
    (ret : C.Ret fn) (w' : World S X E),
    Inv w →
    Tx.run (C.exec fn args) ctx (World.creditValue w ctx.value) = .ok (ret, w') →
    claim a w' < claim a w →
    Auth a (Call.ofCtx ctx fn args) w

/--
`Auth` is state-dependent (allowance), so the hyp must follow the prefix state.
Environment steps are skipped (`Auth` is only judged at calls).
-/
def NoAuthAlong [HasCreditValue X] (Auth : AuthPred C) (a : Address) :
    List (Step C) → World S X E → Prop
  | [], _ => True
  | .call c :: tr, w => ¬ Auth a c w ∧ NoAuthAlong Auth a tr (step (.call c) w)
  | .env x' :: tr, w => NoAuthAlong Auth a tr { w with ext := x' }

/-! Trace theorems `no_unauthorized_extraction` / `_at` live in `WealthTheorems`. -/

/-! ### Native send: debit of `self` and matching book-claim drop -/

/-- Native balance of the executing account (`HasSelfBalance`). On `ExtState`
this is `World.nativeBalance`. -/
abbrev selfNative [HasSelfBalance X] (w : World S X E) : Nat :=
  HasSelfBalance.get w.ext

/-- Successful `oracle.send` of `v` wei debits `self`'s native balance by `v`.
Not implied by 8C-2 (balances are *not* restored); it is the honest-send
direction a native-holding contract assumes of the same oracle. Self-sends
(`dst = self`) are net-zero in the EVM and fall outside this predicate. -/
def DebitsOnSend [HasSelfBalance X] (o : Oracle X) : Prop :=
  ∀ (dst : Address) (v : Nat) (x x' : X),
    o.send dst v x = some x' → HasSelfBalance.get x' + v = HasSelfBalance.get x

/-- The only address whose claim falls is `dst`, and it falls by `v`.
This is the book-claim half of an authorised `Native.send` (WETH `withdraw`:
burn `v` of `dst`'s wrapped balance). The send itself updates only `ext`. -/
structure NativeOutflow (claim : Claim S X E)
    (dst : Address) (v : Nat) (w w' : World S X E) : Prop where
  drop : claim dst w' + v = claim dst w
  frame : ∀ a, a ≠ dst → claim a w' = claim a w

/-- Authorised native outflow: `self`'s native balance falls by `v` and
`dst`'s claim falls by the same amount (others unchanged). WETH `withdraw`
burns `a`'s wrapped balance then `Native.send`s `a` exactly that much;
`dst` is the caller. -/
structure NativeSendAuth [HasSelfBalance X] (claim : Claim S X E)
    (dst : Address) (v : Nat) (w w' : World S X E)
    extends NativeOutflow claim dst v w w' where
  debit : selfNative w' + v = selfNative w

/-! ### Conservation (local) and solvency -/

/-- Actual inflow of claim-units on this call (0 on revert). -/
abbrev Inflow (C : Spec S X E ε) := Call C → World S X E → Nat

/-- ∃ a touched set `T` closed for `claim`, and `T` conserves up to `inflow`.
Stated from worlds satisfying `Inv` (a pro-rata `claim` is only conservative under `Inv`). -/
def Conservation [HasCreditValue X] (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S X E)
    (inflow : Inflow C) : Prop :=
  ∀ (c : Call C) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T → claim a (step (.call c) w) = claim a w) ∧
      T.sum (fun a => claim a (step (.call c) w)) ≤
        T.sum (fun a => claim a w) + inflow c w

/-- Per-entrypoint form of `Conservation` (unpacked args). -/
def ConservesFn (C : Spec S X E ε) (Inv : World S X E → Prop) (claim : Claim S X E)
    (inflow : Inflow C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T →
        claim a (worldAfter (C.exec fn args) ctx w) = claim a w) ∧
      T.sum (fun a => claim a (worldAfter (C.exec fn args) ctx w)) ≤
        T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w

/-- Assets the contract actually controls, read from storage or the world (oracle). -/
abbrev Holdings (S X E : Type) := Address → World S X E → Nat

/-- `∉ H → claim = 0` (finite support) and `∑_H claim ≤ holdings self`. -/
def Solvent (claim : Claim S X E) (holdings : Holdings S X E) (self : Address)
    (w : World S X E) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → claim a w = 0) ∧
    H.sum (fun a => claim a w) ≤ holdings self w

/-! `solvent_run` / `solvent_run_at` live in `WealthTheorems`. -/

end Lsc.Security
