import Lsc.Security.Invariant
import Lsc.Security.InvariantProof

/-!
Protocol invariants along an attack trace. If each entrypoint and each
environment step the token model allows preserves the invariant, then
the invariant still holds after any well-formed sequence of such steps.

Token uses the unrestricted form (its invariant is only about its own
storage). Vault and AMM use the form that only assumes preservation on
calls that actually target this contract.
-/

namespace Lsc.Security

/-- If every entrypoint preserves the protocol invariant, and so does every
environment step the token model allows, then the invariant still holds
after any well-formed attack trace. Reverted calls leave the world
unchanged, so they cannot break it. Token uses this to carry "balances
sum to supply" from a single transaction to a whole attack. -/
theorem inv_run [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop} {rely : X → X → Prop}
    (hC : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) {self : Address} (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run hC hE hw tr hW hR

/-- Same conclusion as `inv_run`, but the invariant is only assumed to
survive calls that target this contract with a distinct sender. Vault and
AMM need this because their invariant mentions this contract's token
balance, which cannot be claimed for a call to some other address. -/
theorem inv_run_at [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop} {rely : X → X → Prop}
    {self : Address}
    (hC : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run_at hC hE hw tr hW hR

/-- `PreservesInv` follows from the per-entrypoint form. Non-payable
contracts need no credit obligation: nonzero value is a revert step,
and `creditValue w 0 = w`. -/
theorem PreservesInv.of_fns [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop}
    (h : ∀ fn, PreservesInvFn C Inv fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    PreservesInv C Inv :=
  Proof.PreservesInv.of_fns h hnp

/-- Reduce `PreservesInvFn` to the success path: a revert leaves the world unchanged. -/
theorem PreservesInvFn_of_ok {C : Spec S X E ε} {Inv : World S X E → Prop} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (a, w') → Inv w') :
    PreservesInvFn C Inv fn :=
  Proof.PreservesInvFn_of_ok hok

/-- `PreservesInv` for contracts that may have payable entrypoints.
Each unpacked obligation is judged on the post-transfer world. -/
theorem PreservesInv.of_fns_credit [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop}
    (h : ∀ fn, PreservesInvCreditFn C Inv fn) :
    PreservesInv C Inv :=
  Proof.PreservesInv.of_fns_credit h

/-- `PreservesInvAt` follows from the per-entrypoint form at `self`.
Non-payable contracts need no credit obligation. -/
theorem PreservesInvAt.of_fns [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop}
    {self : Address}
    (h : ∀ fn, PreservesInvFnAt C Inv self fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    PreservesInvAt C Inv self :=
  Proof.PreservesInvAt.of_fns h hnp

/-- `PreservesInvAt` for contracts that may have payable entrypoints. -/
theorem PreservesInvAt.of_fns_credit [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {self : Address}
    (h : ∀ fn, PreservesInvCreditFnAt C Inv self fn) :
    PreservesInvAt C Inv self :=
  Proof.PreservesInvAt.of_fns_credit h

/-- Non-payable `PreservesInvFn` yields the credit form: `valueOk` forces
`value = 0`, so `creditValue` is the identity. -/
theorem PreservesInvCreditFn_of_fn [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {fn : C.Fn}
    (hp : C.payable fn = false)
    (h : PreservesInvFn C Inv fn) :
    PreservesInvCreditFn C Inv fn :=
  Proof.PreservesInvCreditFn_of_fn hp h

/-- Non-payable `PreservesInvFnAt` yields the credit form. -/
theorem PreservesInvCreditFnAt_of_fn [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {self : Address} {fn : C.Fn}
    (hp : C.payable fn = false)
    (h : PreservesInvFnAt C Inv self fn) :
    PreservesInvCreditFnAt C Inv self fn :=
  Proof.PreservesInvCreditFnAt_of_fn hp h

/-- Reduce `PreservesInvFnAt` to the success path: a revert leaves the world unchanged. -/
theorem PreservesInvFnAt_of_ok {C : Spec S X E ε} {Inv : World S X E → Prop}
    {self : Address} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : C.Ret fn)
        (w' : World S X E),
      ctx.self = self → ctx.sender ≠ self → Inv w →
      Tx.run (C.exec fn args) ctx w = .ok (a, w') → Inv w') :
    PreservesInvFnAt C Inv self fn :=
  Proof.PreservesInvFnAt_of_ok hok

end Lsc.Security
