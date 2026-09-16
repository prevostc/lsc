import Lsc.Security.Wealth
import Lsc.Security.WealthProof

/-!
Victim-side wealth, once and for all contracts: nobody can reduce your
protocol claim without your authorisation, and if the invariant already
implies solvency then solvency survives any well-formed attack trace.

Each contract declares what a claim is (token units plus optional native
redeemable from `self`), who may reduce it, and what the contract holds.
Token, Vault, and AMM discharge the local obligations and inherit these
conclusions. Reverted calls are no-ops; between our calls the environment
may change only as the token model allows.
-/

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-- If a protocol never lowers an account's claim except when that account
authorised the call, then on any sequence of calls — any senders, any
arguments, interleaved with environment steps the token model allows — an
account that authorised nothing never sees its claim fall. "Authorised" is
whatever the contract declared: typically the victim sent the call, or an
allowance they granted covers it. Reverted calls leave the world unchanged.
The protocol invariant must hold at the start and survive every entrypoint
and those environment steps. Environment steps must not themselves decrease
the claim (`ClaimMonoEnv`; automatic when `claim` depends only on storage).
Unlike `no_unauthorized_extraction_at`, this form does not require the caller
to differ from the contract, and does not restrict to calls that target this
contract. -/
theorem no_unauthorized_extraction [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.no_unauthorized_extraction hN hP hE hM tr w a hw hR hA

/-- Same victim-side guarantee as `no_unauthorized_extraction`, but the
invariant is only assumed to survive calls that actually target this
contract with a distinct sender. Vault and AMM need this form because
their invariant talks about "our" token balance, which would be
meaningless for a call to some other address; well-formedness (caller ≠
contract) is required here, not on `no_unauthorized_extraction`.
Authorisation is still judged in the pre-state of each call, so allowances
can change along the trace. -/
theorem no_unauthorized_extraction_at [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.no_unauthorized_extraction_at hN hP hE hM tr w a hw hW hR hA

/-- If the protocol invariant already implies the contract does not owe more
than it holds, then after any well-formed attack trace it still doesn't.
Per-step conservation of claims is not required: Vault's floor-rounded
pro-rata shares can leak dust each step, and solvency is the statement
that matters there. The invariant must hold at the start and survive
every entrypoint and every environment step the token model allows. -/
theorem solvent_run [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run hP hE hS hw tr hW hR

/-- Same solvency preservation as `solvent_run`, restricted to traces of
calls that target this contract with a distinct sender. Vault and AMM use
this form because "what the contract holds" is this contract's token
balance, which is only meaningful on calls to this address. -/
theorem solvent_run_at [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run_at hP hE hS hw tr hW hR

/-- Updating a member of a finite support replaces its contribution in the sum. -/
theorem sum_update_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i n) + f i = H.sum f + n :=
  Proof.sum_update_mem H f hi n

/-- Updating a key outside a finite support does not change the sum. -/
theorem sum_update_not_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∉ H) (n : Nat) :
    H.sum (Function.update f i n) = H.sum f :=
  Proof.sum_update_not_mem H f hi n

/-- `Claim.eval` is tokens plus native. -/
@[simp] theorem Claim.eval_apply (c : Claim S X E) (a : Address) (w : World S X E) :
    Claim.eval c a w = c.tokens a w + c.native a w :=
  Proof.Claim.eval_apply c a w

/-- A token-only claim (`ofFun`) evaluates to the given function. -/
@[simp] theorem Claim.eval_ofFun (f : Address → World S X E → Nat)
    (a : Address) (w : World S X E) :
    Claim.ofFun (S := S) (X := X) (E := E) f a w = f a w :=
  Proof.Claim.eval_ofFun f a w

/-- `Claim.ofSelf` ignores `ext` and `log`. -/
@[simp] theorem Claim.eval_ofSelf (c : Address → S → Nat) (a : Address)
    (w : World S X E) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w = c a w.self :=
  Proof.Claim.eval_ofSelf c a w

/-- A native-only claim (`ofNative`) evaluates to the storage book. -/
@[simp] theorem Claim.eval_ofNative (c : Address → S → Nat) (a : Address)
    (w : World S X E) :
    Claim.ofNative (S := S) (X := X) (E := E) c a w = c a w.self :=
  Proof.Claim.eval_ofNative c a w

/-- `Claim.ofSelf` ignores `ext` and `log`. -/
theorem Claim.ofSelf_congr (c : Address → S → Nat)
    {w w' : World S X E} {a : Address} (h : w.self = w'.self) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w =
      Claim.ofSelf (S := S) (X := X) (E := E) c a w' :=
  Proof.Claim.ofSelf_congr c h

/-- Storage-only claims ignore `ext`, so any `rely` is claim-monotone. -/
theorem ClaimMonoEnv.of_self (c : Address → S → Nat) (rely : X → X → Prop) :
    ClaimMonoEnv (Claim.ofSelf (S := S) (X := X) (E := E) c) rely :=
  Proof.ClaimMonoEnv.of_self c rely

/-- Native-book claims ignore `ext`, so any `rely` is claim-monotone. -/
theorem ClaimMonoEnv.of_native (c : Address → S → Nat) (rely : X → X → Prop) :
    ClaimMonoEnv (Claim.ofNative (S := S) (X := X) (E := E) c) rely :=
  Proof.ClaimMonoEnv.of_native c rely

/-- Book-based claims (`tokens` from `self`) ignore `ext`. -/
theorem Claim.booksOnly_ofSelf (c : Address → S → Nat) :
    Claim.booksOnly (Claim.ofSelf (S := S) (X := X) (E := E) c) :=
  Proof.Claim.booksOnly_ofSelf c

/-- Native-book claims ignore `ext`. -/
theorem Claim.booksOnly_ofNative (c : Address → S → Nat) :
    Claim.booksOnly (Claim.ofNative (S := S) (X := X) (E := E) c) :=
  Proof.Claim.booksOnly_ofNative c

/-- Incoming value does not change a book-based claim. -/
theorem ClaimMonoCredit.of_books [HasCreditValue X] {claim : Claim S X E}
    (h : Claim.booksOnly claim) : ClaimMonoCredit claim :=
  Proof.ClaimMonoCredit.of_books h

/-- On `ExtState`, `selfNative` is `World.nativeBalance`. -/
@[simp] theorem selfNative_eq_nativeBalance (w : World S ExtState E) :
    selfNative w = World.nativeBalance w :=
  Proof.selfNative_eq_nativeBalance w

/-- If `claim a` falls across a `NativeOutflow` of `v` to `dst`, the victim is `dst`. -/
theorem native_outflow_victim {claim : Claim S X E} {dst : Address} {v : Nat}
    {w w' : World S X E} {a : Address}
    (h : NativeOutflow claim dst v w w') (hlt : claim a w' < claim a w) :
    a = dst :=
  Proof.native_outflow_victim h hlt

/-- Successful `sendRaw` updates only `ext`. Book-based claims are unchanged. -/
theorem sendRaw_books {claim : Claim S X E} (hB : Claim.booksOnly claim)
    (dst amount : Nat) {ctx : Ctx} {w w' : World S X E} {ok : Bool}
    (h : Tx.run (Tx.sendRaw (ε := ε) dst amount) ctx w =
      .ok (ok, w')) :
    w'.self = w.self ∧ ∀ a, claim a w' = claim a w :=
  Proof.sendRaw_books hB dst amount h

/-- Successful `Native.send` updates only `ext`. Book-based claims are unchanged. -/
theorem native_send_books {claim : Claim S X E} {a : Asset} (hB : Claim.booksOnly claim)
    (dst : Address) (amount : Amount a) (err : ε) {ctx : Ctx} {w w' : World S X E}
    (h : Tx.run (Native.send dst amount err) ctx w = .ok ((), w')) :
    w'.self = w.self ∧ ∀ a, claim a w' = claim a w :=
  Proof.native_send_books hB dst amount err h

/-- If `oracle.send` succeeds and `DebitsOnSend` holds, `self`'s native balance
falls by `v`. -/
theorem sendRaw_debit [HasSelfBalance X] {dst v : Nat} {ctx : Ctx}
    {w w' : World S X E}
    (hO : DebitsOnSend w.oracle)
    (h : Tx.run (Tx.sendRaw (ε := ε) dst v) ctx w = .ok (true, w')) :
    selfNative w' + v = selfNative w :=
  Proof.sendRaw_debit hO h

/-- `DebitsOnSend` plus a matching book-claim drop is `NativeSendAuth`. -/
theorem NativeSendAuth.of_debits [HasSelfBalance X] {claim : Claim S X E}
    {dst : Address} {v : Nat} {w w' : World S X E}
    (hO : DebitsOnSend w.oracle)
    (hsend : w.oracle.send dst v w.ext = some w'.ext)
    (hout : NativeOutflow claim dst v w w') :
    NativeSendAuth claim dst v w w' :=
  Proof.NativeSendAuth.of_debits hO hsend hout

/-- `NoUnauthorizedDecrease` follows from the per-entrypoint form.
Non-payable contracts need no credit obligation. -/
theorem NoUnauthorizedDecrease.of_fns [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C}
    (h : ∀ fn, NoUnauthorizedDecreaseFn C Inv claim Auth fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    NoUnauthorizedDecrease C Inv claim Auth :=
  Proof.NoUnauthorizedDecrease.of_fns h hnp

/-- `NoUnauthorizedDecrease` for contracts that may have payable entrypoints.
Each unpacked obligation is judged on the post-transfer world (`creditValue`
then `Tx.run`), matching `stepCall`. Non-payable + nonzero value is still a
revert step and cannot decrease `claim`. -/
theorem NoUnauthorizedDecrease.of_fns_credit [HasCreditValue X]
    {Inv : World S X E → Prop} {claim : Claim S X E} {Auth : AuthPred C}
    [HasPayable C]
    (h : ∀ fn, NoUnauthorizedDecreaseCreditFn C Inv claim Auth fn) :
    NoUnauthorizedDecrease C Inv claim Auth :=
  Proof.NoUnauthorizedDecrease.of_fns_credit h

/-- Non-payable `NoUnauthorizedDecreaseFn` yields the credit form: `valueOk`
forces `value = 0`, so `creditValue` is the identity. -/
theorem NoUnauthorizedDecreaseCreditFn_of_fn [HasCreditValue X]
    {Inv : World S X E → Prop} {claim : Claim S X E} {Auth : AuthPred C}
    {fn : C.Fn} [HasPayable C] (hp : C.payable fn = false)
    (h : NoUnauthorizedDecreaseFn C Inv claim Auth fn) :
    NoUnauthorizedDecreaseCreditFn C Inv claim Auth fn :=
  Proof.NoUnauthorizedDecreaseCreditFn_of_fn hp h

/-- If every success path is claim-nondecreasing or a `NativeOutflow` to the
caller, and `Auth` holds of the caller, then `fn` does not unauthorisedly
decrease any claim. This is the generic lemma for `Native.send` after a
matching book burn (WETH `withdraw`: burn `v` of `sender`'s wrapped balance,
then send `sender` exactly `v`). -/
theorem NoUnauthorizedDecreaseFn_of_native_send {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C} {fn : C.Fn}
    (hAuth : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
      Auth ctx.sender (Call.ofCtx ctx fn args) w)
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      (∀ a, claim a w ≤ claim a w') ∨
        ∃ v, NativeOutflow claim ctx.sender v w w') :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn :=
  Proof.NoUnauthorizedDecreaseFn_of_native_send hAuth hok

/-- Same as `NoUnauthorizedDecreaseFn_of_native_send`, but `Auth` is judged
on the success path, so tight permission (`amount ≤ balances`) is allowed. -/
theorem NoUnauthorizedDecreaseFn_of_native_send_ok {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C} {fn : C.Fn}
    (hAuth : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      Auth ctx.sender (Call.ofCtx ctx fn args) w)
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      (∀ a, claim a w ≤ claim a w') ∨
        ∃ v, NativeOutflow claim ctx.sender v w w') :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn :=
  Proof.NoUnauthorizedDecreaseFn_of_native_send_ok hAuth hok

/-- Reduce `NoUnauthorizedDecreaseFn` to the success path: a revert cannot decrease `claim`. -/
theorem NoUnauthorizedDecreaseFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      claim a w' < claim a w →
      Auth a (Call.ofCtx ctx fn args) w) :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn :=
  Proof.NoUnauthorizedDecreaseFn_of_ok hok

/-- `Conservation` follows from the per-entrypoint form. Non-payable
contracts need no credit obligation. -/
theorem Conservation.of_fns [HasCreditValue X] [HasPayable C]
    {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C}
    (h : ∀ fn, ConservesFn C Inv claim inflow fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    Conservation C Inv claim inflow :=
  Proof.Conservation.of_fns h hnp

/-- Reduce `ConservesFn` to the success path: a revert is conservation with empty touch-set. -/
theorem ConservesFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (ret : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      ∃ T : Finset Address,
        (∀ a, a ∉ T → claim a w' = claim a w) ∧
        T.sum (fun a => claim a w') ≤
          T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w) :
    ConservesFn C Inv claim inflow fn :=
  Proof.ConservesFn_of_ok hok

/-- `Σ ⌊f a * num / den⌋ ≤ num` when `Σ f = den` and `den > 0`. -/
theorem sum_mul_div_le {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) (num den : Nat)
    (hsum : H.sum f = den) (hpos : 0 < den) :
    H.sum (fun a => f a * num / den) ≤ num :=
  Proof.sum_mul_div_le H f num den hsum hpos

end Lsc.Security
