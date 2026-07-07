import EscrowProofs

/-!
Required `Escrow` theorems (`docs/reference/ESCROW.md`): `release` actually performs the real
black-box cross-contract call into `Token` with the right arguments (updating both contracts'
storage correctly), and a structural non-reentrancy result — stated here as universally
quantified properties (`∀ a : Address`, `∀ owner amount ..`), derived from the Tier-1
characterization lemmas in `EscrowProofs.lean` (`runReleaseOk`/`runTransferOk`), not as
concrete-witness `native_decide` tests. -/

open Lsc Escrow

section Success

/-! ## Success-path properties

Shared across all three: `release recipient amount` succeeds against `es`/`ts`, producing
`es'`/`ts'`/the `Released` log — via `runReleaseOk`. `escrowAddr` is `Escrow`'s own on-chain
address, as `Token` sees it as `msg.sender` (`ts.context.caller`) — see `runReleaseOk`'s
docstring for why this is distinct from the human `owner` who must call `release`. -/

variable (recipient escrowAddr : Address) (amount : Token.Amount)
variable (es : ContractState EscrowStorage) (ts : ContractState Token.TokenStorage)
variable (howner : es.context.caller == es.storage.owner)
variable (hlocked : es.locked = false)
variable (hreleased : es.storage.released.n + amount.n < 2 ^ 256)
variable (hsub : amount.n ≤ (ts.storage.balances escrowAddr).n)
variable (hadd : (ts.storage.balances recipient).n + amount.n < 2 ^ 256)
variable (htokenCaller : ts.context.caller == escrowAddr)

include howner hlocked hreleased hsub hadd htokenCaller in
/-- `release` bumps `Escrow`'s own `released` bookkeeping by exactly `amount`. -/
theorem release_increases_released :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released amount]) ∧
      es'.storage.released.n = es.storage.released.n + amount.n := by
  obtain ⟨es', ts', h, hreleased', _⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h, hreleased'⟩

/-! Four separate, plainly-statable claims about what `release` does to `Token` balances, rather
than one dense `∀ a, if .. then .. else if .. else ..` formula — this is how a human actually
describes it: "it debits the escrow", "it credits the recipient", "it leaves everyone else alone",
and, as a degenerate edge case, "releasing to yourself is a no-op". All four are the same
`∀ a, ..` fact from `runReleaseOk` (`hbal`), just each instantiated/simplified at the one address
(or address class) it's actually talking about. -/

include howner hlocked hreleased hsub hadd htokenCaller in
/-- If the recipient isn't the escrow itself, `release` debits exactly `amount` from the escrow's
own `Token` balance. -/
theorem release_debits_escrow (hne : escrowAddr ≠ recipient) :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released amount]) ∧
      ts'.storage.balances escrowAddr = Wad.mkNat ((ts.storage.balances escrowAddr).n - amount.n) := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h, by simpa [hne] using hbal escrowAddr⟩

include howner hlocked hreleased hsub hadd htokenCaller in
/-- If the recipient isn't the escrow itself, `release` credits exactly `amount` to the
recipient's `Token` balance. -/
theorem release_credits_recipient (hne : escrowAddr ≠ recipient) :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released amount]) ∧
      ts'.storage.balances recipient = Wad.mkNat ((ts.storage.balances recipient).n + amount.n) := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h, by simpa [hne, Ne.symm hne] using hbal recipient⟩

include howner hlocked hreleased hsub hadd htokenCaller in
/-- `release` doesn't touch any `Token` balance other than the escrow's and the recipient's. -/
theorem release_preserves_other_balances (a : Address) (ha1 : a ≠ escrowAddr)
    (ha2 : a ≠ recipient) :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released amount]) ∧
      ts'.storage.balances a = ts.storage.balances a := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h, by simpa [ha1, ha2] using hbal a⟩

include howner hlocked hreleased hsub hadd htokenCaller in
/-- Degenerate edge case: releasing to the escrow's own address leaves its `Token` balance
unchanged (the debit and the credit exactly cancel). -/
theorem release_self_release_is_noop (heq : escrowAddr = recipient) :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released amount]) ∧
      ts'.storage.balances escrowAddr = ts.storage.balances escrowAddr := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h, by simpa [heq] using hbal escrowAddr⟩

include howner hlocked hreleased hsub hadd htokenCaller in
/-- `release` emits exactly one `Released amount` event. -/
theorem release_emits_released :
    ∃ es' ts', ContractM.PairM.run (release recipient amount) es ts =
      .ok ((), es', ts', [EscrowEvent.Released amount]) := by
  obtain ⟨es', ts', h, _, _⟩ :=
    runReleaseOk recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd htokenCaller
  exact ⟨es', ts', h⟩

end Success

/-! ## Error-path properties -/

/-- `release` rejects a non-owner caller with `NotOwner`, before ever touching `Token`'s storage
at all. -/
theorem release_rejects_non_owner (recipient : Address) (amount : Token.Amount)
    (es : ContractState EscrowStorage) (ts : ContractState Token.TokenStorage)
    (h : ¬ es.context.caller == es.storage.owner) :
    ContractM.PairM.run (release recipient amount) es ts = .error EscrowError.NotOwner := by
  simp [release, Stmt.eval, Stmt.evalWith, h]

/-! ### Structural non-reentrancy

`Token.transfer`'s type (`Address → Wad → Lsc.Stmt`, evaluated as `Token.TokenM Unit =
ContractM Token.TokenStorage Token.TokenEvent Token.TokenError Unit`) has no way to mention
`EscrowStorage`/`PairM`/`exec` at all — there is no nested `exec`/`read` a hostile `Token` could
even attempt to write down, so real reentrancy into `Escrow` *during* the callee's execution is
ruled out structurally, by construction, not merely by a runtime guard (see
`Lsc.ContractM.PairM`'s docstring in `Lsc/Core/ContractM.lean`).

The one residual case `exec`'s `locked` flag still guards against — `release` being invoked while
`Escrow`'s own state is *already* `locked` (e.g. via some future, more general dispatch path that
could reenter `Escrow` itself mid-call) — is what this theorem proves directly: nesting a second
call by presenting `release` with an already-`locked` `Escrow` state is unconditionally rejected
with `Reentrant`, regardless of the caller/`Token` state, before `Token`'s storage is ever
touched. -/
theorem release_rejects_when_already_locked (recipient : Address) (amount : Token.Amount)
    (es : ContractState EscrowStorage) (ts : ContractState Token.TokenStorage)
    (howner : es.context.caller == es.storage.owner) (h : es.locked = true) :
    ContractM.PairM.run (release recipient amount) es ts = .error EscrowError.Reentrant := by
  simp [release, Stmt.eval, Stmt.evalWith, howner, h, ContractErrors.fromFramework]
