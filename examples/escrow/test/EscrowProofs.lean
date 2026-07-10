import Escrow
import Lsc.Lib.Interfaces.IERC20

/-!
Proof machinery backing `EscrowTheorem.lean` (`docs/reference/ESCROW.md`).

Escrow calls an external token via inlined `exec SafeERC20.safeTransfer(σ.token, ..)` (spec-faithful
`IERC20.transfer` + explicit `require (ok)`) — proofs characterize `releaseHonest` under
`[HonestERC20 T]`, not any concrete in-repo token. -/

open Lsc Escrow Lsc.Interfaces

def mkEscrowState (owner : Address) (released : EscrowAmount) (token : IERC20)
    (caller : Address := owner) (locked : Bool := false) : ContractState EscrowStorage :=
  { storage := { owner := owner, released := released, token := token }
    context := { caller := caller, callvalue := 0, timestamp := 0, origin := 0 }
    locked := locked }

def requireOwner : ContractM EscrowStorage EscrowEvent EscrowError Unit :=
  fun es =>
    if es.context.caller == es.storage.owner then .ok ((), es, [])
    else .error EscrowError.NotOwner

def bumpReleasedEmit (amount : Wad) : ContractM EscrowStorage EscrowEvent EscrowError Unit :=
  fun es =>
    match Wad.addChecked (⟨es.storage.released.raw⟩ : Wad.Wad) amount with
    | .error ae => .error (ContractErrors.arith ae)
    | .ok w =>
      let amt := Wad.Fixed.retag amount
      .ok ((), { es with storage := { es.storage with released := Wad.Fixed.retag w } },
        [EscrowEvent.Released amt])

/-- Proof-layer mirror of `release`'s control flow for any `[HonestERC20 T]` token. -/
def releaseHonest (T : Type) [HonestERC20 T] (recipient : Address) (amount : Wad) :
    ContractM.PairM EscrowStorage T EscrowEvent EscrowError Unit :=
  ContractM.PairM.liftCaller requireOwner >>= fun _ =>
  ContractM.PairM.exec (IERC20Spec.transferTyped (T := T) recipient amount) >>= fun _ =>
  ContractM.PairM.liftCaller (bumpReleasedEmit amount)

theorem runReleaseOkHonest (T : Type) [HonestERC20 T]
    (recipient escrowAddr : Address) (amount : Wad)
    (es : ContractState EscrowStorage) (ts : ContractState T)
    (howner : es.context.caller == es.storage.owner)
    (hlocked : es.locked = false)
    (hreleased : es.storage.released.n + amount.n < 2 ^ 256)
    (hsub : amount.n ≤ (IERC20Spec.getBalance (T := T) ts.storage escrowAddr).n)
    (hadd : (IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n < 2 ^ 256)
    (htokenCaller : ts.context.caller == escrowAddr) :
    ∃ es' ts',
      ContractM.PairM.run (releaseHonest T recipient amount) es ts =
        Except.ok ((), es', ts', [EscrowEvent.Released (Wad.Fixed.retag amount)]) ∧
      es'.storage.released.n = es.storage.released.n + amount.n ∧
      ∀ a : Address,
        IERC20Spec.getBalance (T := T) ts'.storage a =
          if a == escrowAddr && a == recipient then
            IERC20Spec.getBalance (T := T) ts.storage a
          else if a == escrowAddr then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage escrowAddr).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n)
          else
            IERC20Spec.getBalance (T := T) ts.storage a := by
  have hcallerEq : ts.context.caller = escrowAddr := by simpa using htokenCaller
  obtain ⟨ts', hexecOk, hbal⟩ :=
    HonestERC20Lemmas.exec_transfer_ok (T := T) (S := EscrowStorage) (E := EscrowEvent)
      (Err := EscrowError) recipient escrowAddr amount es ts hlocked hsub hadd hcallerEq
  have haddOk : Wad.addChecked (⟨es.storage.released.raw⟩ : Wad.Wad) amount =
      .ok (Wad.mkNat (es.storage.released.n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hreleased
  simp only [Wad.mkNat] at haddOk
  refine ⟨{ es with storage := { es.storage with released := Wad.mkNat (es.storage.released.n + amount.n) } }, ts', ?_, ?_, ?_⟩
  · simp [releaseHonest, requireOwner, bumpReleasedEmit, ContractM.PairM.bind_apply,
      ContractM.PairM.liftCaller_apply, howner, hlocked, hexecOk, haddOk,
      EscrowStorage.getField, EscrowStorage.setField, Wad.Fixed.retag, Wad.mkNat,
      BitVec.ofNat_toNat]
  · unfold Wad.Fixed.n at *; simp only [Wad.mkNat, BitVec.toNat_ofNat]
    omega
  · exact hbal

theorem release_honest_atomic_on_transfer_failure (T : Type) [HonestERC20 T]
    (recipient : Address) (amount : Wad)
    (es : ContractState EscrowStorage) (ts : ContractState T)
    (howner : es.context.caller == es.storage.owner) (hlocked : es.locked = false)
    {e : IERC20Spec.ErrT T}
    (hcall : (IERC20Spec.transferTyped (T := T) recipient amount) ts = .error e) :
    ContractM.PairM.run (releaseHonest T recipient amount) es ts =
      .error EscrowError.ExternalCallFailed := by
  simp [releaseHonest, requireOwner, bumpReleasedEmit, ContractM.PairM.run,
    ContractM.PairM.bind_apply, ContractM.PairM.liftCaller_apply, ContractM.PairM.exec,
    ContractM.PairM.exec_unlocked_err, ContractM.PairM.bind_exec_err_left,
    howner, hlocked, hcall, ContractErrors.fromFramework]
