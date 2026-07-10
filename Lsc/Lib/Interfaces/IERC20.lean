import Lsc.Core.ContractM
import Lsc.Lang.AST

/-!
# `IERC20` interface assumptions for cross-contract proofs

Opt-in trust bundle for standard/honest ERC20 `transfer` behavior — see
[`docs/decisions/0009-ierc20-interface-honest-assumptions.md`](../../../docs/decisions/0009-ierc20-interface-honest-assumptions.md).

Black-box `PairM.exec` alone only proves success vs `ExternalCallFailed`. Balance conservation
requires explicitly trusting a callee via `[HonestERC20 T]`. -/

namespace Lsc.Interfaces

open Lsc Lsc.ContractM

/-- Nominal on-chain ERC20 address for storage fields and Solidity-style `σ.token.transfer(..)`
call sites. Codegen stores the underlying `Address` in one word. -/
structure IERC20 where
  addr : Address := 0
  deriving Repr, Inhabited, DecidableEq

namespace IERC20

def interfaceName : String := "IERC20"

/-- Metadata for one interface method — used by `exec σ.field.method(..)` elaboration. -/
structure MethodSpec where
  params : List (String × Ty)
  retTy : Option Ty := none
  retWords : Nat := 0
  mutating : Bool := true

def methodSpecs : List (String × MethodSpec) := [
  ("transfer", {
    params := [("to", .address), ("amount", .wad)]
    retTy := some .bool
    mutating := true
  }),
  ("balanceOf", {
    params := [("account", .address)]
    retTy := some .wad
    retWords := 1
    mutating := false
  }),
  ("approve", {
    params := [("spender", .address), ("amount", .wad)]
    retTy := some .bool
    mutating := true
  }),
  ("transferFrom", {
    params := [("from", .address), ("to", .address), ("amount", .wad)]
    retTy := some .bool
    mutating := true
  }),
  ("allowance", {
    params := [("owner", .address), ("spender", .address)]
    retTy := some .wad
    retWords := 1
    mutating := false
  }),
]

def lookupMethod (method : String) : Option MethodSpec :=
  methodSpecs.find? (·.1 == method) |>.map (·.2)

def isInterfaceType (e : Lean.Expr) : Bool :=
  e.constName? == some ``IERC20

end IERC20

/-- Minimal abstract ERC20 transfer surface for proof-layer composition. Includes the
allowance triple (`getAllowance`/`approveTyped`/`transferFromTyped`) alongside `transferTyped`/
`getBalance`, since a caller (e.g. a future `CPAMM`) that *pulls* tokens via `transferFrom` needs
the same abstract hook into an unknown callee's allowance bookkeeping that it already has for
balances — mirrors `Token.lean`'s concrete `allowances : Mapping (Address × Address) Amount`
shape one level up, at the interface-spec layer. -/
class IERC20Spec (T : Type) where
  ET : Type
  ErrT : Type
  transferTyped : Address → Wad → ContractM T ET ErrT Unit
  getBalance : T → Address → Wad
  approveTyped : Address → Wad → ContractM T ET ErrT Unit
  transferFromTyped : Address → Address → Wad → ContractM T ET ErrT Unit
  getAllowance : T → Address → Address → Wad

/-- Standard/honest ERC20: successful `transfer` moves `amount` from `msg.sender` to `recipient`
and leaves every other balance unchanged (self-transfer cancels). Narrower than literal ERC20:
excludes fee-on-transfer, rebasing, and callback/reentrancy hooks. -/
class HonestERC20 (T : Type) extends IERC20Spec T where
  transfer_conserves :
    ∀ (recipient sender : Address) (amount : Wad) (ts : ContractState T),
      amount.n ≤ (getBalance ts.storage sender).n →
      (getBalance ts.storage recipient).n + amount.n < 2 ^ 256 →
      ts.context.caller = sender →
      ∃ ts' log, runS (transferTyped recipient amount) ts = .ok ((), ts', log) ∧
        ∀ a : Address,
          getBalance ts'.storage a =
            if a == sender && a == recipient then
              getBalance ts.storage a
            else if a == sender then
              Wad.mkNat ((getBalance ts.storage sender).n - amount.n)
            else if a == recipient then
              Wad.mkNat ((getBalance ts.storage recipient).n + amount.n)
            else
              getBalance ts.storage a
  /-- `approve spender amount` (called by `msg.sender = owner`) sets exactly that allowance,
  leaving every other `(owner, spender)` pair and every balance unchanged. Standard finite-approval
  ERC20 semantics (overwrites, does not add to, any prior allowance). -/
  approve_sets_allowance :
    ∀ (spender : Address) (amount : Wad) (ts : ContractState T),
      ∃ ts' log, runS (approveTyped spender amount) ts = .ok ((), ts', log) ∧
        getAllowance ts'.storage ts.context.caller spender = amount ∧
        (∀ a1 a2 : Address, (a1, a2) ≠ (ts.context.caller, spender) →
          getAllowance ts'.storage a1 a2 = getAllowance ts.storage a1 a2) ∧
        (∀ a : Address, getBalance ts'.storage a = getBalance ts.storage a)
  /-- `transferFrom sender recipient amount` (called by any `msg.sender` with sufficient
  `getAllowance ts sender msg.sender`) moves `amount` from `sender` to `recipient` exactly like
  `transfer_conserves`, and additionally decrements that one `(sender, msg.sender)` allowance by
  `amount`, leaving every other allowance untouched. `sender ≠ recipient` mirrors
  `transfer_conserves`'s implicit self-transfer-cancels case (kept as an explicit hypothesis here
  rather than folded into the conclusion, matching `Token`'s own `runTransferFromOk` shape). -/
  transferFrom_conserves :
    ∀ (sender recipient : Address) (amount : Wad) (ts : ContractState T),
      amount.n ≤ (getAllowance ts.storage sender ts.context.caller).n →
      amount.n ≤ (getBalance ts.storage sender).n →
      (getBalance ts.storage recipient).n + amount.n < 2 ^ 256 →
      sender ≠ recipient →
      ∃ ts' log, runS (transferFromTyped sender recipient amount) ts = .ok ((), ts', log) ∧
        getAllowance ts'.storage sender ts.context.caller =
          Wad.mkNat ((getAllowance ts.storage sender ts.context.caller).n - amount.n) ∧
        getBalance ts'.storage sender = Wad.mkNat ((getBalance ts.storage sender).n - amount.n) ∧
        getBalance ts'.storage recipient =
          Wad.mkNat ((getBalance ts.storage recipient).n + amount.n) ∧
        (∀ a1 a2 : Address, (a1, a2) ≠ (sender, ts.context.caller) →
          getAllowance ts'.storage a1 a2 = getAllowance ts.storage a1 a2) ∧
        (∀ a : Address, a ≠ sender → a ≠ recipient →
          getBalance ts'.storage a = getBalance ts.storage a)

namespace HonestERC20Lemmas

variable {T : Type} [HonestERC20 T]

/-- Pointwise balance law from `transfer_conserves`, packaged for direct use in caller proofs. -/
theorem transfer_ok (recipient sender : Address) (amount : Wad) (ts : ContractState T)
    (hsub : amount.n ≤ (IERC20Spec.getBalance (T := T) ts.storage sender).n)
    (hadd : (IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n < 2 ^ 256)
    (hcaller : ts.context.caller = sender) :
    ∃ ts' log,
      runS (IERC20Spec.transferTyped (T := T) recipient amount) ts = .ok ((), ts', log) ∧
      ∀ a : Address,
        IERC20Spec.getBalance (T := T) ts'.storage a =
          if a == sender && a == recipient then
            IERC20Spec.getBalance (T := T) ts.storage a
          else if a == sender then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage sender).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n)
          else
            IERC20Spec.getBalance (T := T) ts.storage a :=
  HonestERC20.transfer_conserves recipient sender amount ts hsub hadd hcaller

/-- Compose black-box `PairM.exec` with a trusted `HonestERC20.transferTyped` step. -/
theorem exec_transfer_ok {S E Err : Type} [ContractErrors Err]
    (recipient sender : Address) (amount : Wad)
    (es : ContractState S) (ts : ContractState T)
    (hlocked : es.locked = false)
    (hsub : amount.n ≤ (IERC20Spec.getBalance (T := T) ts.storage sender).n)
    (hadd : (IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n < 2 ^ 256)
    (hcaller : ts.context.caller = sender) :
    ∃ ts' : ContractState T,
      PairM.exec (S := S) (T := T) (E := E) (Err := Err)
          (IERC20Spec.transferTyped (T := T) recipient amount) es ts =
        .ok ((), { es with locked := false }, ts', []) ∧
      ∀ a : Address,
        IERC20Spec.getBalance (T := T) ts'.storage a =
          if a == sender && a == recipient then
            IERC20Spec.getBalance (T := T) ts.storage a
          else if a == sender then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage sender).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n)
          else
            IERC20Spec.getBalance (T := T) ts.storage a := by
  obtain ⟨ts', _log, hrun, hbal⟩ := transfer_ok recipient sender amount ts hsub hadd hcaller
  refine ⟨ts', ?_, hbal⟩
  exact PairM.exec_unlocked_ok _ es ts hlocked _ ts' _ hrun

end HonestERC20Lemmas

def interfaceFieldKind? (e : Lean.Expr) : Option String :=
  if IERC20.isInterfaceType e then some IERC20.interfaceName else none

end Lsc.Interfaces
