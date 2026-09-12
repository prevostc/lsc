import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Lsc.Lang.Inline
import Lsc.Lang.Interface
import Lsc.Lang.Word

/-!
# IERC20 may-model

Ghost is `balances` + `decimals` (no allowances). `transfer`/`transferFrom` succeed
iff the source balance covers the amount, then `move`. `decimals` is immutable in
the model. `transferFrom` ignores allowances (pull succeeds if `src`'s balance covers
and the call is not faulted).
-/

namespace Lsc.Stdlib

open Lsc

structure Ghost where
  balances : Address → Nat := fun _ => 0
  decimals : Nat := 18

instance : Inhabited Ghost := ⟨{}⟩

inductive Method
  | transfer
  | transferFrom
  | balanceOf
  | decimals
  deriving DecidableEq, Repr

def move (g : Ghost) (src dst : Address) (amt : Nat) : Ghost :=
  if src = dst then g
  else
    { g with
      balances :=
        Function.update
          (Function.update g.balances src (g.balances src - amt))
          dst (g.balances dst + amt) }

def model : Method → Address → List Nat → Ghost → Option (Nat × Ghost)
  | .transfer, self, [dst, amt], g =>
      if amt ≤ g.balances self then some (1, move g self dst amt) else none
  | .transferFrom, _, [src, dst, amt], g =>
      if amt ≤ g.balances src then some (1, move g src dst amt) else none
  | .balanceOf, _, [owner], g => some (g.balances owner, g)
  | .decimals, _, [], g => some (g.decimals, g)
  | _, _, _, _ => none

/-- Between our calls: our balance is non-decreasing and `decimals` is fixed. -/
def Rely (self : Address) (g g' : Ghost) : Prop :=
  g.balances self ≤ g'.balances self ∧ g'.decimals = g.decimals

def Method.toFin : Method → Fin 4
  | .transfer => ⟨0, by decide⟩
  | .transferFrom => ⟨1, by decide⟩
  | .balanceOf => ⟨2, by decide⟩
  | .decimals => ⟨3, by decide⟩

def Method.ofFin : Fin 4 → Method
  | ⟨0, _⟩ => .transfer
  | ⟨1, _⟩ => .transferFrom
  | ⟨2, _⟩ => .balanceOf
  | ⟨3, _⟩ => .decimals

def Method.equivFin : Method ≃ Fin 4 where
  toFun := Method.toFin
  invFun := Method.ofFin
  left_inv := by intro m; cases m <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def IERC20 : Interface where
  Ghost := Ghost
  Method := Method
  n := 4
  model := model
  abi
    | .transfer => ⟨0xa9059cbb, 2, .boolOpt⟩
    | .transferFrom => ⟨0x23b872dd, 3, .boolOpt⟩
    | .balanceOf => ⟨0x70a08231, 1, .word⟩
    | .decimals => ⟨0x313ce567, 0, .word⟩
  idx := Method.equivFin

/-- Solidity-style persistent layout (`vaultAbsSolidity`): `balances[o]` at mapping
slot 0 (`keccak(abi.encode(o, 0))`); `decimals` at scalar slot 1. -/
def IERC20.balancesMappingSlot : Nat := 0
def IERC20.decimalsSlot : Nat := 1

/-- Field type of a bound token, indexed by the asset it denominates.
A one-field structure (`Ref`) so `Ref IERC20 token0` and `Ref IERC20 token1`
do not unify. -/
abbrev IERC20.Ref (a : Asset) : Type := Lsc.Ref IERC20 a

@[simp] theorem IERC20.model_eq : IERC20.model = model := rfl

theorem IERC20.abi_selector_inj {m₁ m₂ : Method}
    (h : (IERC20.abi m₁).selector = (IERC20.abi m₂).selector) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | cases h

theorem IERC20.abi_ret_transfer : (IERC20.abi .transfer).ret = .boolOpt := rfl
theorem IERC20.abi_ret_transferFrom : (IERC20.abi .transferFrom).ret = .boolOpt := rfl
theorem IERC20.abi_sel_lt (m : Method) : (IERC20.abi m).selector < 2 ^ 32 := by
  cases m <;> decide

theorem IERC20.abi_arity_le_3 (m : Method) : (IERC20.abi m).arity ≤ 3 := by
  cases m <;> decide

end Lsc.Stdlib

namespace Lsc.Binding

open Lsc.Stdlib

variable {S X E ε : Type} {a : Asset}

@[lsc_inline]
def transfer (b : Binding IERC20 S X) (dst : Address) (amt : Amount a) : Tx S X E ε Nat :=
  Tx.call b .transfer [dst, amt.raw]

@[lsc_inline]
def transferFrom (b : Binding IERC20 S X) (src dst : Address) (amt : Amount a) : Tx S X E ε Nat :=
  Tx.call b .transferFrom [src, dst, amt.raw]

@[lsc_inline]
def balanceOf (b : Binding IERC20 S X) (owner : Address) : Tx S X E ε (Amount a) :=
  Amount.ofWord <$> Tx.call b .balanceOf [owner]

@[lsc_inline]
def decimals (b : Binding IERC20 S X) : Tx S X E ε Word :=
  Tx.call b .decimals []

@[lsc_inline]
def transferUnit (b : Binding IERC20 S X) (dst : Address) (amt : Amount a) : Tx S X E ε Unit :=
  Tx.callUnit b .transfer [dst, amt.raw]

@[lsc_inline]
def transferFromUnit (b : Binding IERC20 S X) (src dst : Address) (amt : Amount a) : Tx S X E ε Unit :=
  Tx.callUnit b .transferFrom [src, dst, amt.raw]

@[simp] theorem run_transfer (b : Binding IERC20 S X) (dst : Address) (amt : Amount a)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (transfer (E := E) (ε := ε) b dst amt) ctx w =
      Tx.run (Tx.call (I := IERC20) (E := E) (ε := ε) b .transfer [dst, amt.raw]) ctx w :=
  rfl

@[simp] theorem run_transferFrom (b : Binding IERC20 S X) (src dst : Address) (amt : Amount a)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (transferFrom (E := E) (ε := ε) b src dst amt) ctx w =
      Tx.run (Tx.call (I := IERC20) (E := E) (ε := ε) b .transferFrom
        [src, dst, amt.raw]) ctx w :=
  rfl

@[simp] theorem run_balanceOf (b : Binding IERC20 S X) (owner : Address)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (balanceOf (a := a) (E := E) (ε := ε) b owner) ctx w =
      Tx.run (Amount.ofWord (a := a) <$>
        Tx.call (I := IERC20) (E := E) (ε := ε) b .balanceOf [owner]) ctx w :=
  rfl

@[simp] theorem run_decimals (b : Binding IERC20 S X) (ctx : Ctx) (w : World S X E) :
    Tx.run (decimals (E := E) (ε := ε) b) ctx w =
      Tx.run (Tx.call (I := IERC20) (E := E) (ε := ε) b .decimals []) ctx w :=
  rfl

@[simp] theorem run_transferUnit (b : Binding IERC20 S X) (dst : Address) (amt : Amount a)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (transferUnit (E := E) (ε := ε) b dst amt) ctx w =
      Tx.run (Tx.callUnit (I := IERC20) (E := E) (ε := ε) b .transfer
        [dst, amt.raw]) ctx w :=
  rfl

@[simp] theorem transferUnit_run (b : Binding IERC20 S X) (dst : Address) (amt : Amount a)
    (ctx : Ctx) (w : World S X E) :
    (transferUnit (E := E) (ε := ε) b dst amt).run ctx w =
      (Tx.callUnit (I := IERC20) (E := E) (ε := ε) b .transfer [dst, amt.raw]).run
        ctx w :=
  rfl

@[simp] theorem run_transferFromUnit (b : Binding IERC20 S X) (src dst : Address)
    (amt : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (transferFromUnit (E := E) (ε := ε) b src dst amt) ctx w =
      Tx.run (Tx.callUnit (I := IERC20) (E := E) (ε := ε) b .transferFrom
        [src, dst, amt.raw]) ctx w :=
  rfl

@[simp] theorem transferFromUnit_run (b : Binding IERC20 S X) (src dst : Address)
    (amt : Amount a) (ctx : Ctx) (w : World S X E) :
    (transferFromUnit (E := E) (ε := ε) b src dst amt).run ctx w =
      (Tx.callUnit (I := IERC20) (E := E) (ε := ε) b .transferFrom
        [src, dst, amt.raw]).run ctx w :=
  rfl

end Lsc.Binding

namespace Lsc.Stdlib

theorem move_src {g : Ghost} {src dst : Address} {amt : Nat} (h : src ≠ dst) :
    (move g src dst amt).balances src = g.balances src - amt := by
  simp [move, h]

theorem move_dst {g : Ghost} {src dst : Address} {amt : Nat} (h : src ≠ dst) :
    (move g src dst amt).balances dst = g.balances dst + amt := by
  simp [move, h]

theorem move_other {g : Ghost} {src dst a : Address} {amt : Nat}
    (ha : a ≠ src) (hb : a ≠ dst) :
    (move g src dst amt).balances a = g.balances a := by
  by_cases h : src = dst
  · subst h; simp [move]
  · simp [move, h, Function.update_of_ne hb, Function.update_of_ne ha]

theorem move_decimals (g : Ghost) (src dst : Address) (amt : Nat) :
    (move g src dst amt).decimals = g.decimals := by
  simp [move]
  split_ifs <;> rfl

theorem move_self (g : Ghost) (src : Address) (amt : Nat) :
    move g src src amt = g := by
  simp [move]

theorem model_transfer {src dst amt g} (h : amt ≤ g.balances src) :
    model .transfer src [dst, amt] g = some (1, move g src dst amt) := by
  simp [model, h]

theorem model_transferFrom {callee src dst amt g} (h : amt ≤ g.balances src) :
    model .transferFrom callee [src, dst, amt] g = some (1, move g src dst amt) := by
  simp [model, h]

theorem model_decimals (callee : Address) (g : Ghost) :
    model .decimals callee [] g = some (g.decimals, g) :=
  rfl

theorem model_transfer_none {src dst amt g} (h : ¬ amt ≤ g.balances src) :
    model .transfer src [dst, amt] g = none := by
  simp [model, h]

theorem model_transferFrom_none {callee src dst amt g} (h : ¬ amt ≤ g.balances src) :
    model .transferFrom callee [src, dst, amt] g = none := by
  simp [model, h]

end Lsc.Stdlib
