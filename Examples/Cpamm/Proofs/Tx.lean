import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Examples.Cpamm.Spec
import Examples.Cpamm.Proofs.Math
import Examples.Cpamm.Proofs.SwapOut
import Stdlib.SafeERC20
import Lsc.Lang.TxTheorems
import Lsc.Lang.AmountTheorems
import Lsc.Lang.WordTheorems
import Lsc.Lang.InterfaceTheorems
import Lsc.Security.Wealth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-!
CPAMM `Tx.run` lemmas. External CALLs are opaque; success lemmas recover
storage, logs, and the oracle, and use `IERC20.Spec` for holdings.
-/

open Lsc Lsc.Syntax Lsc.Stdlib Lsc.Security Cpamm Stdlib

attribute [local simp] Amount.eq_iff Amount.ne_iff Amount.lt_iff Amount.le_iff

namespace Cpamm

variable {ctx : Ctx} {w : World Storage ExtState Event}

abbrev tfCall {a : Asset} (r : IERC20.Ref a) (src dst : Address)
    (amt : Amount a) : Tx Storage ExtState Event Error Bool :=
  r.transferFrom src dst amt

abbrev trCall {a : Asset} (r : IERC20.Ref a) (dst : Address)
    (amt : Amount a) : Tx Storage ExtState Event Error Bool :=
  r.transfer dst amt

/-- Shares `addLiquidity` mints from `σ` (the floor-min; first mint is `a0`). -/
def mintedShares (σ : Storage) (a0 a1 : Nat) : Nat :=
  if σ.totalShares.raw = 0 then a0
  else if σ.totalShares.raw * a0 / σ.reserve0.raw ≤
      σ.totalShares.raw * a1 / σ.reserve1.raw then
    σ.totalShares.raw * a0 / σ.reserve0.raw
  else
    σ.totalShares.raw * a1 / σ.reserve1.raw

/-- Storage after a successful `addLiquidity` by `who`. -/
def addLiquidityPost (σ : Storage) (who : Address) (a0 a1 : Nat) : Storage :=
  let n := mintedShares σ a0 a1
  { σ with
    reserve0 := σ.reserve0 + Amount.ofWord a0
    reserve1 := σ.reserve1 + Amount.ofWord a1
    totalShares := Amount.ofWord n + σ.totalShares
    shares := Function.update σ.shares who (Amount.ofWord n + σ.shares who) }

/-- Floor-pro-rata redemption of `s` shares. -/
def redeemed (σ : Storage) (s : Nat) : Nat × Nat :=
  (σ.reserve0.raw * s / σ.totalShares.raw, σ.reserve1.raw * s / σ.totalShares.raw)

/-- Storage after a successful `removeLiquidity` by `who`. -/
def removeLiquidityPost (σ : Storage) (who : Address) (s : Nat) : Storage :=
  let out := redeemed σ s
  { σ with
    reserve0 := σ.reserve0 - Amount.ofWord out.1
    reserve1 := σ.reserve1 - Amount.ofWord out.2
    totalShares := σ.totalShares - Amount.ofWord s
    shares := Function.update σ.shares who (σ.shares who - Amount.ofWord s) }

def amountOut (rIn rOut dx : Nat) : Nat := amountOutF rIn rOut dx

def coeffOf (σ : Storage) : Nat :=
  if (σ.feeTo : Nat) = 0 then 0 else σ.protocolShareBps.raw

def protoOf (σ : Storage) (dx : Nat) : Nat :=
  if (σ.feeTo : Nat) = 0 then 0
  else swapFee dx * σ.protocolShareBps.raw / BPS.raw

/-- Storage after a successful `swap0for1`. -/
def swap0Post (σ : Storage) (dx proto out : Nat) : Storage :=
  { σ with
    reserve0 := σ.reserve0 + Amount.ofWord (dx - proto)
    reserve1 := σ.reserve1 - Amount.ofWord out
    protocolFees0 := σ.protocolFees0 + Amount.ofWord proto }

/-- Storage after a successful `swap1for0`. -/
def swap1Post (σ : Storage) (dx proto out : Nat) : Storage :=
  { σ with
    reserve1 := σ.reserve1 + Amount.ofWord (dx - proto)
    reserve0 := σ.reserve0 - Amount.ofWord out
    protocolFees1 := σ.protocolFees1 + Amount.ofWord proto }

def collectPost (σ : Storage) : Storage :=
  { σ with protocolFees0 := 0, protocolFees1 := 0 }

theorem protoOf_eq_take (σ : Storage) (dx : Nat) :
    protoOf σ dx = protoTake σ.feeTo σ.protocolShareBps.raw (swapFee dx) :=
  rfl

theorem protoOf_of_eq {σ : Storage} {dx : Nat} (h : σ.feeTo = 0) :
    protoOf σ dx = 0 := by
  have h' : (σ.feeTo : Nat) = 0 := h
  unfold protoOf; rw [if_pos h']

theorem protoOf_of_ne {σ : Storage} {dx : Nat} (h : σ.feeTo ≠ 0) :
    protoOf σ dx = swapFee dx * σ.protocolShareBps.raw / BPS.raw := by
  have h' : ¬ (σ.feeTo : Nat) = 0 := h
  unfold protoOf; rw [if_neg h']

theorem coeffOf_of_eq {σ : Storage} (h : σ.feeTo = 0) : coeffOf σ = 0 := by
  have h' : (σ.feeTo : Nat) = 0 := h
  unfold coeffOf; rw [if_pos h']

theorem coeffOf_of_ne {σ : Storage} (h : σ.feeTo ≠ 0) :
    coeffOf σ = σ.protocolShareBps.raw := by
  have h' : ¬ (σ.feeTo : Nat) = 0 := h
  unfold coeffOf; rw [if_neg h']

theorem swapOutProto_coeff (σ : Storage) (dx : Nat) :
    swapOutProto dx (coeffBps σ) = protoOf σ dx := by
  unfold swapOutProto coeffBps protoOf
  split_ifs <;> simp [Amount.raw_zero]

theorem coeffBps_raw (σ : Storage) : (coeffBps σ).raw = coeffOf σ := by
  unfold coeffBps coeffOf
  split_ifs <;> simp [Amount.raw_zero]

theorem BPS_eq : BPS.raw = 10000 := rfl
theorem BPS_pos : 0 < BPS.raw := by decide
theorem dxFeeLess_lit (dx : Nat) : dxFeeLess dx = dx * 9970 / 10000 := rfl

theorem dxFeeLess_le (dx : Nat) : dxFeeLess dx ≤ dx := by
  simpa [dxFeeLess, Nat.mul_comm dx] using
    remove_le_reserves (BPS.raw - FEE_BPS) dx BPS.raw (Nat.sub_le _ _) BPS_pos

theorem protoOf_le_dx (σ : Storage) (dx : Nat) (h : σ.protocolShareBps ≤ BPS) :
    protoOf σ dx ≤ dx := by
  unfold protoOf
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.le_trans
      (share_le (swapFee dx) σ.protocolShareBps.raw BPS.raw (by simpa using h) (by decide))
      (Nat.sub_le _ _)

@[simp] theorem balSel0_eq : balSel0 = 0x70a08231 := by decide
@[simp] theorem balSel1_eq : balSel1 = 0x70a08231 := by decide
@[simp] theorem supplySel0_eq : supplySel0 = 0x18160ddd := by decide
@[simp] theorem supplySel1_eq : supplySel1 = 0x18160ddd := by decide

theorem holdings0_view (self : Address) :
    holdings0 self w = (viewBal0 w.self.token0 self w.oracle w.ext).raw := by
  simp [holdings0, viewBal0, IERC20.Ref.impl, IERC20.Impl.ofRef, World.view]

theorem holdings1_view (self : Address) :
    holdings1 self w = (viewBal1 w.self.token1 self w.oracle w.ext).raw := by
  simp [holdings1, viewBal1, IERC20.Ref.impl, IERC20.Impl.ofRef, World.view]

theorem holdings0_congr (self : Address) {w w' : World Storage ExtState Event}
    (ha : w'.self.token0.addr = w.self.token0.addr)
    (ho : w'.oracle = w.oracle) (hx : w'.ext = w.ext) :
    holdings0 self w' = holdings0 self w := by
  simp [holdings0, IERC20.Ref.impl, IERC20.Impl.ofRef, ha, ho, hx, World.view]

theorem holdings1_congr (self : Address) {w w' : World Storage ExtState Event}
    (ha : w'.self.token1.addr = w.self.token1.addr)
    (ho : w'.oracle = w.oracle) (hx : w'.ext = w.ext) :
    holdings1 self w' = holdings1 self w := by
  simp [holdings1, IERC20.Ref.impl, IERC20.Impl.ofRef, ha, ho, hx, World.view]

theorem transferFrom_frame {a : Asset} {r : IERC20.Ref a}
    {src dst : Address} {amt : Amount a} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (tfCall r src dst amt) ctx w = .ok (b, w')) :
    w'.self = w.self ∧ w'.oracle = w.oracle ∧ w'.log = w.log := by
  refine ⟨Tx.call_self (α := Bool) r.addr
      (Interface.selector (I := IERC20 a) "transferFrom")
      [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] h,
    Tx.call_oracle (α := Bool) r.addr
      (Interface.selector (I := IERC20 a) "transferFrom")
      [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] h, ?_⟩
  simp [IERC20.Ref.transferFrom, Tx.run_call] at h
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem transfer_frame {a : Asset} {r : IERC20.Ref a}
    {dst : Address} {amt : Amount a} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (trCall r dst amt) ctx w = .ok (b, w')) :
    w'.self = w.self ∧ w'.oracle = w.oracle ∧ w'.log = w.log := by
  refine ⟨Tx.call_self (α := Bool) r.addr
      (Interface.selector (I := IERC20 a) "transfer")
      [AbiType.encode dst, AbiType.encode amt] h,
    Tx.call_oracle (α := Bool) r.addr
      (Interface.selector (I := IERC20 a) "transfer")
      [AbiType.encode dst, AbiType.encode amt] h, ?_⟩
  simp [IERC20.Ref.transfer, Tx.run_call] at h
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem impl_transferFrom {a : Asset} (r : IERC20.Ref a)
    (src dst : Address) (amt : Amount a) :
    r.impl.transferFrom src dst amt ctx w.view =
      (Tx.run (tfCall r src dst amt) ctx w).toOption.map
        (Prod.map id World.view) := by
  simp only [IERC20.Ref.impl, IERC20.Impl.ofRef, IERC20.Ref.transferFrom, tfCall]
  exact Tx.callDecode_view (α := Bool) (ε := Error) r.addr (0x23b872dd : Nat)
    [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] ctx w

theorem impl_transfer {a : Asset} (r : IERC20.Ref a)
    (dst : Address) (amt : Amount a) :
    r.impl.transfer dst amt ctx w.view =
      (Tx.run (trCall r dst amt) ctx w).toOption.map
        (Prod.map id World.view) := by
  simp only [IERC20.Ref.impl, IERC20.Impl.ofRef, IERC20.Ref.transfer, trCall]
  exact Tx.callDecode_view (α := Bool) (ε := Error) r.addr (0xa9059cbb : Nat)
    [AbiType.encode dst, AbiType.encode amt] ctx w

theorem transfer_run_ctx_irrel {a : Asset} {r : IERC20.Ref a}
    {dst : Address} {amt : Amount a} {ctx' : Ctx}
    {w₀ : World Storage ExtState Event} :
    Tx.run (trCall r dst amt) ctx w₀ =
      Tx.run (trCall r dst amt) ctx' w₀ := by
  simp [IERC20.Ref.transfer, Tx.run_call]

theorem eq_self_ext {σ : Storage} {w1 : World Storage ExtState Event}
    (hs : w1.self = σ) (ho : w1.oracle = w.oracle) (hl : w1.log = w.log) :
    w1 = { w with self := σ, ext := w1.ext } := by
  cases w; cases w1; simp_all

/-- A CALL ignores `self`; success on an updated storage world transports to
the original world with only `ext` changed. -/
theorem transferFrom_call_ignore_self {a : Asset} {r : IERC20.Ref a}
    {src dst : Address} {amt : Amount a} {σ : Storage} {b : Bool}
    {w1 : World Storage ExtState Event}
    (h : Tx.run (tfCall r src dst amt) ctx { w with self := σ } = .ok (b, w1)) :
    Tx.run (tfCall r src dst amt) ctx w = .ok (b, { w with ext := w1.ext }) ∧
      w1.self = σ ∧ w1.oracle = w.oracle ∧ w1.log = w.log := by
  have hframe := transferFrom_frame (w := { w with self := σ }) h
  refine ⟨?_, hframe.1, hframe.2.1, hframe.2.2⟩
  simp [IERC20.Ref.transferFrom, Tx.run_call] at h ⊢
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem transfer_call_ignore_self {a : Asset} {r : IERC20.Ref a}
    {dst : Address} {amt : Amount a} {σ : Storage} {b : Bool}
    {w1 : World Storage ExtState Event}
    (h : Tx.run (trCall r dst amt) ctx { w with self := σ } = .ok (b, w1)) :
    Tx.run (trCall r dst amt) ctx w = .ok (b, { w with ext := w1.ext }) ∧
      w1.self = σ ∧ w1.oracle = w.oracle ∧ w1.log = w.log := by
  have hframe := transfer_frame (w := { w with self := σ }) h
  refine ⟨?_, hframe.1, hframe.2.1, hframe.2.2⟩
  simp [IERC20.Ref.transfer, Tx.run_call] at h ⊢
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem transferFrom_call_addr {a : Asset} {r : IERC20.Ref a}
    {src dst : Address} {amt : Amount a} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (tfCall r src dst amt) ctx w = .ok (b, w')) :
    ∃ sel args rets, w.oracle.call r.addr sel args w.ext = some (rets, w'.ext) := by
  simp [IERC20.Ref.transferFrom, Tx.run_call] at h
  split at h
  · cases h
  · next rets x' hcall =>
    split at h
    · cases h
    · cases h
      exact ⟨_, _, rets, hcall⟩

theorem transfer_call_addr {a : Asset} {r : IERC20.Ref a}
    {dst : Address} {amt : Amount a} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (trCall r dst amt) ctx w = .ok (b, w')) :
    ∃ sel args rets, w.oracle.call r.addr sel args w.ext = some (rets, w'.ext) := by
  simp [IERC20.Ref.transfer, Tx.run_call] at h
  split at h
  · cases h
  · next rets x' hcall =>
    split at h
    · cases h
    · cases h
      exact ⟨_, _, rets, hcall⟩

private theorem run_req_false {α : Type} {c : Prop} [Decidable c] {e : Error}
    {k : Unit → Tx Storage ExtState Event Error α} (h : ¬c) :
    Tx.run (Tx.require (S := Storage) (X := ExtState) (E := Event) c e >>= k) ctx w =
      .error (.user e) := by
  simp [Tx.run_bind, Tx.run_require, h]

private theorem run_req_true {α : Type} {c : Prop} [Decidable c] {e : Error}
    {k : Unit → Tx Storage ExtState Event Error α} (h : c) :
    Tx.run (Tx.require (S := Storage) (X := ExtState) (E := Event) c e >>= k) ctx w =
      Tx.run (k ()) ctx w := by
  simp [Tx.run_bind, Tx.run_require, h]

private theorem run_load_bind {α β : Type} {proj : Storage → α}
    {k : α → Tx Storage ExtState Event Error β} :
    Tx.run (Tx.load (X := ExtState) (E := Event) (ε := Error) proj >>= k) ctx w =
      Tx.run (k (proj w.self)) ctx w := by
  simp [Tx.run_bind, Tx.run_load]

private theorem run_loadMap_bind {α : Type} {who : Address}
    {k : Amount lpShare → Tx Storage ExtState Event Error α} :
    Tx.run (Tx.loadMap (X := ExtState) (E := Event) (ε := Error)
        (fun σ k => σ.shares k) who >>= k) ctx w =
      Tx.run (k (w.self.shares who)) ctx w := by
  simp [Tx.run_bind, Tx.run_loadMap]

private theorem run_sender_bind {α : Type}
    {k : Address → Tx Storage ExtState Event Error α} :
    Tx.run (Tx.sender (S := Storage) (X := ExtState) (E := Event) >>= k) ctx w =
      Tx.run (k ctx.sender) ctx w := by
  simp [Tx.run_bind, Tx.run_sender]

private theorem run_self_bind {α : Type}
    {k : Address → Tx Storage ExtState Event Error α} :
    Tx.run (Tx.selfAddress (S := Storage) (X := ExtState) (E := Event) >>= k)
        ctx w =
      Tx.run (k ctx.self) ctx w := by
  simp [Tx.run_bind, Tx.run_selfAddress]

private theorem bind_ite {α β : Type} {c : Prop} [Decidable c]
    (x y : Tx Storage ExtState Event Error α)
    (k : α → Tx Storage ExtState Event Error β) :
    ((if c then x else y) >>= k) = if c then (x >>= k) else (y >>= k) := by
  split <;> rfl

private theorem run_mulDivDown_bind {α : Type} {a b : Asset}
    (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        Tx.run (k ⟨num.raw * x.raw / y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_def, Amount.run_mulDivDown]
  split_ifs <;> rfl

private theorem run_mulDivDown_word_bind {α : Type} {b : Asset}
    (num : Amount b) (x y : Word)
    (k : Amount b → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y = 0 then .error (.arith .divByZero)
      else if num.raw * x < wordBound then
        Tx.run (k ⟨num.raw * x / y⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_word, Amount.run_mulDivDown]
  by_cases h0 : (Amount.ofWord (a := Asset.fixed 0) y).raw = 0
  · rw [if_pos h0]
    simp [Amount.raw_ofWord] at h0
    simp [h0]
  · rw [if_neg h0]
    simp [Amount.raw_ofWord] at h0
    by_cases hfit : num.raw * (Amount.ofWord (a := Asset.fixed 0) x).raw < wordBound
    · rw [if_pos hfit]
      simp [Amount.raw_ofWord] at hfit
      simp [h0, hfit]
    · rw [if_neg hfit]
      simp [Amount.raw_ofWord] at hfit
      simp [h0, hfit]

private theorem run_mulFixedDown_bind {α : Type} {a : Asset} {d : Nat}
    (x : Amount a) (r : Fixed d)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulFixedDown.hMulFixedDown (S := Storage) (X := ExtState)
        (E := Event) (ε := Error) x r >>= k) ctx w =
      if x.raw * r.raw < wordBound then Tx.run (k (Amount.mulDown x r)) ctx w
      else .error (.arith .overflow) := by
  have hden : (Amount.ofWord (Word.scale d) : Amount (Asset.fixed d)).raw ≠ 0 := by
    simpa [Amount.raw_ofWord] using
      (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide : 0 < 10)) : Word.scale d ≠ 0)
  rw [Tx.run_bind, Amount.hMulFixedDown_def, Amount.mulFixedDown, Amount.run_mulDivDown]
  rw [if_neg hden]
  by_cases hfit : x.raw * r.raw < wordBound
  · rw [if_pos hfit]
    simp [hfit, Amount.mulDown, Amount.floorMulDiv, Amount.raw_ofWord]
  · rw [if_neg hfit]
    simp [hfit]

private theorem run_hAdd_bind {α : Type} {a : Asset} (x y : Amount a)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HAddChecked.hAdd (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) x y >>= k) ctx w =
      if x.raw + y.raw < wordBound then Tx.run (k ⟨x.raw + y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hAdd_def, Amount.run_add]
  split_ifs <;> rfl

private theorem run_hSub_bind {α : Type} {a : Asset} (x y : Amount a)
    (k : Amount a → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HSubChecked.hSub (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) x y >>= k) ctx w =
      if y.raw ≤ x.raw then Tx.run (k ⟨x.raw - y.raw⟩) ctx w
      else .error (.arith .underflow) := by
  rw [Tx.run_bind, Amount.hSub_def, Amount.run_sub]
  split_ifs <;> rfl

private theorem run_pure_bind {α β : Type} (a : α)
    (k : α → Tx Storage ExtState Event Error β) :
    Tx.run (pure a >>= k) ctx w = Tx.run (k a) ctx w := by
  rw [Tx.pure_bind]

private theorem run_store_bind {α β : Type} (upd : Storage → α → Storage) (v : α)
    (k : Unit → Tx Storage ExtState Event Error β) :
    Tx.run (Tx.store (X := ExtState) (E := Event) (ε := Error) upd v >>= k) ctx w =
      Tx.run (k ()) ctx { w with self := upd w.self v } := by
  rw [Tx.run_bind, Tx.run_store]

private theorem run_storeMap_bind {α : Type} (who : Address) (v : Amount lpShare)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.storeMap (X := ExtState) (E := Event) (ε := Error)
        (fun σ k => (σ.shares k).raw)
        (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
        who v.raw >>= k) ctx w =
      Tx.run (k ()) ctx
        { w with self := { w.self with
            shares := fun k =>
              Amount.ofWord (Function.update (fun k => (w.self.shares k).raw)
                who v.raw k) } } := by
  rw [Tx.run_bind, Tx.run_storeMap]

private theorem run_read_token0 {α : Type}
    (k : IERC20.Ref asset0 → Tx Storage ExtState Event Error α) :
    Tx.run (((fun n => ({ addr := n } : IERC20.Ref asset0)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error)
          (fun σ => σ.token0.addr)) >>= k) ctx w =
      Tx.run (k w.self.token0) ctx w := by
  simp only [Tx.run_bind, Tx.run_map, Tx.run_load]

private theorem run_read_token1 {α : Type}
    (k : IERC20.Ref asset1 → Tx Storage ExtState Event Error α) :
    Tx.run (((fun n => ({ addr := n } : IERC20.Ref asset1)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error)
          (fun σ => σ.token1.addr)) >>= k) ctx w =
      Tx.run (k w.self.token1) ctx w := by
  simp only [Tx.run_bind, Tx.run_map, Tx.run_load]

/-- Both token refs, in `token0` then `token1` order. Closed so CALLs stay opaque. -/
private theorem run_read_token0_then_token1 {α : Type}
    (k : IERC20.Ref asset0 → IERC20.Ref asset1 →
      Tx Storage ExtState Event Error α) :
    Tx.run (do
      let t0 ← (fun n => ({ addr := n } : IERC20.Ref asset0)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error) (fun σ => σ.token0.addr)
      let t1 ← (fun n => ({ addr := n } : IERC20.Ref asset1)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error) (fun σ => σ.token1.addr)
      k t0 t1) ctx w =
      Tx.run (k w.self.token0 w.self.token1) ctx w := by
  simp only [Tx.run_bind, Tx.run_map, Tx.run_load]

/-- Both token refs, in `token1` then `token0` order (`swap1for0`). -/
private theorem run_read_token1_then_token0 {α : Type}
    (k : IERC20.Ref asset1 → IERC20.Ref asset0 →
      Tx Storage ExtState Event Error α) :
    Tx.run (do
      let t1 ← (fun n => ({ addr := n } : IERC20.Ref asset1)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error) (fun σ => σ.token1.addr)
      let t0 ← (fun n => ({ addr := n } : IERC20.Ref asset0)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error) (fun σ => σ.token0.addr)
      k t1 t0) ctx w =
      Tx.run (k w.self.token1 w.self.token0) ctx w := by
  simp only [Tx.run_bind, Tx.run_map, Tx.run_load]

private theorem run_emit_bind {α : Type} {ev : Event}
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.emit (S := Storage) (X := ExtState) ev >>= k) ctx w =
      Tx.run (k ()) ctx { w with log := w.log ++ [ev] } := by
  simp [Tx.run_bind, Tx.run_emit]

/-- Bind after `safeTransferFrom` is a match on the Bool CALL, not a nested
Unit match. Quantified over `w₀` so it rewrites on post-storage worlds. -/
private theorem run_safeTF_bind {α : Type} {a : Asset}
    {w₀ : World Storage ExtState Event}
    (r : IERC20.Ref a) (src dst : Address) (amt : Amount a)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (safeTransferFrom (E := Event) r src dst amt Error.TransferFailed >>= k)
        ctx w₀ =
      match Tx.run (tfCall r src dst amt) ctx w₀ with
      | .error e => .error e
      | .ok (ok, w') =>
        if ok = true then Tx.run (k ()) ctx w'
        else .error (.user .TransferFailed) := by
  rw [Tx.run_bind, run_safeTransferFrom]
  cases htf : Tx.run (tfCall r src dst amt) ctx w₀
  · rfl
  · rename_i p
    rcases p with ⟨ok, w'⟩
    cases ok <;> rfl

/-- Bind after `safeTransfer` is a match on the Bool CALL. -/
private theorem run_safeTR_bind {α : Type} {a : Asset}
    {w₀ : World Storage ExtState Event}
    (r : IERC20.Ref a) (dst : Address) (amt : Amount a)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (safeTransfer (E := Event) r dst amt Error.TransferFailed >>= k) ctx w₀ =
      match Tx.run (trCall r dst amt) ctx w₀ with
      | .error e => .error e
      | .ok (ok, w') =>
        if ok = true then Tx.run (k ()) ctx w'
        else .error (.user .TransferFailed) := by
  rw [Tx.run_bind, run_safeTransfer]
  cases htr : Tx.run (trCall r dst amt) ctx w₀
  · rfl
  · rename_i p
    rcases p with ⟨ok, w'⟩
    cases ok <;> rfl

private theorem run_emit_pure {w₀ : World Storage ExtState Event}
    (ev : Event) {α : Type} (a : α) :
    Tx.run (do
        Tx.emit (S := Storage) (X := ExtState) ev
        (pure a : Tx Storage ExtState Event Error α)) ctx w₀ =
      .ok (a, { w₀ with log := w₀.log ++ [ev] }) := by
  simp [Tx.run_bind, Tx.run_emit, Tx.run_pure]

private theorem ok_of_emit_pure {w₀ : World Storage ExtState Event}
    {ev : Event} {α : Type} {a n : α} {w' : World Storage ExtState Event}
    (hrun : Tx.run (do
        Tx.emit (S := Storage) (X := ExtState) ev
        (pure a : Tx Storage ExtState Event Error α)) ctx w₀ = .ok (n, w')) :
    n = a ∧ w'.self = w₀.self ∧ w'.oracle = w₀.oracle ∧
      w'.log = w₀.log ++ [ev] ∧ w'.ext = w₀.ext := by
  simp [Tx.run_bind, Tx.run_emit, Tx.run_pure] at hrun
  rcases hrun with ⟨hn, rfl⟩
  exact ⟨hn.symm, rfl, rfl, rfl, rfl⟩

/-- Success of `safeTransferFrom >>= k` yields a true CALL that preserves
`self` / oracle / log, then `k`. -/
private theorem ok_of_safeTF_bind {α : Type} {a : Asset}
    {w₀ : World Storage ExtState Event}
    {r : IERC20.Ref a} {src dst : Address} {amt : Amount a}
    {k : Unit → Tx Storage ExtState Event Error α}
    {n : α} {w' : World Storage ExtState Event}
    (hrun : Tx.run (safeTransferFrom (E := Event) r src dst amt
        Error.TransferFailed >>= k) ctx w₀ = .ok (n, w')) :
    ∃ w1, Tx.run (tfCall r src dst amt) ctx w₀ = .ok (true, w1) ∧
      w1.self = w₀.self ∧ w1.oracle = w₀.oracle ∧ w1.log = w₀.log ∧
      Tx.run (k ()) ctx w1 = .ok (n, w') := by
  rw [run_safeTF_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    cases b
    · simp at hrun
    · rcases transferFrom_frame (w := w₀) hcall with ⟨hs, ho, hl⟩
      exact ⟨w1, hcall, hs, ho, hl, hrun⟩

/-- Success of `safeTransfer >>= k` yields a true CALL that preserves
`self` / oracle / log, then `k`. -/
private theorem ok_of_safeTR_bind {α : Type} {a : Asset}
    {w₀ : World Storage ExtState Event}
    {r : IERC20.Ref a} {dst : Address} {amt : Amount a}
    {k : Unit → Tx Storage ExtState Event Error α}
    {n : α} {w' : World Storage ExtState Event}
    (hrun : Tx.run (safeTransfer (E := Event) r dst amt
        Error.TransferFailed >>= k) ctx w₀ = .ok (n, w')) :
    ∃ w1, Tx.run (trCall r dst amt) ctx w₀ = .ok (true, w1) ∧
      w1.self = w₀.self ∧ w1.oracle = w₀.oracle ∧ w1.log = w₀.log ∧
      Tx.run (k ()) ctx w1 = .ok (n, w') := by
  rw [run_safeTR_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    cases b
    · simp at hrun
    · rcases transfer_frame (w := w₀) hcall with ⟨hs, ho, hl⟩
      exact ⟨w1, hcall, hs, ho, hl, hrun⟩

private theorem word_10000_ne : (10000 : Word) ≠ 0 := by decide

private theorem wordBound_pos : 0 < wordBound :=
  Nat.pow_pos (by decide)

private theorem swapFee_sub (dx : Nat) : swapFee dx = dx - dxFeeLess dx :=
  rfl

private theorem proto_mulDown {_a : Asset} (dx : Nat) (ps : Bps) :
    Amount.mulDown (⟨dx - dxFeeLess dx⟩ : Amount _a) ps =
      ⟨(dx - dxFeeLess dx) * ps.raw / BPS.raw⟩ := by
  apply Amount.ext
  simp [Amount.mulDown_raw, Amount.raw_mk]
  rfl

private theorem proto_mulDown_zero (dx : Nat) {_a : Asset} :
    Amount.mulDown (⟨dx - dxFeeLess dx⟩ : Amount _a) (0 : Bps) = ⟨0⟩ := by
  apply Amount.ext
  simp [Amount.mulDown_raw]

private theorem proto_prod_zero (dx : Nat) :
    (dx - dxFeeLess dx) * (0 : Bps).raw < wordBound := by
  simp [Amount.raw_zero]
  exact wordBound_pos

/-- `addLiquidity` after a successful mint, at the first `+?`. -/
private theorem addLiq_after_mint (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hminted : 0 < mintedShares w.self a0.raw a1.raw) :
    Tx.run (addLiquidity a0 a1) ctx w =
      Tx.run (do
        let r0' ← w.self.reserve0 +? a0
        write reserve0 r0'
        let r1' ← w.self.reserve1 +? a1
        write reserve1 r1'
        let ts' ← (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare) +?
          w.self.totalShares
        write totalShares ts'
        let bal ← read shares[ctx.sender]
        let bal' ← (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare) +? bal
        write shares[ctx.sender] bal'
        let t0 ← read token0
        let t1 ← read token1
        safeTransferFrom t0 ctx.sender ctx.self a0 .TransferFailed
        safeTransferFrom t1 ctx.sender ctx.self a1 .TransferFailed
        Tx.emit (.AddLiquidity ctx.sender a0 a1
          ⟨mintedShares w.self a0.raw a1.raw⟩)
        pure (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare)
        : M (Amount lpShare)) ctx w := by
  have hposM : 0 < (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare) := by
    simpa [Amount.lt_iff] using hminted
  rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind]
  rw [Tx.run_ite]
  by_cases hts : w.self.totalShares = 0
  · have htsr : w.self.totalShares.raw = 0 := (Amount.eq_iff _ _).mp hts
    rw [if_pos hts]
    simp only [Tx.pure_bind]
    have hm : a0.as lpShare =
          ⟨mintedShares w.self a0.raw a1.raw⟩ := by
      apply Amount.ext
      simp [mintedShares, htsr, Amount.raw_as]
    rw [hm, run_req_true hposM]
  · have htsr : w.self.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (htsr h0).elim
    · have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
      have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
      have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      rw [if_neg hts, run_req_true hr0A, run_req_true hr1A]
      rw [run_mulDivDown_bind]
      rw [if_neg hr0n, if_pos hm0]
      rw [run_mulDivDown_bind]
      rw [if_neg hr1n, if_pos hm1]
      rw [Tx.run_ite]
      by_cases hle :
          (⟨w.self.totalShares.raw * a0.raw / w.self.reserve0.raw⟩ :
            Amount lpShare) ≤
            ⟨w.self.totalShares.raw * a1.raw / w.self.reserve1.raw⟩
      · rw [if_pos hle, run_pure_bind]
        have hle' : w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [Amount.le_iff] using hle
        have hm :
            (⟨w.self.totalShares.raw * a0.raw / w.self.reserve0.raw⟩ :
              Amount lpShare) =
              ⟨mintedShares w.self a0.raw a1.raw⟩ := by
          simp [mintedShares, htsr, hle']
        rw [hm, run_req_true hposM]
      · rw [if_neg hle, run_pure_bind]
        have hle' : ¬ w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [Amount.le_iff] using hle
        have hm :
            (⟨w.self.totalShares.raw * a1.raw / w.self.reserve1.raw⟩ :
              Amount lpShare) =
              ⟨mintedShares w.self a0.raw a1.raw⟩ := by
          simp [mintedShares, htsr, hle']
        rw [hm, run_req_true hposM]

/-! ### Views / admin -/

theorem getReserves_ok :
    Tx.run getReserves ctx w = .ok ((w.self.reserve0, w.self.reserve1), w) := by
  simp [getReserves]

theorem sharesOf_ok (who : Address) :
    Tx.run (sharesOf who) ctx w = .ok (w.self.shares who, w) := by
  simp [sharesOf]

theorem protocolFees_ok :
    Tx.run protocolFees ctx w =
      .ok ((w.self.protocolFees0, w.self.protocolFees1), w) := by
  simp [protocolFees]

theorem setProtocolShare_ok (bps : Bps)
    (hown : ctx.sender = w.self.owner) (hle : bps ≤ BPS) :
    Tx.run (setProtocolShare bps) ctx w =
      .ok ((), { w with
        self := { w.self with protocolShareBps := bps }
        log := w.log ++ [.ProtocolShareSet bps] }) := by
  simp [setProtocolShare, hown, hle]

theorem setProtocolShare_only_owner (bps : Bps)
    (h : ctx.sender ≠ w.self.owner) :
    Tx.run (setProtocolShare bps) ctx w = .error (.user .NotOwner) := by
  simp [setProtocolShare, h]

theorem setProtocolShare_ok_of_run {bps : Bps} {w' : World Storage ExtState Event}
    (hrun : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    ctx.sender = w.self.owner ∧ bps ≤ BPS ∧
      w' = { w with
        self := { w.self with protocolShareBps := bps }
        log := w.log ++ [.ProtocolShareSet bps] } := by
  have hown : ctx.sender = w.self.owner := by
    by_contra h; exact Tx.run_ok_error hrun (setProtocolShare_only_owner bps h)
  have hle : bps ≤ BPS := by
    by_contra h; simp [setProtocolShare, hown, h] at hrun
  refine ⟨hown, hle, ?_⟩
  cases hrun.symm.trans (setProtocolShare_ok bps hown hle); rfl

theorem setFeeTo_ok (recipient : Address) (hown : ctx.sender = w.self.owner) :
    Tx.run (setFeeTo recipient) ctx w =
      .ok ((), { w with
        self := { w.self with feeTo := recipient }
        log := w.log ++ [.FeeToSet recipient] }) := by
  simp [setFeeTo, hown]

theorem setFeeTo_only_owner (recipient : Address)
    (h : ctx.sender ≠ w.self.owner) :
    Tx.run (setFeeTo recipient) ctx w = .error (.user .NotOwner) := by
  simp [setFeeTo, h]

theorem setFeeTo_ok_of_run {recipient : Address} {w' : World Storage ExtState Event}
    (hrun : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    ctx.sender = w.self.owner ∧
      w' = { w with
        self := { w.self with feeTo := recipient }
        log := w.log ++ [.FeeToSet recipient] } := by
  have hown : ctx.sender = w.self.owner := by
    by_contra h; exact Tx.run_ok_error hrun (setFeeTo_only_owner recipient h)
  refine ⟨hown, ?_⟩
  cases hrun.symm.trans (setFeeTo_ok recipient hown); rfl

/-! ### addLiquidity -/

theorem addLiquidity_reverts_on_nonpos0 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos : ¬ 0 < a0) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.user .Zero) := by
  rw [addLiquidity, run_req_false hpos]

theorem addLiquidity_reverts_on_nonpos1 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : ¬ 0 < a1) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.user .Zero) := by
  rw [addLiquidity, run_req_true hpos0, run_req_false hpos1]

structure AddLiqOk (ctx : Ctx) (w : World Storage ExtState Event)
    (a0 : Amount asset0) (a1 : Amount asset1) : Prop where
  pos0 : 0 < a0
  pos1 : 0 < a1
  minted : 0 < mintedShares w.self a0.raw a1.raw
  prod :
    w.self.totalShares.raw = 0 ∨
      (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
        w.self.totalShares.raw * a0.raw < wordBound ∧
        w.self.totalShares.raw * a1.raw < wordBound)
  add0 : w.self.reserve0.raw + a0.raw < wordBound
  add1 : w.self.reserve1.raw + a1.raw < wordBound
  addS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound
  addB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw < wordBound

theorem addLiquidity_reverts_on_zero_r0 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hts : w.self.totalShares.raw ≠ 0) (hr0 : ¬ 0 < w.self.reserve0.raw) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.user .Zero) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  have hz : ¬ 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind,
    Tx.run_ite, if_neg hne, run_req_false hz]

theorem addLiquidity_reverts_on_zero_r1 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hts : w.self.totalShares.raw ≠ 0) (hr0 : 0 < w.self.reserve0.raw)
    (hr1 : ¬ 0 < w.self.reserve1.raw) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.user .Zero) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  have hz : ¬ 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
  rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind,
    Tx.run_ite, if_neg hne, run_req_true hr0A, run_req_false hz]

theorem addLiquidity_reverts_on_mul0 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hts : w.self.totalShares.raw ≠ 0) (hr0 : 0 < w.self.reserve0.raw)
    (hr1 : 0 < w.self.reserve1.raw)
    (hmul : ¬ w.self.totalShares.raw * a0.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind]
  rw [Tx.run_ite, if_neg hne, run_req_true hr0A, run_req_true hr1A]
  rw [run_mulDivDown_bind, if_neg hr0n, if_neg hmul]

theorem addLiquidity_reverts_on_mul1 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hts : w.self.totalShares.raw ≠ 0) (hr0 : 0 < w.self.reserve0.raw)
    (hr1 : 0 < w.self.reserve1.raw)
    (hm0 : w.self.totalShares.raw * a0.raw < wordBound)
    (hmul : ¬ w.self.totalShares.raw * a1.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
  have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
  have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
  rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind]
  rw [Tx.run_ite, if_neg hne, run_req_true hr0A, run_req_true hr1A]
  rw [run_mulDivDown_bind, if_neg hr0n, if_pos hm0]
  rw [run_mulDivDown_bind, if_neg hr1n, if_neg hmul]

theorem addLiquidity_reverts_on_zero_shares (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hminted : ¬ 0 < mintedShares w.self a0.raw a1.raw) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.user .ZeroShares) := by
  have hreq : ¬ 0 < (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare) := by
    simpa [Amount.lt_iff] using hminted
  by_cases hts : w.self.totalShares = 0
  · have htsr : w.self.totalShares.raw = 0 := (Amount.eq_iff _ _).mp hts
    have : ¬ 0 < a0.raw := by simpa [mintedShares, htsr] using hminted
    exact (this (by simpa [Amount.lt_iff] using hpos0)).elim
  · have htsr : w.self.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    rcases hprod with h0 | ⟨hr0, hr1, hm0, hm1⟩
    · exact (htsr h0).elim
    · have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
      have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
      have hr0n : w.self.reserve0.raw ≠ 0 := Nat.ne_of_gt hr0
      have hr1n : w.self.reserve1.raw ≠ 0 := Nat.ne_of_gt hr1
      rw [addLiquidity, run_req_true hpos0, run_req_true hpos1,
        run_sender_bind, run_self_bind, run_load_bind, run_load_bind, run_load_bind]
      rw [Tx.run_ite, if_neg hts, run_req_true hr0A, run_req_true hr1A]
      rw [run_mulDivDown_bind, if_neg hr0n, if_pos hm0]
      rw [run_mulDivDown_bind, if_neg hr1n, if_pos hm1, Tx.run_ite]
      by_cases hle :
          (⟨w.self.totalShares.raw * a0.raw / w.self.reserve0.raw⟩ :
            Amount lpShare) ≤
            ⟨w.self.totalShares.raw * a1.raw / w.self.reserve1.raw⟩
      · have hle' : w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [Amount.le_iff] using hle
        have hm :
            (⟨w.self.totalShares.raw * a0.raw / w.self.reserve0.raw⟩ :
              Amount lpShare) =
              ⟨mintedShares w.self a0.raw a1.raw⟩ := by
          simp [mintedShares, htsr, hle']
        rw [if_pos hle, run_pure_bind, hm, run_req_false hreq]
      · have hle' : ¬ w.self.totalShares.raw * a0.raw / w.self.reserve0.raw ≤
            w.self.totalShares.raw * a1.raw / w.self.reserve1.raw := by
          simpa [Amount.le_iff] using hle
        have hm :
            (⟨w.self.totalShares.raw * a1.raw / w.self.reserve1.raw⟩ :
              Amount lpShare) =
              ⟨mintedShares w.self a0.raw a1.raw⟩ := by
          simp [mintedShares, htsr, hle']
        rw [if_neg hle, run_pure_bind, hm, run_req_false hreq]

theorem addLiquidity_reverts_on_add_r0 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd : ¬ w.self.reserve0.raw + a0.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  rw [addLiq_after_mint a0 a1 hpos0 hpos1 hprod hminted]
  simp only [run_hAdd_bind]
  rw [if_neg hadd]

theorem addLiquidity_reverts_on_add_r1 (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd : ¬ w.self.reserve1.raw + a1.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  rw [addLiq_after_mint a0 a1 hpos0 hpos1 hprod hminted]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_neg hadd]

theorem addLiquidity_reverts_on_add_ts (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (hadd : ¬ mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  rw [addLiq_after_mint a0 a1 hpos0 hpos1 hprod hminted]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_neg hadd]

theorem addLiquidity_reverts_on_add_bal (a0 : Amount asset0) (a1 : Amount asset1)
    (hpos0 : 0 < a0) (hpos1 : 0 < a1)
    (hminted : 0 < mintedShares w.self a0.raw a1.raw)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound))
    (hadd0 : w.self.reserve0.raw + a0.raw < wordBound)
    (hadd1 : w.self.reserve1.raw + a1.raw < wordBound)
    (haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound)
    (hadd : ¬ mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw <
        wordBound) :
    Tx.run (addLiquidity a0 a1) ctx w = .error (.arith .overflow) := by
  rw [addLiq_after_mint a0 a1 hpos0 hpos1 hprod hminted]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos haddS, run_store_bind, run_loadMap_bind]
  simp only [run_hAdd_bind]
  rw [if_neg hadd]

theorem addLiquidity_ok_of_run {a0 : Amount asset0} {a1 : Amount asset1}
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (hrun : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    AddLiqOk ctx w a0 a1 := by
  have hpos0 : 0 < a0 := by
    by_contra h; exact Tx.run_ok_error hrun (addLiquidity_reverts_on_nonpos0 a0 a1 h)
  have hpos1 : 0 < a1 := by
    by_contra h; exact Tx.run_ok_error hrun (addLiquidity_reverts_on_nonpos1 a0 a1 hpos0 h)
  have hprod :
      w.self.totalShares.raw = 0 ∨
        (0 < w.self.reserve0.raw ∧ 0 < w.self.reserve1.raw ∧
          w.self.totalShares.raw * a0.raw < wordBound ∧
          w.self.totalShares.raw * a1.raw < wordBound) := by
    by_cases hts : w.self.totalShares.raw = 0
    · exact Or.inl hts
    · by_cases hr0 : 0 < w.self.reserve0.raw
      · by_cases hr1 : 0 < w.self.reserve1.raw
        · by_cases hm0 : w.self.totalShares.raw * a0.raw < wordBound
          · by_cases hm1 : w.self.totalShares.raw * a1.raw < wordBound
            · exact Or.inr ⟨hr0, hr1, hm0, hm1⟩
            · exact (Tx.run_ok_error hrun
                (addLiquidity_reverts_on_mul1 a0 a1 hpos0 hpos1 hts hr0 hr1 hm0 hm1)).elim
          · exact (Tx.run_ok_error hrun
              (addLiquidity_reverts_on_mul0 a0 a1 hpos0 hpos1 hts hr0 hr1 hm0)).elim
        · exact (Tx.run_ok_error hrun
            (addLiquidity_reverts_on_zero_r1 a0 a1 hpos0 hpos1 hts hr0 hr1)).elim
      · exact (Tx.run_ok_error hrun
          (addLiquidity_reverts_on_zero_r0 a0 a1 hpos0 hpos1 hts hr0)).elim
  have hminted : 0 < mintedShares w.self a0.raw a1.raw := by
    by_contra h
    exact Tx.run_ok_error hrun (addLiquidity_reverts_on_zero_shares a0 a1 hpos0 hpos1 hprod h)
  have hadd0 : w.self.reserve0.raw + a0.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (addLiquidity_reverts_on_add_r0 a0 a1 hpos0 hpos1 hminted hprod h)
  have hadd1 : w.self.reserve1.raw + a1.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (addLiquidity_reverts_on_add_r1 a0 a1 hpos0 hpos1 hminted hprod hadd0 h)
  have haddS : mintedShares w.self a0.raw a1.raw + w.self.totalShares.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (addLiquidity_reverts_on_add_ts a0 a1 hpos0 hpos1 hminted hprod hadd0 hadd1 h)
  have haddB : mintedShares w.self a0.raw a1.raw + (w.self.shares ctx.sender).raw <
      wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (addLiquidity_reverts_on_add_bal a0 a1 hpos0 hpos1 hminted hprod
        hadd0 hadd1 haddS h)
  exact ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB⟩

/-- Reduce a well-formed `addLiquidity` to the two token pulls + emit on post-storage. -/
theorem addLiquidity_to_tail (a0 : Amount asset0) (a1 : Amount asset1)
    (h : AddLiqOk ctx w a0 a1) :
    let minted := Amount.ofWord (mintedShares w.self a0.raw a1.raw)
    Tx.run (addLiquidity a0 a1) ctx w =
      Tx.run (
        safeTransferFrom (E := Event) w.self.token0 ctx.sender ctx.self a0
          Error.TransferFailed >>= fun _ =>
        safeTransferFrom (E := Event) w.self.token1 ctx.sender ctx.self a1
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.AddLiquidity ctx.sender a0 a1 minted) >>= fun _ =>
        (pure minted : Tx Storage ExtState Event Error (Amount lpShare)))
        ctx { w with self := addLiquidityPost w.self ctx.sender a0.raw a1.raw } := by
  rcases h with ⟨hpos0, hpos1, hminted, hprod, hadd0, hadd1, haddS, haddB⟩
  rw [addLiq_after_mint a0 a1 hpos0 hpos1 hprod hminted]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos haddS, run_store_bind, run_loadMap_bind]
  simp only [run_hAdd_bind]
  rw [if_pos haddB, run_storeMap_bind]
  refine (run_read_token0_then_token1 (fun t0 t1 =>
    safeTransferFrom (E := Event) t0 ctx.sender ctx.self a0 Error.TransferFailed >>=
      fun _ =>
    safeTransferFrom (E := Event) t1 ctx.sender ctx.self a1 Error.TransferFailed >>=
      fun _ =>
    Tx.emit (.AddLiquidity ctx.sender a0 a1
      ⟨mintedShares w.self a0.raw a1.raw⟩) >>= fun _ =>
    (pure (⟨mintedShares w.self a0.raw a1.raw⟩ : Amount lpShare)))).trans ?_
  simp only [addLiquidityPost, mintedShares, Amount.update_raw, Amount.raw_add,
    Amount.raw_ofWord, Amount.ofWord_add_right, Amount.ofWord_raw, Amount.mk_raw]
  rfl

theorem addLiquidity_post (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : AddLiqOk ctx w a0 a1)
    (hrun : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    n = Amount.ofWord (mintedShares w.self a0.raw a1.raw) ∧
      w'.self = addLiquidityPost w.self ctx.sender a0.raw a1.raw ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.AddLiquidity ctx.sender a0 a1
        (Amount.ofWord (mintedShares w.self a0.raw a1.raw))] := by
  have heq := addLiquidity_to_tail a0 a1 h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := addLiquidityPost w.self ctx.sender a0.raw a1.raw }) hrun with
    ⟨w1, _, hs1, ho1, hl1, hrun⟩
  rcases ok_of_safeTF_bind (w₀ := w1) hrun with ⟨w2, _, hs2, ho2, hl2, hrun⟩
  have ⟨hn, hs3, ho3, hl3, _⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨hn, hs3.trans (hs2.trans hs1), ho3.trans (ho2.trans ho1),
    by simp [hl1, hl2, hl3]⟩

theorem addLiquidity_call (a0 : Amount asset0) (a1 : Amount asset1)
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : AddLiqOk ctx w a0 a1)
    (hrun : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    ∃ w1 w2,
      Tx.run (tfCall w.self.token0 ctx.sender ctx.self a0) ctx w =
        .ok (true, w1) ∧
      Tx.run (tfCall w.self.token1 ctx.sender ctx.self a1) ctx
          { w with ext := w1.ext } = .ok (true, w2) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w2.self = w.self ∧ w2.oracle = w.oracle ∧
      w'.ext = w2.ext ∧ w'.oracle = w.oracle ∧
      w'.self = addLiquidityPost w.self ctx.sender a0.raw a1.raw := by
  have ⟨_, hσ, hor, _⟩ := addLiquidity_post a0 a1 h hrun
  have heq := addLiquidity_to_tail a0 a1 h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := addLiquidityPost w.self ctx.sender a0.raw a1.raw }) hrun with
    ⟨w1, hcall0, hs1, ho1, hl1, hrun⟩
  have htf0 := transferFrom_call_ignore_self
    (σ := addLiquidityPost w.self ctx.sender a0.raw a1.raw) hcall0
  rcases ok_of_safeTF_bind (w₀ := w1) hrun with ⟨w2, hcall1, hs2, ho2, hl2, hrun⟩
  have : w1 = { w with
      self := addLiquidityPost w.self ctx.sender a0.raw a1.raw
      ext := w1.ext } :=
    eq_self_ext hs1 ho1 hl1
  have htf1 := transferFrom_call_ignore_self
    (w := { w with ext := w1.ext })
    (σ := addLiquidityPost w.self ctx.sender a0.raw a1.raw)
    (this ▸ hcall1)
  have ⟨_, _, _, _, hext⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨{ w with ext := w1.ext }, { w with ext := w2.ext },
    htf0.1, htf1.1, rfl, rfl, rfl, rfl, rfl, hext, hor, hσ⟩

/-! ### removeLiquidity -/

theorem removeLiquidity_reverts_on_nonpos (s : Amount lpShare) (hpos : ¬ 0 < s) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .Zero) := by
  rw [removeLiquidity, run_req_false hpos]

theorem removeLiquidity_reverts_on_insufficient (s : Amount lpShare)
    (hpos : 0 < s) (hbal : ¬ s ≤ w.self.shares ctx.sender) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .InsufficientShares) := by
  rw [removeLiquidity, run_req_true hpos, run_sender_bind, run_loadMap_bind,
    run_req_false hbal]

theorem removeLiquidity_reverts_on_zero_supply (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hts : w.self.totalShares.raw = 0) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .Zero) := by
  have hts' : ¬ 0 < w.self.totalShares := by
    simpa [Amount.lt_iff, Amount.raw_ofNat] using Nat.not_lt.mpr (Nat.le_of_eq hts)
  rw [removeLiquidity, run_req_true hpos, run_sender_bind, run_loadMap_bind,
    run_req_true hbal, run_load_bind, run_load_bind, run_load_bind,
    run_req_false hts']

/-- `removeLiquidity` after the share/supply guards, at the first `mulDiv↓`.
First action is `>>=`; the rest stays a `do` so later peels match. -/
private theorem removeLiq_after_supply (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw) :
    Tx.run (removeLiquidity s) ctx w =
      Tx.run (
        Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
          (ε := Error) w.self.reserve0 s w.self.totalShares >>= fun out0 => do
          let out1 ← w.self.reserve1 mulDiv↓ s / w.self.totalShares
          Tx.require (0 < out0) .ZeroOut
          Tx.require (0 < out1) .ZeroOut
          let bal' ← w.self.shares ctx.sender -? s
          write shares[ctx.sender] bal'
          let ts' ← w.self.totalShares -? s
          write totalShares ts'
          let r0' ← w.self.reserve0 -? out0
          write reserve0 r0'
          let r1' ← w.self.reserve1 -? out1
          write reserve1 r1'
          let t0 ← read token0
          let t1 ← read token1
          safeTransfer t0 ctx.sender out0 .TransferFailed
          safeTransfer t1 ctx.sender out1 .TransferFailed
          Tx.emit (.RemoveLiquidity ctx.sender out0 out1 s)
          pure (out0, out1)
        : M (Amount asset0 × Amount asset1)) ctx w := by
  have hsupA : 0 < w.self.totalShares := by simpa [Amount.lt_iff] using hsup
  rw [removeLiquidity, run_req_true hpos, run_sender_bind, run_loadMap_bind,
    run_req_true hbal, run_load_bind, run_load_bind, run_load_bind,
    run_req_true hsupA]

theorem removeLiquidity_reverts_on_mul0 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul : ¬ w.self.reserve0.raw * s.raw < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  rw [removeLiq_after_supply s hpos hbal hsup]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_neg hmul]

/-- After a successful first `mulDiv↓`, at the second `mulDiv↓`. -/
private theorem removeLiq_after_mul0 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound) :
    Tx.run (removeLiquidity s) ctx w =
      Tx.run (do
        let out1 ← w.self.reserve1 mulDiv↓ s / w.self.totalShares
        Tx.require (0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
          Amount asset0)) .ZeroOut
        Tx.require (0 < out1) .ZeroOut
        let bal' ← w.self.shares ctx.sender -? s
        write shares[ctx.sender] bal'
        let ts' ← w.self.totalShares -? s
        write totalShares ts'
        let r0' ← w.self.reserve0 -?
          (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ : Amount asset0)
        write reserve0 r0'
        let r1' ← w.self.reserve1 -? out1
        write reserve1 r1'
        let t0 ← read token0
        let t1 ← read token1
        safeTransfer t0 ctx.sender
          (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ : Amount asset0)
          .TransferFailed
        safeTransfer t1 ctx.sender out1 .TransferFailed
        Tx.emit (.RemoveLiquidity ctx.sender
          (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ : Amount asset0)
          out1 s)
        pure ((⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ : Amount asset0),
          out1)
        : M (Amount asset0 × Amount asset1)) ctx w := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  rw [removeLiq_after_supply s hpos hbal hsup]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul0]

theorem removeLiquidity_reverts_on_mul1 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul : ¬ w.self.reserve1.raw * s.raw < wordBound) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .overflow) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_neg hmul]

theorem removeLiquidity_reverts_on_zero_out0 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout : ¬ 0 < (redeemed w.self s.raw).1) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  have hreq : ¬ 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_false hreq]

theorem removeLiquidity_reverts_on_zero_out1 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout : ¬ 0 < (redeemed w.self s.raw).2) :
    Tx.run (removeLiquidity s) ctx w = .error (.user .ZeroOut) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  have h0a : 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout0
  have hreq : ¬ 0 < (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) := by simpa [Amount.lt_iff, redeemed] using hout
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_true h0a, run_req_false hreq]

theorem removeLiquidity_reverts_on_sub_shares (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hsubS : ¬ s ≤ w.self.totalShares) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .underflow) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  have h0a : 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout0
  have h1a : 0 < (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) := by simpa [Amount.lt_iff, redeemed] using hout1
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_true h0a, run_req_true h1a]
  simp only [run_hSub_bind]
  have hbalR : s.raw ≤ (w.self.shares ctx.sender).raw := by
    simpa [Amount.le_iff] using hbal
  rw [if_pos hbalR, run_storeMap_bind]
  simp only [run_hSub_bind]
  have hsubSR : ¬ s.raw ≤ w.self.totalShares.raw := by
    simpa [Amount.le_iff] using hsubS
  rw [if_neg hsubSR]

theorem removeLiquidity_reverts_on_sub_r0 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hsubS : s ≤ w.self.totalShares)
    (hle0 : ¬ (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .underflow) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  have h0a : 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout0
  have h1a : 0 < (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) := by simpa [Amount.lt_iff, redeemed] using hout1
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_true h0a, run_req_true h1a]
  simp only [run_hSub_bind]
  have hbalR : s.raw ≤ (w.self.shares ctx.sender).raw := by
    simpa [Amount.le_iff] using hbal
  rw [if_pos hbalR, run_storeMap_bind]
  simp only [run_hSub_bind]
  have hsubSR : s.raw ≤ w.self.totalShares.raw := by
    simpa [Amount.le_iff] using hsubS
  rw [if_pos hsubSR, run_store_bind]
  simp only [run_hSub_bind]
  have hle0R : ¬ w.self.reserve0.raw * s.raw / w.self.totalShares.raw ≤
      w.self.reserve0.raw := by simpa [redeemed] using hle0
  rw [if_neg hle0R]

theorem removeLiquidity_reverts_on_sub_r1 (s : Amount lpShare)
    (hpos : 0 < s) (hbal : s ≤ w.self.shares ctx.sender)
    (hsup : 0 < w.self.totalShares.raw)
    (hmul0 : w.self.reserve0.raw * s.raw < wordBound)
    (hmul1 : w.self.reserve1.raw * s.raw < wordBound)
    (hout0 : 0 < (redeemed w.self s.raw).1)
    (hout1 : 0 < (redeemed w.self s.raw).2)
    (hsubS : s ≤ w.self.totalShares)
    (hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw)
    (hle1 : ¬ (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw) :
    Tx.run (removeLiquidity s) ctx w = .error (.arith .underflow) := by
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  have h0a : 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout0
  have h1a : 0 < (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) := by simpa [Amount.lt_iff, redeemed] using hout1
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_true h0a, run_req_true h1a]
  simp only [run_hSub_bind]
  have hbalR : s.raw ≤ (w.self.shares ctx.sender).raw := by
    simpa [Amount.le_iff] using hbal
  rw [if_pos hbalR, run_storeMap_bind]
  simp only [run_hSub_bind]
  have hsubSR : s.raw ≤ w.self.totalShares.raw := by
    simpa [Amount.le_iff] using hsubS
  rw [if_pos hsubSR, run_store_bind]
  simp only [run_hSub_bind]
  have hle0R : w.self.reserve0.raw * s.raw / w.self.totalShares.raw ≤
      w.self.reserve0.raw := by simpa [redeemed] using hle0
  rw [if_pos hle0R, run_store_bind]
  simp only [run_hSub_bind]
  have hle1R : ¬ w.self.reserve1.raw * s.raw / w.self.totalShares.raw ≤
      w.self.reserve1.raw := by simpa [redeemed] using hle1
  rw [if_neg hle1R]

structure RemoveOk (ctx : Ctx) (w : World Storage ExtState Event)
    (s : Amount lpShare) : Prop where
  pos : 0 < s
  bal : s ≤ w.self.shares ctx.sender
  supply : 0 < w.self.totalShares.raw
  mul0 : w.self.reserve0.raw * s.raw < wordBound
  mul1 : w.self.reserve1.raw * s.raw < wordBound
  out0 : 0 < (redeemed w.self s.raw).1
  out1 : 0 < (redeemed w.self s.raw).2
  subS : s ≤ w.self.totalShares
  le0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw
  le1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw

theorem removeLiquidity_ok_of_run {s : Amount lpShare}
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (hrun : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    RemoveOk ctx w s := by
  have hpos : 0 < s := by
    by_contra h; exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_nonpos s h)
  have hbal : s ≤ w.self.shares ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_insufficient s hpos h)
  have hsup : 0 < w.self.totalShares.raw := by
    by_contra h
    have hz : w.self.totalShares.raw = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h)
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_zero_supply s hpos hbal hz)
  have hmul0 : w.self.reserve0.raw * s.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul0 s hpos hbal hsup h)
  have hmul1 : w.self.reserve1.raw * s.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (removeLiquidity_reverts_on_mul1 s hpos hbal hsup hmul0 h)
  have hout0 : 0 < (redeemed w.self s.raw).1 := by
    by_contra h
    exact Tx.run_ok_error hrun
      (removeLiquidity_reverts_on_zero_out0 s hpos hbal hsup hmul0 hmul1 h)
  have hout1 : 0 < (redeemed w.self s.raw).2 := by
    by_contra h
    exact Tx.run_ok_error hrun
      (removeLiquidity_reverts_on_zero_out1 s hpos hbal hsup hmul0 hmul1 hout0 h)
  have hsubS : s ≤ w.self.totalShares := by
    by_contra h
    exact Tx.run_ok_error hrun
      (removeLiquidity_reverts_on_sub_shares s hpos hbal hsup hmul0 hmul1 hout0 hout1 h)
  have hle0 : (redeemed w.self s.raw).1 ≤ w.self.reserve0.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (removeLiquidity_reverts_on_sub_r0 s hpos hbal hsup hmul0 hmul1 hout0 hout1 hsubS h)
  have hle1 : (redeemed w.self s.raw).2 ≤ w.self.reserve1.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (removeLiquidity_reverts_on_sub_r1 s hpos hbal hsup hmul0 hmul1 hout0 hout1
        hsubS hle0 h)
  exact ⟨hpos, hbal, hsup, hmul0, hmul1, hout0, hout1, hsubS, hle0, hle1⟩

theorem removeLiquidity_to_tail (s : Amount lpShare) (h : RemoveOk ctx w s) :
    let out0 := Amount.ofWord (redeemed w.self s.raw).1
    let out1 := Amount.ofWord (redeemed w.self s.raw).2
    Tx.run (removeLiquidity s) ctx w =
      Tx.run (
        safeTransfer (E := Event) w.self.token0 ctx.sender out0
          Error.TransferFailed >>= fun _ =>
        safeTransfer (E := Event) w.self.token1 ctx.sender out1
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.RemoveLiquidity ctx.sender out0 out1 s) >>= fun _ =>
        (pure (out0, out1) :
          Tx Storage ExtState Event Error (Amount asset0 × Amount asset1)))
        ctx { w with self := removeLiquidityPost w.self ctx.sender s.raw } := by
  rcases h with ⟨hpos, hbal, hsup, hmul0, hmul1, hout0, hout1, hsubS, hle0, hle1⟩
  have h0a : 0 < (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) := by simpa [Amount.lt_iff, redeemed] using hout0
  have h1a : 0 < (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) := by simpa [Amount.lt_iff, redeemed] using hout1
  have hout0' : (⟨w.self.reserve0.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset0) = Amount.ofWord (redeemed w.self s.raw).1 := by
    simp [redeemed]
  have hout1' : (⟨w.self.reserve1.raw * s.raw / w.self.totalShares.raw⟩ :
      Amount asset1) = Amount.ofWord (redeemed w.self s.raw).2 := by
    simp [redeemed]
  have htsn : w.self.totalShares.raw ≠ 0 := Nat.ne_of_gt hsup
  rw [removeLiq_after_mul0 s hpos hbal hsup hmul0]
  simp only [run_mulDivDown_bind]
  rw [if_neg htsn, if_pos hmul1, run_req_true h0a, run_req_true h1a]
  simp only [run_hSub_bind]
  have hbalR : s.raw ≤ (w.self.shares ctx.sender).raw := by
    simpa [Amount.le_iff] using hbal
  rw [if_pos hbalR, run_storeMap_bind]
  simp only [run_hSub_bind]
  have hsubSR : s.raw ≤ w.self.totalShares.raw := by
    simpa [Amount.le_iff] using hsubS
  rw [if_pos hsubSR, run_store_bind]
  simp only [run_hSub_bind]
  have hle0R : w.self.reserve0.raw * s.raw / w.self.totalShares.raw ≤
      w.self.reserve0.raw := by simpa [redeemed] using hle0
  rw [if_pos hle0R, run_store_bind]
  simp only [run_hSub_bind]
  have hle1R : w.self.reserve1.raw * s.raw / w.self.totalShares.raw ≤
      w.self.reserve1.raw := by simpa [redeemed] using hle1
  rw [if_pos hle1R, run_store_bind]
  rw [hout0', hout1']
  refine (run_read_token0_then_token1 (fun t0 t1 =>
    safeTransfer (E := Event) t0 ctx.sender
      (Amount.ofWord (redeemed w.self s.raw).1) Error.TransferFailed >>=
      fun _ =>
    safeTransfer (E := Event) t1 ctx.sender
      (Amount.ofWord (redeemed w.self s.raw).2) Error.TransferFailed >>=
      fun _ =>
    Tx.emit (.RemoveLiquidity ctx.sender
      (Amount.ofWord (redeemed w.self s.raw).1)
      (Amount.ofWord (redeemed w.self s.raw).2) s) >>= fun _ =>
    (pure (Amount.ofWord (redeemed w.self s.raw).1,
      Amount.ofWord (redeemed w.self s.raw).2) :
      Tx Storage ExtState Event Error (Amount asset0 × Amount asset1)))).trans ?_
  simp only [removeLiquidityPost, redeemed, hout0', hout1', Amount.update_raw,
    Amount.raw_sub, Amount.raw_ofWord, Amount.ofWord_sub_left, Amount.ofWord_raw,
    Amount.mk_raw]
  try rfl

theorem removeLiquidity_post (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : RemoveOk ctx w s)
    (hrun : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p = (Amount.ofWord (redeemed w.self s.raw).1,
          Amount.ofWord (redeemed w.self s.raw).2) ∧
      w'.self = removeLiquidityPost w.self ctx.sender s.raw ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.RemoveLiquidity ctx.sender
        (Amount.ofWord (redeemed w.self s.raw).1)
        (Amount.ofWord (redeemed w.self s.raw).2) s] := by
  have heq := removeLiquidity_to_tail s h
  rw [heq] at hrun
  rcases ok_of_safeTR_bind (w₀ := { w with
      self := removeLiquidityPost w.self ctx.sender s.raw }) hrun with
    ⟨w1, _, hs1, ho1, hl1, hrun⟩
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, _, hs2, ho2, hl2, hrun⟩
  have ⟨hn, hs3, ho3, hl3, _⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨hn, hs3.trans (hs2.trans hs1), ho3.trans (ho2.trans ho1),
    by simp [hl1, hl2, hl3]⟩

theorem removeLiquidity_call (s : Amount lpShare)
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : RemoveOk ctx w s)
    (hrun : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    ∃ w1 w2,
      Tx.run (trCall w.self.token0 ctx.sender
          (Amount.ofWord (redeemed w.self s.raw).1)) ctx w =
        .ok (true, w1) ∧
      Tx.run (trCall w.self.token1 ctx.sender
          (Amount.ofWord (redeemed w.self s.raw).2)) ctx
          { w with ext := w1.ext } = .ok (true, w2) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w2.self = w.self ∧ w2.oracle = w.oracle ∧
      w'.ext = w2.ext ∧ w'.oracle = w.oracle ∧
      w'.self = removeLiquidityPost w.self ctx.sender s.raw := by
  have ⟨_, hσ, hor, _⟩ := removeLiquidity_post s h hrun
  have heq := removeLiquidity_to_tail s h
  rw [heq] at hrun
  rcases ok_of_safeTR_bind (w₀ := { w with
      self := removeLiquidityPost w.self ctx.sender s.raw }) hrun with
    ⟨w1, hcall0, hs1, ho1, hl1, hrun⟩
  have htr0 := transfer_call_ignore_self
    (σ := removeLiquidityPost w.self ctx.sender s.raw) hcall0
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, hcall1, hs2, ho2, hl2, hrun⟩
  have : w1 = { w with
      self := removeLiquidityPost w.self ctx.sender s.raw
      ext := w1.ext } :=
    eq_self_ext hs1 ho1 hl1
  have htr1 := transfer_call_ignore_self
    (w := { w with ext := w1.ext })
    (σ := removeLiquidityPost w.self ctx.sender s.raw)
    (this ▸ hcall1)
  have ⟨_, _, _, _, hext⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨{ w with ext := w1.ext }, { w with ext := w2.ext },
    htr0.1, htr1.1, rfl, rfl, rfl, rfl, rfl, hext, hor, hσ⟩

/-! ### swap0for1 / swap1for0 -/

private abbrev swap0Out (σ : Storage) (dx : Nat) : Nat :=
  amountOut σ.reserve0.raw σ.reserve1.raw dx

private abbrev swap1Out (σ : Storage) (dx : Nat) : Nat :=
  amountOut σ.reserve1.raw σ.reserve0.raw dx

structure Swap0Ok (w : World Storage ExtState Event)
    (dx : Amount asset0) (minOut : Amount asset1) : Prop where
  pos : 0 < dx
  r0 : 0 < w.self.reserve0.raw
  r1 : 0 < w.self.reserve1.raw
  feeMul : dx.raw * 9970 < wordBound
  den : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound
  outMul : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound
  protoMul : swapFee dx.raw * coeffOf w.self < wordBound
  lp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw
  min : minOut.raw ≤ swap0Out w.self dx.raw
  outPos : 0 < swap0Out w.self dx.raw
  taken : protoOf w.self dx.raw ≤ dx.raw
  add0 : w.self.reserve0.raw + (dx.raw - protoOf w.self dx.raw) < wordBound
  sub1 : swap0Out w.self dx.raw ≤ w.self.reserve1.raw
  acc : w.self.protocolFees0.raw + protoOf w.self dx.raw < wordBound

structure Swap1Ok (w : World Storage ExtState Event)
    (dx : Amount asset1) (minOut : Amount asset0) : Prop where
  pos : 0 < dx
  r0 : 0 < w.self.reserve0.raw
  r1 : 0 < w.self.reserve1.raw
  feeMul : dx.raw * 9970 < wordBound
  den : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound
  outMul : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound
  protoMul : swapFee dx.raw * coeffOf w.self < wordBound
  lp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw
  min : minOut.raw ≤ swap1Out w.self dx.raw
  outPos : 0 < swap1Out w.self dx.raw
  taken : protoOf w.self dx.raw ≤ dx.raw
  add1 : w.self.reserve1.raw + (dx.raw - protoOf w.self dx.raw) < wordBound
  sub0 : swap1Out w.self dx.raw ≤ w.self.reserve0.raw
  acc : w.self.protocolFees1.raw + protoOf w.self dx.raw < wordBound

private theorem swap0_denNe {dx : Amount asset0}
    (hr0 : 0 < w.self.reserve0.raw) :
    w.self.reserve0.raw + dxFeeLess dx.raw ≠ 0 :=
  Nat.ne_of_gt (Nat.add_pos_left hr0 _)

private theorem swap1_denNe {dx : Amount asset1}
    (hr1 : 0 < w.self.reserve1.raw) :
    w.self.reserve1.raw + dxFeeLess dx.raw ≠ 0 :=
  Nat.ne_of_gt (Nat.add_pos_left hr1 _)

private theorem swap0_quote (h : Swap0Ok w dx minOut) :
    SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
  ⟨h.feeMul, h.den, swap0_denNe (dx := dx) h.r0, h.outMul,
    by simpa [coeffBps_raw] using h.protoMul, h.lp⟩

private theorem swap1_quote (h : Swap1Ok w dx minOut) :
    SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
  ⟨h.feeMul, h.den, swap1_denNe (dx := dx) h.r1, h.outMul,
    by simpa [coeffBps_raw] using h.protoMul, h.lp⟩

private theorem protoMul_coeff {dx : Nat} :
    swapFee dx * (coeffBps w.self).raw < wordBound ↔
      swapFee dx * coeffOf w.self < wordBound := by
  simp [coeffBps_raw]

private theorem swap0_after_quote (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw) :
    Tx.run (swap0for1 dx minOut) ctx w =
      Tx.run (swapOut w.self.reserve0 w.self.reserve1 dx (coeffBps w.self)
        fun out protoFee _lpFee => do
          Tx.require (minOut ≤ out) .InsufficientOutput
          Tx.require (0 < out) .ZeroOut
          let taken ← dx -? protoFee
          let r0' ← w.self.reserve0 +? taken
          write reserve0 r0'
          let r1' ← w.self.reserve1 -? out
          write reserve1 r1'
          let acc ← read protocolFees0
          let acc' ← acc +? protoFee
          write protocolFees0 acc'
          let who ← Tx.sender
          let me ← Tx.selfAddress
          let t0 ← read token0
          let t1 ← read token1
          safeTransferFrom t0 who me dx .TransferFailed
          safeTransfer t1 who out .TransferFailed
          Tx.emit (.Swap0for1 who dx out)
          return out) ctx w := by
  have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
  rw [swap0for1, run_req_true hpos, run_load_bind, run_load_bind,
    run_req_true hr0A, run_req_true hr1A, run_load_bind, run_load_bind]
  rw [Tx.run_ite]
  by_cases hft : w.self.feeTo = 0
  · rw [if_pos hft]
    simp only [Tx.pure_bind]
    have hc : coeffBps w.self = 0 := by simp [coeffBps, hft]
    rw [hc]
  · rw [if_neg hft]
    simp only [Tx.pure_bind]
    have hc : coeffBps w.self = w.self.protocolShareBps := by simp [coeffBps, hft]
    rw [hc]

private theorem swap1_after_quote (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw) :
    Tx.run (swap1for0 dx minOut) ctx w =
      Tx.run (swapOut w.self.reserve1 w.self.reserve0 dx (coeffBps w.self)
        fun out protoFee _lpFee => do
          Tx.require (minOut ≤ out) .InsufficientOutput
          Tx.require (0 < out) .ZeroOut
          let taken ← dx -? protoFee
          let r1' ← w.self.reserve1 +? taken
          write reserve1 r1'
          let r0' ← w.self.reserve0 -? out
          write reserve0 r0'
          let acc ← read protocolFees1
          let acc' ← acc +? protoFee
          write protocolFees1 acc'
          let who ← Tx.sender
          let me ← Tx.selfAddress
          let t1 ← read token1
          let t0 ← read token0
          safeTransferFrom t1 who me dx .TransferFailed
          safeTransfer t0 who out .TransferFailed
          Tx.emit (.Swap1for0 who dx out)
          return out) ctx w := by
  have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
  have hr1A : 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using hr1
  rw [swap1for0, run_req_true hpos, run_load_bind, run_load_bind,
    run_req_true hr0A, run_req_true hr1A, run_load_bind, run_load_bind]
  rw [Tx.run_ite]
  by_cases hft : w.self.feeTo = 0
  · rw [if_pos hft]
    simp only [Tx.pure_bind]
    have hc : coeffBps w.self = 0 := by simp [coeffBps, hft]
    rw [hc]
  · rw [if_neg hft]
    simp only [Tx.pure_bind]
    have hc : coeffBps w.self = w.self.protocolShareBps := by simp [coeffBps, hft]
    rw [hc]

theorem swap0for1_reverts_on_fee_mul (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : ¬ dx.raw * 9970 < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap0_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_fee_mul _ _ _ _ _ hfee

theorem swap0for1_reverts_on_den (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : ¬ w.self.reserve0.raw + dxFeeLess dx.raw < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap0_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_den _ _ _ _ _ hfee hden

theorem swap0for1_reverts_on_out_mul (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : ¬ w.self.reserve1.raw * dxFeeLess dx.raw < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap0_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_out_mul _ _ _ _ _ hfee hden (swap0_denNe (dx := dx) hr0) houtM

theorem swap0for1_reverts_on_proto_mul (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : ¬ swapFee dx.raw * coeffOf w.self < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap0_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_proto_mul _ _ _ _ _
    hfee hden (swap0_denNe (dx := dx) hr0) houtM
    ((protoMul_coeff (dx := dx.raw)).not.mpr hprotoM)

theorem swap0for1_reverts_on_lp (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : ¬ swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .underflow) := by
  rw [swap0_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_lp _ _ _ _ _
    hfee hden (swap0_denNe (dx := dx) hr0) houtM
    ((protoMul_coeff (dx := dx.raw)).mpr hprotoM) hlp

private theorem swap0_k (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self)) :
    Tx.run (swap0for1 dx minOut) ctx w =
      Tx.run (do
        Tx.require (minOut ≤ (⟨swap0Out w.self dx.raw⟩ : Amount asset1))
          .InsufficientOutput
        Tx.require (0 < (⟨swap0Out w.self dx.raw⟩ : Amount asset1)) .ZeroOut
        let taken ← dx -? (⟨protoOf w.self dx.raw⟩ : Amount asset0)
        let r0' ← w.self.reserve0 +? taken
        write reserve0 r0'
        let r1' ← w.self.reserve1 -? (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
        write reserve1 r1'
        let acc ← read protocolFees0
        let acc' ← acc +? (⟨protoOf w.self dx.raw⟩ : Amount asset0)
        write protocolFees0 acc'
        let who ← Tx.sender
        let me ← Tx.selfAddress
        let t0 ← read token0
        let t1 ← read token1
        safeTransferFrom t0 who me dx .TransferFailed
        safeTransfer t1 who (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
          .TransferFailed
        Tx.emit (.Swap0for1 who dx ⟨swap0Out w.self dx.raw⟩)
        pure (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
        : M (Amount asset1)) ctx w := by
  have hout :
      (⟨swapOutOut w.self.reserve0.raw w.self.reserve1.raw dx.raw⟩ : Amount asset1) =
        ⟨swap0Out w.self dx.raw⟩ := by
    simp [swap0Out, amountOut, swapOutOut]
  have hpr :
      (⟨swapOutProto dx.raw (coeffBps w.self)⟩ : Amount asset0) =
        ⟨protoOf w.self dx.raw⟩ := by
    simp [swapOutProto_coeff]
  rw [swap0_after_quote dx minOut hpos hr0 hr1, run_swapOut _ _ _ _ _ hQ, hout, hpr]

theorem swap0for1_reverts_on_min (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : ¬ minOut.raw ≤ swap0Out w.self dx.raw) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.user .InsufficientOutput) := by
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  have hreq : ¬ minOut ≤ (⟨swap0Out w.self dx.raw⟩ : Amount asset1) := by
    simpa [Amount.le_iff] using hmin
  rw [swap0_k dx minOut hpos hr0 hr1 hQ, run_req_false hreq]

theorem swap0for1_reverts_on_zero_out (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap0Out w.self dx.raw)
    (houtP : ¬ 0 < swap0Out w.self dx.raw) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.user .ZeroOut) := by
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  have hminA : minOut ≤ (⟨swap0Out w.self dx.raw⟩ : Amount asset1) := by
    simpa [Amount.le_iff] using hmin
  have hreq : ¬ 0 < (⟨swap0Out w.self dx.raw⟩ : Amount asset1) := by
    simpa [Amount.lt_iff] using houtP
  rw [swap0_k dx minOut hpos hr0 hr1 hQ, run_req_true hminA, run_req_false hreq]

private theorem swap0_after_req (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self))
    (hmin : minOut.raw ≤ swap0Out w.self dx.raw)
    (houtP : 0 < swap0Out w.self dx.raw) :
    Tx.run (swap0for1 dx minOut) ctx w =
      Tx.run (do
        let taken ← dx -? (⟨protoOf w.self dx.raw⟩ : Amount asset0)
        let r0' ← w.self.reserve0 +? taken
        write reserve0 r0'
        let r1' ← w.self.reserve1 -? (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
        write reserve1 r1'
        let acc ← read protocolFees0
        let acc' ← acc +? (⟨protoOf w.self dx.raw⟩ : Amount asset0)
        write protocolFees0 acc'
        let who ← Tx.sender
        let me ← Tx.selfAddress
        let t0 ← read token0
        let t1 ← read token1
        safeTransferFrom t0 who me dx .TransferFailed
        safeTransfer t1 who (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
          .TransferFailed
        Tx.emit (.Swap0for1 who dx ⟨swap0Out w.self dx.raw⟩)
        pure (⟨swap0Out w.self dx.raw⟩ : Amount asset1)
        : M (Amount asset1)) ctx w := by
  have hminA : minOut ≤ (⟨swap0Out w.self dx.raw⟩ : Amount asset1) := by
    simpa [Amount.le_iff] using hmin
  have houtA : 0 < (⟨swap0Out w.self dx.raw⟩ : Amount asset1) := by
    simpa [Amount.lt_iff] using houtP
  rw [swap0_k dx minOut hpos hr0 hr1 hQ, run_req_true hminA, run_req_true houtA]

theorem swap0for1_reverts_on_add0 (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap0Out w.self dx.raw)
    (houtP : 0 < swap0Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd0 : ¬ w.self.reserve0.raw + (dx.raw - protoOf w.self dx.raw) < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap0_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_neg hadd0]

theorem swap0for1_reverts_on_sub1 (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap0Out w.self dx.raw)
    (houtP : 0 < swap0Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd0 : w.self.reserve0.raw + (dx.raw - protoOf w.self dx.raw) < wordBound)
    (hsub1 : ¬ swap0Out w.self dx.raw ≤ w.self.reserve1.raw) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .underflow) := by
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap0_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_neg hsub1]

theorem swap0for1_reverts_on_acc (dx : Amount asset0) (minOut : Amount asset1)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap0Out w.self dx.raw)
    (houtP : 0 < swap0Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd0 : w.self.reserve0.raw + (dx.raw - protoOf w.self dx.raw) < wordBound)
    (hsub1 : swap0Out w.self dx.raw ≤ w.self.reserve1.raw)
    (hacc : ¬ w.self.protocolFees0.raw + protoOf w.self dx.raw < wordBound) :
    Tx.run (swap0for1 dx minOut) ctx w = .error (.arith .overflow) := by
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap0_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_pos hsub1, run_store_bind, run_load_bind]
  simp only [run_hAdd_bind]
  rw [if_neg hacc]

theorem swap0for1_ok_of_run {dx : Amount asset0} {minOut : Amount asset1}
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    Swap0Ok w dx minOut := by
  have hpos : 0 < dx := by
    by_contra h
    rw [swap0for1, run_req_false h] at hrun
    cases hrun
  have hr0 : 0 < w.self.reserve0.raw := by
    by_contra h
    have hz : ¬ 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using h
    rw [swap0for1, run_req_true hpos, run_load_bind, run_load_bind,
      run_req_false hz] at hrun
    cases hrun
  have hr1 : 0 < w.self.reserve1.raw := by
    by_contra h
    have hz : ¬ 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using h
    have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
    rw [swap0for1, run_req_true hpos, run_load_bind, run_load_bind,
      run_req_true hr0A, run_req_false hz] at hrun
    cases hrun
  have hfee : dx.raw * 9970 < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_fee_mul dx minOut hpos hr0 hr1 h)
  have hden : w.self.reserve0.raw + dxFeeLess dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (swap0for1_reverts_on_den dx minOut hpos hr0 hr1 hfee h)
  have houtM : w.self.reserve1.raw * dxFeeLess dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_out_mul dx minOut hpos hr0 hr1 hfee hden h)
  have hprotoM : swapFee dx.raw * coeffOf w.self < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_proto_mul dx minOut hpos hr0 hr1 hfee hden houtM h)
  have hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_lp dx minOut hpos hr0 hr1 hfee hden houtM hprotoM h)
  have hmin : minOut.raw ≤ swap0Out w.self dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_min dx minOut hpos hr0 hr1 hfee hden houtM hprotoM hlp h)
  have houtP : 0 < swap0Out w.self dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_zero_out dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin h)
  have htaken : protoOf w.self dx.raw ≤ dx.raw := by
    have hfee' : protoOf w.self dx.raw ≤ swapFee dx.raw := by
      simpa [swapOutProto_coeff] using hlp
    exact Nat.le_trans hfee' (Nat.sub_le _ _)
  have hadd0 : w.self.reserve0.raw + (dx.raw - protoOf w.self dx.raw) < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_add0 dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken h)
  have hsub1 : swap0Out w.self dx.raw ≤ w.self.reserve1.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_sub1 dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken hadd0 h)
  have hacc : w.self.protocolFees0.raw + protoOf w.self dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap0for1_reverts_on_acc dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken hadd0 hsub1 h)
  exact ⟨hpos, hr0, hr1, hfee, hden, houtM, hprotoM, hlp, hmin, houtP, htaken,
    hadd0, hsub1, hacc⟩

theorem swap0for1_to_tail (dx : Amount asset0) (minOut : Amount asset1)
    (h : Swap0Ok w dx minOut) :
    let out := Amount.ofWord (swap0Out w.self dx.raw)
    let proto := protoOf w.self dx.raw
    Tx.run (swap0for1 dx minOut) ctx w =
      Tx.run (
        safeTransferFrom (E := Event) w.self.token0 ctx.sender ctx.self dx
          Error.TransferFailed >>= fun _ =>
        safeTransfer (E := Event) w.self.token1 ctx.sender out
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.Swap0for1 ctx.sender dx out) >>= fun _ =>
        (pure out : Tx Storage ExtState Event Error (Amount asset1)))
        ctx { w with self := swap0Post w.self dx.raw proto (swap0Out w.self dx.raw) } := by
  rcases h with ⟨hpos, hr0, hr1, hfee, hden, houtM, hprotoM, hlp, hmin, houtP,
    htaken, hadd0, hsub1, hacc⟩
  have hQ : SwapOutOk w.self.reserve0.raw w.self.reserve1.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap0_denNe (dx := dx) hr0, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap0_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd0, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_pos hsub1, run_store_bind, run_load_bind]
  simp only [run_hAdd_bind]
  rw [if_pos hacc, run_store_bind, run_sender_bind, run_self_bind]
  refine (run_read_token0_then_token1 (fun t0 t1 =>
    safeTransferFrom (E := Event) t0 ctx.sender ctx.self dx
      Error.TransferFailed >>= fun _ =>
    safeTransfer (E := Event) t1 ctx.sender
      (Amount.ofWord (swap0Out w.self dx.raw)) Error.TransferFailed >>=
      fun _ =>
    Tx.emit (.Swap0for1 ctx.sender dx
      (Amount.ofWord (swap0Out w.self dx.raw))) >>= fun _ =>
    (pure (Amount.ofWord (swap0Out w.self dx.raw)) :
      Tx Storage ExtState Event Error (Amount asset1)))).trans ?_
  simp only [swap0Post, Amount.raw_add, Amount.raw_sub, Amount.raw_ofWord,
    Amount.ofWord_add_right, Amount.ofWord_sub_left, Amount.ofWord_raw,
    Amount.mk_raw]
  rfl

theorem swap0for1_post (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Swap0Ok w dx minOut)
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    out = Amount.ofWord (swap0Out w.self dx.raw) ∧
      w'.self = swap0Post w.self dx.raw (protoOf w.self dx.raw)
        (swap0Out w.self dx.raw) ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Swap0for1 ctx.sender dx
        (Amount.ofWord (swap0Out w.self dx.raw))] := by
  have heq := swap0for1_to_tail (ctx := ctx) dx minOut h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := swap0Post w.self dx.raw (protoOf w.self dx.raw)
        (swap0Out w.self dx.raw) }) hrun with
    ⟨w1, _, hs1, ho1, hl1, hrun⟩
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, _, hs2, ho2, hl2, hrun⟩
  have ⟨hn, hs3, ho3, hl3, _⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨hn, hs3.trans (hs2.trans hs1), ho3.trans (ho2.trans ho1),
    by simp [hl1, hl2, hl3]⟩

theorem swap0for1_call (dx : Amount asset0) (minOut : Amount asset1)
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Swap0Ok w dx minOut)
    (hrun : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    ∃ w1 w2,
      Tx.run (tfCall w.self.token0 ctx.sender ctx.self dx) ctx w =
        .ok (true, w1) ∧
      Tx.run (trCall w.self.token1 ctx.sender
          (Amount.ofWord (swap0Out w.self dx.raw))) ctx
          { w with ext := w1.ext } = .ok (true, w2) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w2.self = w.self ∧ w2.oracle = w.oracle ∧
      w'.ext = w2.ext ∧ w'.oracle = w.oracle ∧
      w'.self = swap0Post w.self dx.raw (protoOf w.self dx.raw)
        (swap0Out w.self dx.raw) := by
  have ⟨_, hσ, hor, _⟩ := swap0for1_post dx minOut h hrun
  have heq := swap0for1_to_tail (ctx := ctx) dx minOut h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := swap0Post w.self dx.raw (protoOf w.self dx.raw)
        (swap0Out w.self dx.raw) }) hrun with
    ⟨w1, hcall0, hs1, ho1, hl1, hrun⟩
  have htf0 := transferFrom_call_ignore_self
    (σ := swap0Post w.self dx.raw (protoOf w.self dx.raw) (swap0Out w.self dx.raw))
    hcall0
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, hcall1, hs2, ho2, hl2, hrun⟩
  have : w1 = { w with
      self := swap0Post w.self dx.raw (protoOf w.self dx.raw)
        (swap0Out w.self dx.raw)
      ext := w1.ext } :=
    eq_self_ext hs1 ho1 hl1
  have htr1 := transfer_call_ignore_self
    (w := { w with ext := w1.ext })
    (σ := swap0Post w.self dx.raw (protoOf w.self dx.raw) (swap0Out w.self dx.raw))
    (this ▸ hcall1)
  have ⟨_, _, _, _, hext⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨{ w with ext := w1.ext }, { w with ext := w2.ext },
    htf0.1, htr1.1, rfl, rfl, rfl, rfl, rfl, hext, hor, hσ⟩

theorem swap1for0_reverts_on_fee_mul (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : ¬ dx.raw * 9970 < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap1_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_fee_mul _ _ _ _ _ hfee

theorem swap1for0_reverts_on_den (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : ¬ w.self.reserve1.raw + dxFeeLess dx.raw < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap1_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_den _ _ _ _ _ hfee hden

theorem swap1for0_reverts_on_out_mul (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : ¬ w.self.reserve0.raw * dxFeeLess dx.raw < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap1_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_out_mul _ _ _ _ _ hfee hden (swap1_denNe (dx := dx) hr1) houtM

theorem swap1for0_reverts_on_proto_mul (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : ¬ swapFee dx.raw * coeffOf w.self < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  rw [swap1_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_proto_mul _ _ _ _ _
    hfee hden (swap1_denNe (dx := dx) hr1) houtM
    ((protoMul_coeff (dx := dx.raw)).not.mpr hprotoM)

theorem swap1for0_reverts_on_lp (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : ¬ swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .underflow) := by
  rw [swap1_after_quote dx minOut hpos hr0 hr1]
  exact run_swapOut_lp _ _ _ _ _
    hfee hden (swap1_denNe (dx := dx) hr1) houtM ((protoMul_coeff (dx := dx.raw)).mpr hprotoM) hlp

private theorem swap1_k (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self)) :
    Tx.run (swap1for0 dx minOut) ctx w =
      Tx.run (do
        Tx.require (minOut ≤ (⟨swap1Out w.self dx.raw⟩ : Amount asset0))
          .InsufficientOutput
        Tx.require (0 < (⟨swap1Out w.self dx.raw⟩ : Amount asset0)) .ZeroOut
        let taken ← dx -? (⟨protoOf w.self dx.raw⟩ : Amount asset1)
        let r1' ← w.self.reserve1 +? taken
        write reserve1 r1'
        let r0' ← w.self.reserve0 -? (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
        write reserve0 r0'
        let acc ← read protocolFees1
        let acc' ← acc +? (⟨protoOf w.self dx.raw⟩ : Amount asset1)
        write protocolFees1 acc'
        let who ← Tx.sender
        let me ← Tx.selfAddress
        let t1 ← read token1
        let t0 ← read token0
        safeTransferFrom t1 who me dx .TransferFailed
        safeTransfer t0 who (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
          .TransferFailed
        Tx.emit (.Swap1for0 who dx ⟨swap1Out w.self dx.raw⟩)
        pure (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
        : M (Amount asset0)) ctx w := by
  have hout :
      (⟨swapOutOut w.self.reserve1.raw w.self.reserve0.raw dx.raw⟩ : Amount asset0) =
        ⟨swap1Out w.self dx.raw⟩ := by
    simp [swap1Out, amountOut, swapOutOut]
  have hpr :
      (⟨swapOutProto dx.raw (coeffBps w.self)⟩ : Amount asset1) =
        ⟨protoOf w.self dx.raw⟩ := by
    simp [swapOutProto_coeff]
  rw [swap1_after_quote dx minOut hpos hr0 hr1, run_swapOut _ _ _ _ _ hQ, hout, hpr]

theorem swap1for0_reverts_on_min (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : ¬ minOut.raw ≤ swap1Out w.self dx.raw) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.user .InsufficientOutput) := by
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  have hreq : ¬ minOut ≤ (⟨swap1Out w.self dx.raw⟩ : Amount asset0) := by
    simpa [Amount.le_iff] using hmin
  rw [swap1_k dx minOut hpos hr0 hr1 hQ, run_req_false hreq]

theorem swap1for0_reverts_on_zero_out (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap1Out w.self dx.raw)
    (houtP : ¬ 0 < swap1Out w.self dx.raw) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.user .ZeroOut) := by
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  have hminA : minOut ≤ (⟨swap1Out w.self dx.raw⟩ : Amount asset0) := by
    simpa [Amount.le_iff] using hmin
  have hreq : ¬ 0 < (⟨swap1Out w.self dx.raw⟩ : Amount asset0) := by
    simpa [Amount.lt_iff] using houtP
  rw [swap1_k dx minOut hpos hr0 hr1 hQ, run_req_true hminA, run_req_false hreq]

private theorem swap1_after_req (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self))
    (hmin : minOut.raw ≤ swap1Out w.self dx.raw)
    (houtP : 0 < swap1Out w.self dx.raw) :
    Tx.run (swap1for0 dx minOut) ctx w =
      Tx.run (do
        let taken ← dx -? (⟨protoOf w.self dx.raw⟩ : Amount asset1)
        let r1' ← w.self.reserve1 +? taken
        write reserve1 r1'
        let r0' ← w.self.reserve0 -? (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
        write reserve0 r0'
        let acc ← read protocolFees1
        let acc' ← acc +? (⟨protoOf w.self dx.raw⟩ : Amount asset1)
        write protocolFees1 acc'
        let who ← Tx.sender
        let me ← Tx.selfAddress
        let t1 ← read token1
        let t0 ← read token0
        safeTransferFrom t1 who me dx .TransferFailed
        safeTransfer t0 who (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
          .TransferFailed
        Tx.emit (.Swap1for0 who dx ⟨swap1Out w.self dx.raw⟩)
        pure (⟨swap1Out w.self dx.raw⟩ : Amount asset0)
        : M (Amount asset0)) ctx w := by
  have hminA : minOut ≤ (⟨swap1Out w.self dx.raw⟩ : Amount asset0) := by
    simpa [Amount.le_iff] using hmin
  have houtA : 0 < (⟨swap1Out w.self dx.raw⟩ : Amount asset0) := by
    simpa [Amount.lt_iff] using houtP
  rw [swap1_k dx minOut hpos hr0 hr1 hQ, run_req_true hminA, run_req_true houtA]

theorem swap1for0_reverts_on_add1 (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap1Out w.self dx.raw)
    (houtP : 0 < swap1Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd1 : ¬ w.self.reserve1.raw + (dx.raw - protoOf w.self dx.raw) < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap1_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_neg hadd1]

theorem swap1for0_reverts_on_sub0 (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap1Out w.self dx.raw)
    (houtP : 0 < swap1Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd1 : w.self.reserve1.raw + (dx.raw - protoOf w.self dx.raw) < wordBound)
    (hsub0 : ¬ swap1Out w.self dx.raw ≤ w.self.reserve0.raw) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .underflow) := by
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap1_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_neg hsub0]

theorem swap1for0_reverts_on_acc (dx : Amount asset1) (minOut : Amount asset0)
    (hpos : 0 < dx) (hr0 : 0 < w.self.reserve0.raw) (hr1 : 0 < w.self.reserve1.raw)
    (hfee : dx.raw * 9970 < wordBound)
    (hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound)
    (houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound)
    (hprotoM : swapFee dx.raw * coeffOf w.self < wordBound)
    (hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw)
    (hmin : minOut.raw ≤ swap1Out w.self dx.raw)
    (houtP : 0 < swap1Out w.self dx.raw)
    (htaken : protoOf w.self dx.raw ≤ dx.raw)
    (hadd1 : w.self.reserve1.raw + (dx.raw - protoOf w.self dx.raw) < wordBound)
    (hsub0 : swap1Out w.self dx.raw ≤ w.self.reserve0.raw)
    (hacc : ¬ w.self.protocolFees1.raw + protoOf w.self dx.raw < wordBound) :
    Tx.run (swap1for0 dx minOut) ctx w = .error (.arith .overflow) := by
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap1_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_pos hsub0, run_store_bind, run_load_bind]
  simp only [run_hAdd_bind]
  rw [if_neg hacc]

theorem swap1for0_ok_of_run {dx : Amount asset1} {minOut : Amount asset0}
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    Swap1Ok w dx minOut := by
  have hpos : 0 < dx := by
    by_contra h
    rw [swap1for0, run_req_false h] at hrun
    cases hrun
  have hr0 : 0 < w.self.reserve0.raw := by
    by_contra h
    have hz : ¬ 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using h
    rw [swap1for0, run_req_true hpos, run_load_bind, run_load_bind,
      run_req_false hz] at hrun
    cases hrun
  have hr1 : 0 < w.self.reserve1.raw := by
    by_contra h
    have hz : ¬ 0 < w.self.reserve1 := by simpa [Amount.lt_iff] using h
    have hr0A : 0 < w.self.reserve0 := by simpa [Amount.lt_iff] using hr0
    rw [swap1for0, run_req_true hpos, run_load_bind, run_load_bind,
      run_req_true hr0A, run_req_false hz] at hrun
    cases hrun
  have hfee : dx.raw * 9970 < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_fee_mul dx minOut hpos hr0 hr1 h)
  have hden : w.self.reserve1.raw + dxFeeLess dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (swap1for0_reverts_on_den dx minOut hpos hr0 hr1 hfee h)
  have houtM : w.self.reserve0.raw * dxFeeLess dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_out_mul dx minOut hpos hr0 hr1 hfee hden h)
  have hprotoM : swapFee dx.raw * coeffOf w.self < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_proto_mul dx minOut hpos hr0 hr1 hfee hden houtM h)
  have hlp : swapOutProto dx.raw (coeffBps w.self) ≤ swapFee dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_lp dx minOut hpos hr0 hr1 hfee hden houtM hprotoM h)
  have hmin : minOut.raw ≤ swap1Out w.self dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_min dx minOut hpos hr0 hr1 hfee hden houtM hprotoM hlp h)
  have houtP : 0 < swap1Out w.self dx.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_zero_out dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin h)
  have htaken : protoOf w.self dx.raw ≤ dx.raw := by
    have hfee' : protoOf w.self dx.raw ≤ swapFee dx.raw := by
      simpa [swapOutProto_coeff] using hlp
    exact Nat.le_trans hfee' (Nat.sub_le _ _)
  have hadd1 : w.self.reserve1.raw + (dx.raw - protoOf w.self dx.raw) < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_add1 dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken h)
  have hsub0 : swap1Out w.self dx.raw ≤ w.self.reserve0.raw := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_sub0 dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken hadd1 h)
  have hacc : w.self.protocolFees1.raw + protoOf w.self dx.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (swap1for0_reverts_on_acc dx minOut hpos hr0 hr1 hfee hden houtM
        hprotoM hlp hmin houtP htaken hadd1 hsub0 h)
  exact ⟨hpos, hr0, hr1, hfee, hden, houtM, hprotoM, hlp, hmin, houtP, htaken,
    hadd1, hsub0, hacc⟩

theorem swap1for0_to_tail (dx : Amount asset1) (minOut : Amount asset0)
    (h : Swap1Ok w dx minOut) :
    let out := Amount.ofWord (swap1Out w.self dx.raw)
    let proto := protoOf w.self dx.raw
    Tx.run (swap1for0 dx minOut) ctx w =
      Tx.run (
        safeTransferFrom (E := Event) w.self.token1 ctx.sender ctx.self dx
          Error.TransferFailed >>= fun _ =>
        safeTransfer (E := Event) w.self.token0 ctx.sender out
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.Swap1for0 ctx.sender dx out) >>= fun _ =>
        (pure out : Tx Storage ExtState Event Error (Amount asset0)))
        ctx { w with self := swap1Post w.self dx.raw proto (swap1Out w.self dx.raw) } := by
  rcases h with ⟨hpos, hr0, hr1, hfee, hden, houtM, hprotoM, hlp, hmin, houtP,
    htaken, hadd1, hsub0, hacc⟩
  have hQ : SwapOutOk w.self.reserve1.raw w.self.reserve0.raw dx.raw (coeffBps w.self) :=
    ⟨hfee, hden, swap1_denNe (dx := dx) hr1, houtM, (protoMul_coeff (dx := dx.raw)).mpr hprotoM, hlp⟩
  rw [swap1_after_req dx minOut hpos hr0 hr1 hQ hmin houtP]
  simp only [run_hSub_bind]
  rw [if_pos htaken]
  simp only [run_hAdd_bind]
  rw [if_pos hadd1, run_store_bind]
  simp only [run_hSub_bind]
  rw [if_pos hsub0, run_store_bind, run_load_bind]
  simp only [run_hAdd_bind]
  rw [if_pos hacc, run_store_bind, run_sender_bind, run_self_bind]
  refine (run_read_token1_then_token0 (fun t1 t0 =>
    safeTransferFrom (E := Event) t1 ctx.sender ctx.self dx
      Error.TransferFailed >>= fun _ =>
    safeTransfer (E := Event) t0 ctx.sender
      (Amount.ofWord (swap1Out w.self dx.raw)) Error.TransferFailed >>=
      fun _ =>
    Tx.emit (.Swap1for0 ctx.sender dx
      (Amount.ofWord (swap1Out w.self dx.raw))) >>= fun _ =>
    (pure (Amount.ofWord (swap1Out w.self dx.raw)) :
      Tx Storage ExtState Event Error (Amount asset0)))).trans ?_
  simp only [swap1Post, Amount.raw_add, Amount.raw_sub, Amount.raw_ofWord,
    Amount.ofWord_add_right, Amount.ofWord_sub_left, Amount.ofWord_raw,
    Amount.mk_raw]
  rfl

theorem swap1for0_post (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Swap1Ok w dx minOut)
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    out = Amount.ofWord (swap1Out w.self dx.raw) ∧
      w'.self = swap1Post w.self dx.raw (protoOf w.self dx.raw)
        (swap1Out w.self dx.raw) ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Swap1for0 ctx.sender dx
        (Amount.ofWord (swap1Out w.self dx.raw))] := by
  have heq := swap1for0_to_tail (ctx := ctx) dx minOut h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := swap1Post w.self dx.raw (protoOf w.self dx.raw)
        (swap1Out w.self dx.raw) }) hrun with
    ⟨w1, _, hs1, ho1, hl1, hrun⟩
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, _, hs2, ho2, hl2, hrun⟩
  have ⟨hn, hs3, ho3, hl3, _⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨hn, hs3.trans (hs2.trans hs1), ho3.trans (ho2.trans ho1),
    by simp [hl1, hl2, hl3]⟩

theorem swap1for0_call (dx : Amount asset1) (minOut : Amount asset0)
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Swap1Ok w dx minOut)
    (hrun : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    ∃ w1 w2,
      Tx.run (tfCall w.self.token1 ctx.sender ctx.self dx) ctx w =
        .ok (true, w1) ∧
      Tx.run (trCall w.self.token0 ctx.sender
          (Amount.ofWord (swap1Out w.self dx.raw))) ctx
          { w with ext := w1.ext } = .ok (true, w2) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w2.self = w.self ∧ w2.oracle = w.oracle ∧
      w'.ext = w2.ext ∧ w'.oracle = w.oracle ∧
      w'.self = swap1Post w.self dx.raw (protoOf w.self dx.raw)
        (swap1Out w.self dx.raw) := by
  have ⟨_, hσ, hor, _⟩ := swap1for0_post dx minOut h hrun
  have heq := swap1for0_to_tail (ctx := ctx) dx minOut h
  rw [heq] at hrun
  rcases ok_of_safeTF_bind (w₀ := { w with
      self := swap1Post w.self dx.raw (protoOf w.self dx.raw)
        (swap1Out w.self dx.raw) }) hrun with
    ⟨w1, hcall0, hs1, ho1, hl1, hrun⟩
  have htf0 := transferFrom_call_ignore_self
    (σ := swap1Post w.self dx.raw (protoOf w.self dx.raw) (swap1Out w.self dx.raw))
    hcall0
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, hcall1, hs2, ho2, hl2, hrun⟩
  have : w1 = { w with
      self := swap1Post w.self dx.raw (protoOf w.self dx.raw)
        (swap1Out w.self dx.raw)
      ext := w1.ext } :=
    eq_self_ext hs1 ho1 hl1
  have htr1 := transfer_call_ignore_self
    (w := { w with ext := w1.ext })
    (σ := swap1Post w.self dx.raw (protoOf w.self dx.raw) (swap1Out w.self dx.raw))
    (this ▸ hcall1)
  have ⟨_, _, _, _, hext⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨{ w with ext := w1.ext }, { w with ext := w2.ext },
    htf0.1, htr1.1, rfl, rfl, rfl, rfl, rfl, hext, hor, hσ⟩

/-! ### collectProtocolFees -/

theorem collectProtocolFees_reverts_on_no_feeTo (h : w.self.feeTo = 0) :
    Tx.run collectProtocolFees ctx w = .error (.user .NoFeeTo) := by
  have : ¬ w.self.feeTo ≠ 0 := by simp [h]
  rw [collectProtocolFees, run_sender_bind, run_load_bind, run_req_false this]

theorem collectProtocolFees_reverts_on_not_feeTo
    (hft : w.self.feeTo ≠ 0) (h : ctx.sender ≠ w.self.feeTo) :
    Tx.run collectProtocolFees ctx w = .error (.user .NotOwner) := by
  rw [collectProtocolFees, run_sender_bind, run_load_bind, run_req_true hft,
    run_req_false h]

structure CollectOk (ctx : Ctx) (w : World Storage ExtState Event) : Prop where
  feeTo : w.self.feeTo ≠ 0
  sender : ctx.sender = w.self.feeTo

theorem collectProtocolFees_ok_of_run
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (hrun : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    CollectOk ctx w := by
  have hft : w.self.feeTo ≠ 0 := by
    by_contra h
    exact Tx.run_ok_error hrun (collectProtocolFees_reverts_on_no_feeTo h)
  have hwho : ctx.sender = w.self.feeTo := by
    by_contra h
    exact Tx.run_ok_error hrun (collectProtocolFees_reverts_on_not_feeTo hft h)
  exact ⟨hft, hwho⟩

theorem collectProtocolFees_to_tail (h : CollectOk ctx w) :
    Tx.run collectProtocolFees ctx w =
      Tx.run (
        safeTransfer (E := Event) w.self.token0 ctx.sender w.self.protocolFees0
          Error.TransferFailed >>= fun _ =>
        safeTransfer (E := Event) w.self.token1 ctx.sender w.self.protocolFees1
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.ProtocolFeesCollected ctx.sender w.self.protocolFees0
          w.self.protocolFees1) >>= fun _ =>
        (pure (w.self.protocolFees0, w.self.protocolFees1) :
          Tx Storage ExtState Event Error (Amount asset0 × Amount asset1)))
        ctx { w with self := collectPost w.self } := by
  rcases h with ⟨hft, hwho⟩
  rw [collectProtocolFees, run_sender_bind, run_load_bind, run_req_true hft,
    run_req_true hwho, run_load_bind, run_load_bind, run_store_bind, run_store_bind]
  refine (run_read_token0_then_token1 (fun t0 t1 =>
    safeTransfer (E := Event) t0 ctx.sender w.self.protocolFees0
      Error.TransferFailed >>= fun _ =>
    safeTransfer (E := Event) t1 ctx.sender w.self.protocolFees1
      Error.TransferFailed >>= fun _ =>
    Tx.emit (.ProtocolFeesCollected ctx.sender w.self.protocolFees0
      w.self.protocolFees1) >>= fun _ =>
    (pure (w.self.protocolFees0, w.self.protocolFees1) :
      Tx Storage ExtState Event Error (Amount asset0 × Amount asset1)))).trans ?_
  simp only [collectPost, Amount.ofWord_zero]
  rfl

theorem collectProtocolFees_post
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : CollectOk ctx w)
    (hrun : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    p = (w.self.protocolFees0, w.self.protocolFees1) ∧
      w'.self = collectPost w.self ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.ProtocolFeesCollected ctx.sender
        w.self.protocolFees0 w.self.protocolFees1] := by
  have heq := collectProtocolFees_to_tail h
  rw [heq] at hrun
  rcases ok_of_safeTR_bind (w₀ := { w with self := collectPost w.self }) hrun with
    ⟨w1, _, hs1, ho1, hl1, hrun⟩
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, _, hs2, ho2, hl2, hrun⟩
  have ⟨hn, hs3, ho3, hl3, _⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨hn, hs3.trans (hs2.trans hs1), ho3.trans (ho2.trans ho1),
    by simp [hl1, hl2, hl3]⟩

theorem collectProtocolFees_call
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : CollectOk ctx w)
    (hrun : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    ∃ w1 w2,
      Tx.run (trCall w.self.token0 ctx.sender w.self.protocolFees0) ctx w =
        .ok (true, w1) ∧
      Tx.run (trCall w.self.token1 ctx.sender w.self.protocolFees1) ctx
          { w with ext := w1.ext } = .ok (true, w2) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w2.self = w.self ∧ w2.oracle = w.oracle ∧
      w'.ext = w2.ext ∧ w'.oracle = w.oracle ∧
      w'.self = collectPost w.self := by
  have ⟨_, hσ, hor, _⟩ := collectProtocolFees_post h hrun
  have heq := collectProtocolFees_to_tail h
  rw [heq] at hrun
  rcases ok_of_safeTR_bind (w₀ := { w with self := collectPost w.self }) hrun with
    ⟨w1, hcall0, hs1, ho1, hl1, hrun⟩
  have htr0 := transfer_call_ignore_self (σ := collectPost w.self) hcall0
  rcases ok_of_safeTR_bind (w₀ := w1) hrun with ⟨w2, hcall1, hs2, ho2, hl2, hrun⟩
  have : w1 = { w with self := collectPost w.self, ext := w1.ext } :=
    eq_self_ext hs1 ho1 hl1
  have htr1 := transfer_call_ignore_self
    (w := { w with ext := w1.ext }) (σ := collectPost w.self) (this ▸ hcall1)
  have ⟨_, _, _, _, hext⟩ := ok_of_emit_pure (w₀ := w2) hrun
  exact ⟨{ w with ext := w1.ext }, { w with ext := w2.ext },
    htr0.1, htr1.1, rfl, rfl, rfl, rfl, rfl, hext, hor, hσ⟩

namespace Proof

theorem swap0for1_k {dx : Amount asset0} {minOut : Amount asset1}
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw := by
  have hok := swap0for1_ok_of_run h
  have ⟨_, hσ, _, _⟩ := swap0for1_post dx minOut hok h
  have hpsN : w.self.protocolShareBps.raw ≤ BPS.raw := by
    simpa [Amount.le_iff] using hps
  have hk := swapQuote_k w.self.reserve0.raw w.self.reserve1.raw dx.raw
    w.self.feeTo w.self.protocolShareBps.raw hok.r0 hpsN
  simp [hσ, swap0Post, Amount.raw_add, Amount.raw_sub, Amount.raw_ofWord,
    protoOf, protoTake, swapQuote, amountOut, amountOutF, swap0Out]
  change (_ : Nat) ≤ _
  exact hk

theorem swap1for0_k {dx : Amount asset1} {minOut : Amount asset0}
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w'))
    (hps : w.self.protocolShareBps ≤ BPS) :
    w'.self.reserve0.raw * w'.self.reserve1.raw ≥
      w.self.reserve0.raw * w.self.reserve1.raw := by
  have hok := swap1for0_ok_of_run h
  have ⟨_, hσ, _, _⟩ := swap1for0_post dx minOut hok h
  have hpsN : w.self.protocolShareBps.raw ≤ BPS.raw := by
    simpa [Amount.le_iff] using hps
  have hk := swapQuote_k w.self.reserve1.raw w.self.reserve0.raw dx.raw
    w.self.feeTo w.self.protocolShareBps.raw hok.r1 hpsN
  simp [hσ, swap1Post, Amount.raw_add, Amount.raw_sub, Amount.raw_ofWord]
  change (_ : Nat) ≤ _
  refine (Nat.mul_comm _ _).trans_le (le_trans hk ?_)
  simp [protoOf, protoTake, swapQuote, amountOut, amountOutF, swap1Out]
  exact (Nat.mul_comm _ _).le

theorem swap0_protocol_fee {dx : Amount asset0} {minOut : Amount asset1}
    {out : Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees0 =
      w.self.protocolFees0 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := swap0for1_ok_of_run h
  have ⟨_, hσ, _, _⟩ := swap0for1_post dx minOut hok h
  simp [hσ, swap0Post]

theorem swap1_protocol_fee {dx : Amount asset1} {minOut : Amount asset0}
    {out : Amount asset0} {w' : World Storage ExtState Event}
    (h : Tx.run (swap1for0 dx minOut) ctx w = .ok (out, w')) :
    w'.self.protocolFees1 =
      w.self.protocolFees1 + Amount.ofWord (protoOf w.self dx.raw) ∧
      w'.self.protocolFees0 = w.self.protocolFees0 := by
  have hok := swap1for0_ok_of_run h
  have ⟨_, hσ, _, _⟩ := swap1for0_post dx minOut hok h
  simp [hσ, swap1Post]

theorem collect_only_feeTo {p : Amount asset0 × Amount asset1}
    {w' : World Storage ExtState Event}
    (h : Tx.run collectProtocolFees ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = 0 ∧ w'.self.protocolFees1 = 0 ∧
      w'.self.reserve0 = w.self.reserve0 ∧ w'.self.reserve1 = w.self.reserve1 := by
  have hok := collectProtocolFees_ok_of_run h
  have ⟨_, hσ, _, _⟩ := collectProtocolFees_post hok h
  exact ⟨by simp [hσ, collectPost], by simp [hσ, collectPost],
    by simp [hσ, collectPost], by simp [hσ, collectPost]⟩

theorem addLiquidity_buckets {a0 : Amount asset0} {a1 : Amount asset1}
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := addLiquidity_ok_of_run h
  have ⟨_, hσ, _, _⟩ := addLiquidity_post a0 a1 hok h
  simp [hσ, addLiquidityPost]

theorem removeLiquidity_buckets {s : Amount lpShare}
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  have hok := removeLiquidity_ok_of_run h
  have ⟨_, hσ, _, _⟩ := removeLiquidity_post s hok h
  simp [hσ, removeLiquidityPost]

theorem setProtocolShare_buckets {bps : Bps} {w' : World Storage ExtState Event}
    (h : Tx.run (setProtocolShare bps) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  obtain ⟨_, _, rfl⟩ := setProtocolShare_ok_of_run h
  simp

theorem setFeeTo_buckets {recipient : Address} {w' : World Storage ExtState Event}
    (h : Tx.run (setFeeTo recipient) ctx w = .ok ((), w')) :
    w'.self.protocolFees0 = w.self.protocolFees0 ∧
      w'.self.protocolFees1 = w.self.protocolFees1 := by
  obtain ⟨_, rfl⟩ := setFeeTo_ok_of_run h
  simp

theorem removeLiquidity_pro_rata {s : Amount lpShare}
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    w'.self.reserve0 = w.self.reserve0 - p.1 ∧
      w'.self.reserve1 = w.self.reserve1 - p.2 := by
  have hok := removeLiquidity_ok_of_run h
  have ⟨hp, hσ, _, _⟩ := removeLiquidity_post s hok h
  subst hp
  simp [hσ, removeLiquidityPost, redeemed]

theorem removeLiquidity_paid {s : Amount lpShare}
    {p : Amount asset0 × Amount asset1} {w' : World Storage ExtState Event}
    (h : Tx.run (removeLiquidity s) ctx w = .ok (p, w')) :
    p.1.raw = w.self.reserve0.raw * s.raw / w.self.totalShares.raw ∧
      p.2.raw = w.self.reserve1.raw * s.raw / w.self.totalShares.raw := by
  have hok := removeLiquidity_ok_of_run h
  have ⟨hp, _, _, _⟩ := removeLiquidity_post s hok h
  simp [hp, redeemed, Amount.raw_ofWord]

theorem addLiquidity_pro_rata {a0 : Amount asset0} {a1 : Amount asset1}
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender + n ∧
      w'.self.totalShares = w.self.totalShares + n := by
  have hok := addLiquidity_ok_of_run h
  have ⟨hn, hσ, _, _⟩ := addLiquidity_post a0 a1 hok h
  subst hn
  simp [hσ, addLiquidityPost, Function.update, Amount.raw_add, Amount.raw_ofWord,
    Nat.add_comm]

theorem addLiquidity_minted {a0 : Amount asset0} {a1 : Amount asset1}
    {n : Amount lpShare} {w' : World Storage ExtState Event}
    (h : Tx.run (addLiquidity a0 a1) ctx w = .ok (n, w')) :
    n = Amount.ofWord (mintedShares w.self a0.raw a1.raw) := by
  have hok := addLiquidity_ok_of_run h
  exact (addLiquidity_post a0 a1 hok h).1

end Proof

end Cpamm
