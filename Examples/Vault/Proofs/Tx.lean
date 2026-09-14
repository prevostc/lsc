import Mathlib.Tactic.SplitIfs
import Examples.Vault.Spec
import Stdlib.SafeERC20
import Lsc.Lang.TxTheorems
import Lsc.Lang.AmountTheorems

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
Vault `Tx.run` lemmas. External CALLs are opaque; success lemmas recover
storage, logs, and the oracle, and use `IERC20.Spec` for holdings.
-/

open Lsc Lsc.Stdlib Vault

attribute [local simp] Amount.eq_iff Amount.ne_iff Amount.lt_iff Amount.le_iff

namespace Vault

variable {ctx : Ctx} {w : World Storage ExtState Event}

abbrev tfCall (r : IERC20.Ref vaultAsset) (src dst : Address)
    (amt : Amount vaultAsset) : Tx Storage ExtState Event Error Bool :=
  r.transferFrom src dst amt

abbrev trCall (r : IERC20.Ref vaultAsset) (dst : Address)
    (amt : Amount vaultAsset) : Tx Storage ExtState Event Error Bool :=
  r.transfer dst amt

/-- Shares that `deposit` mints from `σ` (the floor; 1:1 when empty). -/
def mintedShares (σ : Storage) (assets : Amount vaultAsset) : Nat :=
  if σ.totalShares.raw = 0 then assets.raw
  else σ.totalShares.raw * assets.raw / σ.totalAssets.raw

/-- Storage after a successful `deposit` by `who`. -/
def depositPost (σ : Storage) (who : Address) (assets : Amount vaultAsset) : Storage :=
  let minted : Amount vShare := Amount.ofWord (mintedShares σ assets)
  { σ with
    totalAssets := σ.totalAssets + assets
    totalShares := σ.totalShares + minted
    shares := Function.update σ.shares who (σ.shares who + minted) }

/-- Assets `withdraw` pays. -/
def redeemedAssets (σ : Storage) (sharesIn : Amount vShare) : Nat :=
  σ.totalAssets.raw * sharesIn.raw / σ.totalShares.raw

/-- Storage after a successful `withdraw` by `who`. -/
def withdrawPost (σ : Storage) (who : Address) (sharesIn : Amount vShare)
    (assetsOut : Nat) : Storage :=
  { σ with
    totalAssets := σ.totalAssets - Amount.ofWord assetsOut
    totalShares := σ.totalShares - sharesIn
    shares := Function.update σ.shares who (σ.shares who - sharesIn) }

private theorem depositPost_of_stores (σ : Storage) (who : Address)
    (assets : Amount vaultAsset) :
    { σ with
      totalAssets := Amount.ofWord (σ.totalAssets.raw + assets.raw)
      totalShares := Amount.ofWord (σ.totalShares.raw + mintedShares σ assets)
      shares := fun k => Amount.ofWord
        (Function.update (fun i => (σ.shares i).raw) who
          ((σ.shares who).raw + mintedShares σ assets) k) } =
      depositPost σ who assets := by
  simp [depositPost, Amount.update_raw, Amount.ofWord_add_left, Amount.ofWord_raw]

private theorem withdrawPost_of_stores (σ : Storage) (who : Address)
    (sharesIn : Amount vShare) (assetsOut : Nat) :
    { σ with
      totalAssets := Amount.ofWord (σ.totalAssets.raw - assetsOut)
      totalShares := Amount.ofWord (σ.totalShares.raw - sharesIn.raw)
      shares := fun i => Amount.ofWord
        (Function.update (fun i => (σ.shares i).raw) who
          ((σ.shares who).raw - sharesIn.raw) i) } =
      withdrawPost σ who sharesIn assetsOut := by
  simp [withdrawPost, Amount.update_raw, Amount.ofWord_sub]

private theorem run_store_ta {α : Type} (v : Nat)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.store (X := ExtState) (E := Event) (ε := Error)
        (fun σ m => { σ with totalAssets := Amount.ofWord m }) v >>= k) ctx w =
      Tx.run (k ()) ctx
        { w with self := { w.self with totalAssets := Amount.ofWord v } } := by
  rw [Tx.run_bind, Tx.run_store]

private theorem run_store_ts {α : Type} (v : Nat)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.store (X := ExtState) (E := Event) (ε := Error)
        (fun σ m => { σ with totalShares := Amount.ofWord m }) v >>= k) ctx w =
      Tx.run (k ()) ctx
        { w with self := { w.self with totalShares := Amount.ofWord v } } := by
  rw [Tx.run_bind, Tx.run_store]

private theorem run_storeMap_shares {α : Type} (who : Address) (v : Nat)
    (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.storeMap (X := ExtState) (E := Event) (ε := Error)
        (fun σ k => (σ.shares k).raw)
        (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
        who v >>= k) ctx w =
      Tx.run (k ()) ctx
        { w with self := { w.self with
            shares := fun k => Amount.ofWord
              (Function.update (fun i => (w.self.shares i).raw) who v k) } } := by
  rw [Tx.run_bind, Tx.run_storeMap]

theorem holdings_view (self : Address) :
    holdings self w = (viewBal w.self.asset self w.oracle w.ext).raw := by
  simp [holdings, viewBal, IERC20.Ref.impl, IERC20.Impl.ofRef, balSel]

theorem holdings_congr (self : Address) {w w' : World Storage ExtState Event}
    (ha : w'.self.asset.addr = w.self.asset.addr)
    (ho : w'.oracle = w.oracle) (hx : w'.ext = w.ext) :
    holdings self w' = holdings self w := by
  simp [holdings, IERC20.Ref.impl, IERC20.Impl.ofRef, ha, ho, hx]

theorem transferFrom_frame {r : IERC20.Ref vaultAsset}
    {src dst : Address} {amt : Amount vaultAsset} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (tfCall r src dst amt) ctx w = .ok (b, w')) :
    w'.self = w.self ∧ w'.oracle = w.oracle ∧ w'.log = w.log := by
  refine ⟨Tx.call_self (α := Bool) r.addr
      (Interface.selector (I := IERC20 vaultAsset) "transferFrom")
      [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] h,
    Tx.call_oracle (α := Bool) r.addr
      (Interface.selector (I := IERC20 vaultAsset) "transferFrom")
      [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] h, ?_⟩
  simp [IERC20.Ref.transferFrom, Tx.run_call] at h
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem transfer_frame {r : IERC20.Ref vaultAsset}
    {dst : Address} {amt : Amount vaultAsset} {b : Bool}
    {w' : World Storage ExtState Event}
    (h : Tx.run (trCall r dst amt) ctx w = .ok (b, w')) :
    w'.self = w.self ∧ w'.oracle = w.oracle ∧ w'.log = w.log := by
  refine ⟨Tx.call_self (α := Bool) r.addr
      (Interface.selector (I := IERC20 vaultAsset) "transfer")
      [AbiType.encode dst, AbiType.encode amt] h,
    Tx.call_oracle (α := Bool) r.addr
      (Interface.selector (I := IERC20 vaultAsset) "transfer")
      [AbiType.encode dst, AbiType.encode amt] h, ?_⟩
  simp [IERC20.Ref.transfer, Tx.run_call] at h
  split at h <;> try cases h
  split at h <;> cases h
  rfl

theorem impl_transferFrom (r : IERC20.Ref vaultAsset)
    (src dst : Address) (amt : Amount vaultAsset) :
    (r.impl w : IERC20.Impl vaultAsset (World Storage ExtState Event) Error).transferFrom
        src dst amt ctx w =
      Tx.run (tfCall r src dst amt) ctx w :=
  rfl

theorem impl_transfer (r : IERC20.Ref vaultAsset)
    (dst : Address) (amt : Amount vaultAsset) :
    (r.impl w : IERC20.Impl vaultAsset (World Storage ExtState Event) Error).transfer
        dst amt ctx w =
      Tx.run (trCall r dst amt) ctx w :=
  rfl

theorem transfer_run_ctx_irrel {r : IERC20.Ref vaultAsset}
    {dst : Address} {amt : Amount vaultAsset} {ctx' : Ctx}
    {w₀ : World Storage ExtState Event} :
    Tx.run (trCall r dst amt) ctx w₀ =
      Tx.run (trCall r dst amt) ctx' w₀ := by
  simp [IERC20.Ref.transfer, Tx.run_call]

/-- A CALL ignores `self`; success on an updated storage world transports to
the original world with only `ext` changed. -/
theorem transferFrom_call_ignore_self {r : IERC20.Ref vaultAsset}
    {src dst : Address} {amt : Amount vaultAsset} {σ : Storage} {b : Bool}
    {w1 : World Storage ExtState Event}
    (h : Tx.run (tfCall r src dst amt) ctx { w with self := σ } = .ok (b, w1)) :
    Tx.run (tfCall r src dst amt) ctx w = .ok (b, { w with ext := w1.ext }) ∧
      w1.self = σ ∧ w1.oracle = w.oracle ∧ w1.log = w.log := by
  have hframe := transferFrom_frame (w := { w with self := σ }) h
  refine ⟨?_, hframe.1, hframe.2.1, hframe.2.2⟩
  simp [tfCall, IERC20.Ref.transferFrom, Tx.run_call] at h ⊢
  -- CALL ignores `self`; only `ext` in the success world can change.
  split at h <;> try cases h
  split at h <;> try cases h
  simp_all

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
    {k : Amount vShare → Tx Storage ExtState Event Error α} :
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

private theorem run_pure {α : Type} {a : α} :
    Tx.run (pure a : Tx Storage ExtState Event Error α) ctx w = .ok (a, w) :=
  Tx.run_pure a ctx w

private theorem run_emit_bind {α : Type} {ev : Event}
    {k : Unit → Tx Storage ExtState Event Error α} :
    Tx.run (Tx.emit (S := Storage) (X := ExtState) ev >>= k) ctx w =
      Tx.run (k ()) ctx { w with log := w.log ++ [ev] } := by
  simp [Tx.run_bind, Tx.run_emit]

private theorem run_safeTF_error {src dst : Address} {amt : Amount vaultAsset}
    {r : IERC20.Ref vaultAsset} {e : Err Error}
    (h : Tx.run (tfCall r src dst amt) ctx w = .error e) :
    Tx.run (safeTransferFrom (E := Event) r src dst amt Error.TransferFailed) ctx w =
      .error e := by
  simp [run_safeTransferFrom, h]

private theorem run_safeTR_error {dst : Address} {amt : Amount vaultAsset}
    {r : IERC20.Ref vaultAsset} {e : Err Error}
    (h : Tx.run (trCall r dst amt) ctx w = .error e) :
    Tx.run (safeTransfer (E := Event) r dst amt Error.TransferFailed) ctx w =
      .error e := by
  simp [run_safeTransfer, h]

/-- Bind after `safeTransferFrom` is a match on the Bool CALL, not a nested
Unit match. Quantified over `w₀` so it rewrites on post-storage worlds. -/
private theorem run_safeTF_bind {α : Type} {w₀ : World Storage ExtState Event}
    (r : IERC20.Ref vaultAsset) (src dst : Address) (amt : Amount vaultAsset)
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
private theorem run_safeTR_bind {α : Type} {w₀ : World Storage ExtState Event}
    (r : IERC20.Ref vaultAsset) (dst : Address) (amt : Amount vaultAsset)
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
    Tx.run (Tx.emit (S := Storage) (X := ExtState) ev >>= fun _ =>
        (pure a : Tx Storage ExtState Event Error α)) ctx w₀ =
      .ok (a, { w₀ with log := w₀.log ++ [ev] }) := by
  simp [Tx.run_bind, Tx.run_emit, Tx.run_pure]

/-- `0 < a / b` for nats. Used when `simp` unfolds `0 < minted`. -/
theorem pos_div_iff {a b : Nat} : 0 < a / b ↔ 0 < b ∧ b ≤ a := by
  rw [Nat.pos_iff_ne_zero, ne_eq, Nat.div_eq_zero_iff]
  omega

private theorem not_pos_div {a b : Nat} (hb : 0 < b) (h : ¬ 0 < a / b) : ¬ b ≤ a := by
  intro hba
  exact h (pos_div_iff.mpr ⟨hb, hba⟩)

private theorem empty_mul {assets : Amount vaultAsset} (h : assets.raw < wordBound) :
    (1 : Amount vShare).raw * assets.raw < wordBound := by
  rw [Amount.raw_ofNat, Nat.one_mul]
  exact h

private theorem empty_mul_not {assets : Amount vaultAsset}
    (h : ¬ assets.raw < wordBound) :
    ¬ (1 : Amount vShare).raw * assets.raw < wordBound := by
  rw [Amount.raw_ofNat, Nat.one_mul]
  exact h

private theorem empty_mint_pos {assets : Amount vaultAsset} (h : 0 < assets) :
    0 < (1 : Amount vShare).raw ∧
      (1 : Amount vShare).raw ≤ (1 : Amount vShare).raw * assets.raw := by
  have h0 : 0 < assets.raw := by simpa [Amount.lt_iff] using h
  rw [Amount.raw_ofNat, Nat.one_mul]
  exact ⟨Nat.succ_pos 0, Nat.succ_le_of_lt h0⟩

private theorem not_oneA_zero : ¬ (1 : Amount vaultAsset).raw = 0 := by simp

/-- `oneS mulDiv↓ assets / oneA` and `ts mulDiv↓ assets / ta`. Closed; no CALL. -/
private theorem run_mulDivDown_ts {α : Type}
    (num : Amount vShare) (x y : Amount vaultAsset)
    (k : Amount vShare → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        Tx.run (k ⟨num.raw * x.raw / y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_def, Amount.run_mulDivDown]
  split_ifs <;> rfl

/-- `ta mulDiv↓ sharesIn / ts`. -/
private theorem run_mulDivDown_ta {α : Type}
    (num : Amount vaultAsset) (x y : Amount vShare)
    (k : Amount vaultAsset → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) num x y >>= k) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        Tx.run (k ⟨num.raw * x.raw / y.raw⟩) ctx w
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Amount.hMulDivDown_def, Amount.run_mulDivDown]
  split_ifs <;> rfl

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

private theorem run_read_asset {α : Type}
    (k : IERC20.Ref vaultAsset → Tx Storage ExtState Event Error α) :
    Tx.run (((fun n => ({ addr := n } : IERC20.Ref vaultAsset)) <$>
        Tx.load (X := ExtState) (E := Event) (ε := Error)
          (fun σ => σ.asset.addr)) >>= k) ctx w =
      Tx.run (k w.self.asset) ctx w := by
  simp only [Tx.run_bind, Tx.run_map, Tx.run_load]

private theorem run_store_bind {α β : Type} (upd : Storage → α → Storage) (v : α)
    (k : Unit → Tx Storage ExtState Event Error β) :
    Tx.run (Tx.store (X := ExtState) (E := Event) (ε := Error) upd v >>= k) ctx w =
      Tx.run (k ()) ctx { w with self := upd w.self v } := by
  rw [Tx.run_bind, Tx.run_store]

private theorem run_storeMap_bind {α : Type} {K V : Type} [DecidableEq K]
    (proj : Storage → K → V) (upd : Storage → (K → V) → Storage)
    (key : K) (v : V) (k : Unit → Tx Storage ExtState Event Error α) :
    Tx.run (Tx.storeMap (X := ExtState) (E := Event) (ε := Error) proj upd key v >>=
        k) ctx w =
      Tx.run (k ()) ctx
        { w with self := upd w.self (Function.update (proj w.self) key v) } := by
  rw [Tx.run_bind, Tx.run_storeMap]

/-- 1:1 `mulDiv↓` when the product fits. -/
private theorem run_oneS_mulDiv {α : Type} (assets : Amount vaultAsset)
    (k : Amount vShare → Tx Storage ExtState Event Error α)
    (hfit : assets.raw < wordBound) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) (1 : Amount vShare) assets (1 : Amount vaultAsset) >>= k)
        ctx w =
      Tx.run (k ⟨assets.raw⟩) ctx w := by
  simp only [run_mulDivDown_ts]
  rw [if_neg not_oneA_zero, if_pos (empty_mul hfit)]
  have hval :
      (⟨(1 : Amount vShare).raw * assets.raw / (1 : Amount vaultAsset).raw⟩ :
        Amount vShare) = ⟨assets.raw⟩ := by
    apply Amount.ext
    rw [Amount.raw_ofNat (a := vShare) 1, Amount.raw_ofNat (a := vaultAsset) 1,
      Nat.one_mul, Nat.div_one]
  rw [hval]

private theorem run_oneS_mulDiv_overflow {α : Type} (assets : Amount vaultAsset)
    (k : Amount vShare → Tx Storage ExtState Event Error α)
    (hfit : ¬ assets.raw < wordBound) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) (1 : Amount vShare) assets (1 : Amount vaultAsset) >>= k)
        ctx w =
      .error (.arith .overflow) := by
  simp only [run_mulDivDown_ts]
  rw [if_neg not_oneA_zero, if_neg (empty_mul_not hfit)]

private theorem run_rate_mulDiv {α : Type}
    (ts : Amount vShare) (assets ta : Amount vaultAsset)
    (k : Amount vShare → Tx Storage ExtState Event Error α)
    (hta : ta.raw ≠ 0) (hmul : ts.raw * assets.raw < wordBound) :
    Tx.run (Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) ts assets ta >>= k) ctx w =
      Tx.run (k ⟨ts.raw * assets.raw / ta.raw⟩) ctx w := by
  simp only [run_mulDivDown_ts]
  rw [if_neg hta, if_pos hmul]

private theorem deposit_guards (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets) :
    Tx.run (deposit assets) ctx w =
      Tx.run (
        have oneA : Amount vaultAsset := 1
        have oneS : Amount vShare := 1
        have jp : Amount vShare → Tx Storage ExtState Event Error (Amount vShare) :=
          fun minted => do
            Tx.require (0 < minted) Error.ZeroShares
            let __do_lift ← Tx.HAddChecked.hAdd w.self.totalAssets assets
            Tx.store (fun σ m =>
              { asset := σ.asset, owner := σ.owner, paused := σ.paused,
                totalAssets := Amount.ofWord m, totalShares := σ.totalShares,
                shares := σ.shares }) __do_lift.raw
            let __do_lift ← Tx.HAddChecked.hAdd w.self.totalShares minted
            Tx.store (fun σ m =>
              { asset := σ.asset, owner := σ.owner, paused := σ.paused,
                totalAssets := σ.totalAssets, totalShares := Amount.ofWord m,
                shares := σ.shares }) __do_lift.raw
            let bal ← Tx.loadMap (fun σ k => σ.shares k) ctx.sender
            let __do_lift ← Tx.HAddChecked.hAdd bal minted
            Tx.storeMap (fun σ k => (σ.shares k).raw)
              (fun σ m =>
                { asset := σ.asset, owner := σ.owner, paused := σ.paused,
                  totalAssets := σ.totalAssets, totalShares := σ.totalShares,
                  shares := fun k => Amount.ofWord (m k) })
              ctx.sender __do_lift.raw
            let tok ← (fun n => ({ addr := n } : IERC20.Ref vaultAsset)) <$>
              Tx.load (fun σ => σ.asset.addr)
            safeTransferFrom tok ctx.sender ctx.self assets Error.TransferFailed
            Tx.emit (.Deposit ctx.sender assets minted)
            pure minted
        if w.self.totalShares = 0 then do
          let minted ← Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState)
            (E := Event) (ε := Error) oneS assets oneA
          jp minted
        else do
          let minted ← Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState)
            (E := Event) (ε := Error) w.self.totalShares assets
            w.self.totalAssets
          jp minted) ctx w := by
  rw [deposit, run_load_bind, run_req_true hp, run_req_true hpos,
    run_sender_bind, run_self_bind, run_load_bind, run_load_bind]
  rfl

/-- `deposit` after a successful mint, at the first `+?`. -/
private theorem deposit_after_mint (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound))
    (hfit : w.self.totalShares.raw = 0 → assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self assets) :
    Tx.run (deposit assets) ctx w =
      Tx.run (do
        let ta' ← Tx.HAddChecked.hAdd w.self.totalAssets assets
        Tx.store (fun σ m => { σ with totalAssets := Amount.ofWord m }) ta'.raw
        let ts' ← Tx.HAddChecked.hAdd w.self.totalShares
          (⟨mintedShares w.self assets⟩ : Amount vShare)
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        let bal ← Tx.loadMap (fun σ k => σ.shares k) ctx.sender
        let bal' ← Tx.HAddChecked.hAdd bal
          (⟨mintedShares w.self assets⟩ : Amount vShare)
        Tx.storeMap (fun σ k => (σ.shares k).raw)
          (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
          ctx.sender bal'.raw
        let tok ← (fun n => ({ addr := n } : IERC20.Ref vaultAsset)) <$>
          Tx.load (fun σ => σ.asset.addr)
        safeTransferFrom tok ctx.sender ctx.self assets Error.TransferFailed
        Tx.emit (.Deposit ctx.sender assets ⟨mintedShares w.self assets⟩)
        pure (⟨mintedShares w.self assets⟩ : Amount vShare)) ctx w := by
  have hposM : 0 < (⟨mintedShares w.self assets⟩ : Amount vShare) := by
    simpa [Amount.lt_iff] using hminted
  rw [deposit_guards assets hp hpos, Tx.run_ite]
  by_cases hts : w.self.totalShares = 0
  · have htsr : w.self.totalShares.raw = 0 := (Amount.eq_iff _ _).mp hts
    rw [if_pos hts, run_oneS_mulDiv (hfit := hfit htsr)]
    have hm : (⟨assets.raw⟩ : Amount vShare) =
        ⟨mintedShares w.self assets⟩ := by
      simp [mintedShares, htsr]
    rw [hm, run_req_true hposM]
  · have htsr : w.self.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (htsr h0).elim
    · rw [if_neg hts, run_rate_mulDiv (hta := hta) (hmul := hmul)]
      have hm :
          (⟨w.self.totalShares.raw * assets.raw / w.self.totalAssets.raw⟩ :
            Amount vShare) = ⟨mintedShares w.self assets⟩ := by
        simp [mintedShares, htsr]
      rw [hm, run_req_true hposM]

private theorem withdraw_guards (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender) :
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (do
        let assetsOut ← Tx.HMulDivDown.hMulDivDown (S := Storage) (X := ExtState)
          (E := Event) (ε := Error) w.self.totalAssets sharesIn w.self.totalShares
        Tx.require (0 < assetsOut) Error.ZeroAssets
        let bal' ← Tx.HSubChecked.hSub (w.self.shares ctx.sender) sharesIn
        Tx.storeMap (fun σ i => (σ.shares i).raw)
          (fun σ m => { σ with shares := fun i => Amount.ofWord (m i) })
          ctx.sender bal'.raw
        let ts' ← Tx.HSubChecked.hSub w.self.totalShares sharesIn
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        let ta' ← Tx.HSubChecked.hSub w.self.totalAssets assetsOut
        Tx.store (fun σ m => { σ with totalAssets := Amount.ofWord m }) ta'.raw
        let tok ← (fun n => ({ addr := n } : IERC20.Ref vaultAsset)) <$>
          Tx.load (fun σ => σ.asset.addr)
        safeTransfer tok ctx.sender assetsOut Error.TransferFailed
        Tx.emit (.Withdraw ctx.sender assetsOut sharesIn)
        pure assetsOut) ctx w := by
  rw [withdraw, run_load_bind, run_req_true hp, run_req_true hpos,
    run_sender_bind, run_loadMap_bind, run_req_true hbal, run_load_bind,
    run_load_bind]
  rfl

/-- `withdraw` after a successful redeem, at the first `-?`. -/
private theorem withdraw_after_redeem (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares.raw ≠ 0)
    (hmul : w.self.totalAssets.raw * sharesIn.raw < wordBound)
    (hassets : 0 < redeemedAssets w.self sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (do
        let bal' ← Tx.HSubChecked.hSub (w.self.shares ctx.sender) sharesIn
        Tx.storeMap (fun σ i => (σ.shares i).raw)
          (fun σ m => { σ with shares := fun i => Amount.ofWord (m i) })
          ctx.sender bal'.raw
        let ts' ← Tx.HSubChecked.hSub w.self.totalShares sharesIn
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        let ta' ← Tx.HSubChecked.hSub w.self.totalAssets
          (⟨redeemedAssets w.self sharesIn⟩ : Amount vaultAsset)
        Tx.store (fun σ m => { σ with totalAssets := Amount.ofWord m }) ta'.raw
        let tok ← (fun n => ({ addr := n } : IERC20.Ref vaultAsset)) <$>
          Tx.load (fun σ => σ.asset.addr)
        safeTransfer tok ctx.sender ⟨redeemedAssets w.self sharesIn⟩
          Error.TransferFailed
        Tx.emit (.Withdraw ctx.sender ⟨redeemedAssets w.self sharesIn⟩ sharesIn)
        pure (⟨redeemedAssets w.self sharesIn⟩ : Amount vaultAsset)) ctx w := by
  have hposA : 0 < (⟨redeemedAssets w.self sharesIn⟩ : Amount vaultAsset) := by
    simpa [Amount.lt_iff] using hassets
  rw [withdraw_guards sharesIn hp hpos hbal]
  simp only [run_mulDivDown_ta]
  rw [if_neg hden, if_pos hmul]
  have hm :
      (⟨w.self.totalAssets.raw * sharesIn.raw / w.self.totalShares.raw⟩ :
        Amount vaultAsset) = ⟨redeemedAssets w.self sharesIn⟩ := by
    simp [redeemedAssets]
  rw [hm, run_req_true hposA]

/-! ### Views / pause -/

theorem isPaused_returns_stored :
    Tx.run isPaused ctx w = .ok (w.self.paused, w) := by
  simp [isPaused]

theorem pause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run pause ctx w =
      .ok ((), { w with
        self := { w.self with paused := Flag.on }
        log := w.log ++ [Event.Paused] }) := by
  simp [pause, howner, Tx.run_bind, Tx.run_sender, Tx.run_load, Tx.run_require,
    Tx.run_store, Tx.run_emit, Tx.run_map, Tx.bind_apply, Tx.map_apply]
  rfl

theorem pause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run pause ctx w = .error (.user .NotOwner) := by
  simp [pause, h]

theorem unpause_ok (howner : ctx.sender = w.self.owner) :
    Tx.run unpause ctx w =
      .ok ((), { w with
        self := { w.self with paused := Flag.off }
        log := w.log ++ [Event.Unpaused] }) := by
  simp [unpause, howner, Tx.run_bind, Tx.run_sender, Tx.run_load, Tx.run_require,
    Tx.run_store, Tx.run_emit, Tx.run_map, Tx.bind_apply, Tx.map_apply]
  rfl

theorem unpause_only_owner (h : ctx.sender ≠ w.self.owner) :
    Tx.run unpause ctx w = .error (.user .NotOwner) := by
  simp [unpause, h]

/-! ### deposit

Peel with `deposit_guards` + closed `run_*_bind` lemmas. Never `simp [deposit]`:
that walks the token CALL.
-/

theorem deposit_reverts_when_paused (assets : Amount vaultAsset)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (deposit assets) ctx w = .error (.user .Paused) := by
  rw [deposit, run_load_bind, run_req_false hp]

theorem deposit_reverts_on_nonpos (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : ¬ 0 < assets) :
    Tx.run (deposit assets) ctx w = .error (.user .Zero) := by
  rw [deposit, run_load_bind, run_req_true hp, run_req_false hpos]

theorem deposit_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (deposit (0 : Amount vaultAsset)) ctx w = .error (.user .Zero) :=
  deposit_reverts_on_nonpos 0 hp (by simp)

theorem deposit_reverts_on_divByZero (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hts : w.self.totalShares.raw ≠ 0) (hta : w.self.totalAssets.raw = 0) :
    Tx.run (deposit assets) ctx w = .error (.arith .divByZero) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  rw [deposit_guards assets hp hpos, Tx.run_ite, if_neg hne]
  simp only [run_mulDivDown_ts]
  rw [if_pos hta]

theorem deposit_reverts_on_mul_overflow (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hts : w.self.totalShares.raw ≠ 0) (hta : w.self.totalAssets.raw ≠ 0)
    (hmul : ¬ w.self.totalShares.raw * assets.raw < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  have hne : ¬ w.self.totalShares = 0 := (Amount.ne_iff _ _).mpr hts
  rw [deposit_guards assets hp hpos, Tx.run_ite, if_neg hne]
  simp only [run_mulDivDown_ts]
  rw [if_neg hta, if_neg hmul]

theorem deposit_reverts_on_zero_shares (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound))
    (hminted : ¬ 0 < mintedShares w.self assets) :
    Tx.run (deposit assets) ctx w = .error (.user .ZeroShares) := by
  rw [deposit_guards assets hp hpos, Tx.run_ite]
  by_cases hts : w.self.totalShares = 0
  · have : 0 < mintedShares w.self assets := by simpa [mintedShares, hts] using hpos
    exact (hminted this).elim
  · have htsr : w.self.totalShares.raw ≠ 0 := (Amount.ne_iff _ _).mp hts
    rcases hprod with h0 | ⟨hta, hmul⟩
    · exact (htsr h0).elim
    · rw [if_neg hts]
      rw [run_rate_mulDiv (hta := hta) (hmul := hmul)]
      apply run_req_false
      simpa [mintedShares, hts, htsr, Amount.lt_iff] using hminted

theorem deposit_reverts_on_one_overflow (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hts : w.self.totalShares = 0) (hfit : ¬ assets.raw < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_guards assets hp hpos, Tx.run_ite, if_pos hts]
  rw [run_oneS_mulDiv_overflow (hfit := hfit)]

theorem deposit_reverts_on_add_assets (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound))
    (hfit : w.self.totalShares.raw = 0 → assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self assets)
    (hadd : ¬ w.self.totalAssets.raw + assets.raw < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_after_mint assets hp hpos hprod hfit hminted]
  simp only [run_hAdd_bind]
  rw [if_neg hadd]

theorem deposit_reverts_on_add_shares (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound))
    (hfit : w.self.totalShares.raw = 0 → assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self assets)
    (haddA : w.self.totalAssets.raw + assets.raw < wordBound)
    (haddS : ¬ w.self.totalShares.raw + mintedShares w.self assets < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_after_mint assets hp hpos hprod hfit hminted]
  simp only [run_hAdd_bind]
  rw [if_pos haddA, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_neg haddS]

theorem deposit_reverts_on_add_bal (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound))
    (hfit : w.self.totalShares.raw = 0 → assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self assets)
    (haddA : w.self.totalAssets.raw + assets.raw < wordBound)
    (haddS : w.self.totalShares.raw + mintedShares w.self assets < wordBound)
    (haddB : ¬ (w.self.shares ctx.sender).raw + mintedShares w.self assets < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_after_mint assets hp hpos hprod hfit hminted]
  simp only [run_hAdd_bind]
  rw [if_pos haddA, run_store_bind]
  simp only [run_hAdd_bind]
  rw [if_pos haddS, run_store_bind, run_loadMap_bind]
  simp only [run_hAdd_bind]
  rw [if_neg haddB]

structure DepositOk (ctx : Ctx) (w : World Storage ExtState Event)
    (assets : Amount vaultAsset) : Prop where
  paused : w.self.paused = Flag.off
  pos : 0 < assets
  mintedPos : 0 < mintedShares w.self assets
  prod :
    w.self.totalShares.raw = 0 ∨
      (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound)
  mintFit : w.self.totalShares.raw = 0 → assets.raw < wordBound
  addAssets : w.self.totalAssets.raw + assets.raw < wordBound
  addShares : w.self.totalShares.raw + mintedShares w.self assets < wordBound
  addBal : (w.self.shares ctx.sender).raw + mintedShares w.self assets < wordBound

/-- Reduce a well-formed `deposit` to the token pull + emit on post-storage. -/
theorem deposit_to_tail (assets : Amount vaultAsset) (h : DepositOk ctx w assets) :
    let minted := Amount.ofWord (mintedShares w.self assets)
    Tx.run (deposit assets) ctx w =
      Tx.run (
        safeTransferFrom (E := Event) w.self.asset ctx.sender ctx.self assets
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.Deposit ctx.sender assets minted) >>= fun _ =>
        (pure minted : Tx Storage ExtState Event Error (Amount vShare)))
        ctx { w with self := depositPost w.self ctx.sender assets } := by
  rcases h with ⟨hp, hpos, hminted, hprod, hfit, haddA, haddS, haddB⟩
  rw [deposit_after_mint assets hp hpos hprod hfit hminted]
  simp only [run_hAdd_bind]
  rw [if_pos haddA, run_store_ta]
  simp only [run_hAdd_bind]
  rw [if_pos haddS, run_store_ts, run_loadMap_bind]
  simp only [run_hAdd_bind]
  rw [if_pos haddB, run_storeMap_shares, run_read_asset]
  dsimp
  have hσ :
      { asset := w.self.asset, owner := w.self.owner, paused := w.self.paused,
        totalAssets := w.self.totalAssets + assets,
        totalShares := w.self.totalShares +
          Amount.ofWord (mintedShares w.self assets),
        shares := fun k => Amount.ofWord
          (Function.update (fun i => (w.self.shares i).raw) ctx.sender
            ((w.self.shares ctx.sender).raw + mintedShares w.self assets) k) } =
        depositPost w.self ctx.sender assets := by
    unfold depositPost
    have h := Amount.update_raw w.self.shares ctx.sender
      ((w.self.shares ctx.sender).raw + mintedShares w.self assets)
    rw [Amount.ofWord_add_left] at h
    simpa using h
  rw [hσ]
  rfl

theorem deposit_ok_of_run {assets : Amount vaultAsset} {n : Amount vShare}
    {w' : World Storage ExtState Event}
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    DepositOk ctx w assets := by
  have hp : w.self.paused = Flag.off := by
    by_contra h; exact Tx.run_ok_error hrun (deposit_reverts_when_paused assets h)
  have hpos : 0 < assets := by
    by_contra h; exact Tx.run_ok_error hrun (deposit_reverts_on_nonpos assets hp h)
  have hprod :
      w.self.totalShares.raw = 0 ∨
        (w.self.totalAssets.raw ≠ 0 ∧ w.self.totalShares.raw * assets.raw < wordBound) := by
    by_cases hts : w.self.totalShares.raw = 0
    · exact Or.inl hts
    · by_cases hta : w.self.totalAssets.raw = 0
      · exact (Tx.run_ok_error hrun (deposit_reverts_on_divByZero assets hp hpos hts hta)).elim
      · by_cases hmul : w.self.totalShares.raw * assets.raw < wordBound
        · exact Or.inr ⟨hta, hmul⟩
        · exact (Tx.run_ok_error hrun
            (deposit_reverts_on_mul_overflow assets hp hpos hts hta hmul)).elim
  have hminted : 0 < mintedShares w.self assets := by
    by_contra h
    exact Tx.run_ok_error hrun (deposit_reverts_on_zero_shares assets hp hpos hprod h)
  have hfit : w.self.totalShares.raw = 0 → assets.raw < wordBound := by
    intro hts0
    by_contra hnb
    have hts : w.self.totalShares = 0 := (Amount.eq_iff _ _).mpr hts0
    exact Tx.run_ok_error hrun (deposit_reverts_on_one_overflow assets hp hpos hts hnb)
  have haddA : w.self.totalAssets.raw + assets.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (deposit_reverts_on_add_assets assets hp hpos hprod hfit hminted h)
  have haddS : w.self.totalShares.raw + mintedShares w.self assets < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (deposit_reverts_on_add_shares assets hp hpos hprod hfit hminted haddA h)
  have haddB : (w.self.shares ctx.sender).raw + mintedShares w.self assets < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun
      (deposit_reverts_on_add_bal assets hp hpos hprod hfit hminted haddA haddS h)
  exact ⟨hp, hpos, hminted, hprod, hfit, haddA, haddS, haddB⟩

/-- Exact storage / log / oracle of a successful `deposit`. -/
theorem deposit_post (assets : Amount vaultAsset) {n : Amount vShare}
    {w' : World Storage ExtState Event}
    (h : DepositOk ctx w assets)
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    n = Amount.ofWord (mintedShares w.self assets) ∧
      w'.self = depositPost w.self ctx.sender assets ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Deposit ctx.sender assets
        (Amount.ofWord (mintedShares w.self assets))] := by
  have heq := deposit_to_tail assets h
  rw [heq] at hrun
  rw [run_safeTF_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    rcases transferFrom_frame
        (w := { w with self := depositPost w.self ctx.sender assets })
        (by simpa [tfCall] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · rw [run_emit_pure] at hrun
      simp [hself1, hor1, hlog1] at hrun
      obtain ⟨hn, rfl⟩ := hrun
      exact ⟨Amount.ext hn.symm, rfl, rfl, rfl⟩

/-- The successful `deposit` CALL, for applying `IERC20.Spec`. -/
theorem deposit_call (assets : Amount vaultAsset) {n : Amount vShare}
    {w' : World Storage ExtState Event}
    (h : DepositOk ctx w assets)
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    ∃ w1, Tx.run (tfCall w.self.asset ctx.sender ctx.self assets) ctx w =
        .ok (true, w1) ∧
      w1.self = w.self ∧ w1.oracle = w.oracle ∧ w1.log = w.log ∧
      w'.ext = w1.ext ∧ w'.oracle = w.oracle := by
  have ⟨_, hσ, hor, _⟩ := deposit_post assets h hrun
  have heq := deposit_to_tail assets h
  rw [heq] at hrun
  rw [run_safeTF_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    have htf := transferFrom_call_ignore_self
      (σ := depositPost w.self ctx.sender assets)
      (by simpa [tfCall] using hcall)
    cases b
    · simp at hrun
    · refine ⟨{ w with ext := w1.ext }, htf.1, rfl, rfl, rfl, ?_, hor⟩
      rw [run_emit_pure] at hrun
      simp [htf.2.1, htf.2.2.1, htf.2.2.2] at hrun
      obtain ⟨_, rfl⟩ := hrun
      rfl

/-! ### withdraw

Peel with `withdraw_guards` + closed `run_*_bind` lemmas. Never `simp [withdraw]`.
-/

theorem withdraw_reverts_when_paused (sharesIn : Amount vShare)
    (hp : w.self.paused ≠ Flag.off) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Paused) := by
  rw [withdraw, run_load_bind, run_req_false hp]

theorem withdraw_reverts_on_nonpos (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : ¬ 0 < sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .Zero) := by
  rw [withdraw, run_load_bind, run_req_true hp, run_req_false hpos]

theorem withdraw_reverts_on_zero (hp : w.self.paused = Flag.off) :
    Tx.run (withdraw (0 : Amount vShare)) ctx w = .error (.user .Zero) :=
  withdraw_reverts_on_nonpos 0 hp (by simp)

theorem withdraw_reverts_on_insufficient_shares (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : w.self.shares ctx.sender < sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .InsufficientShares) := by
  rw [withdraw, run_load_bind, run_req_true hp, run_req_true hpos,
    run_sender_bind, run_loadMap_bind]
  exact run_req_false (Amount.not_le_of_gt hbal)

theorem withdraw_reverts_on_divByZero (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares.raw = 0) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .divByZero) := by
  rw [withdraw_guards sharesIn hp hpos hbal]
  simp only [run_mulDivDown_ta]
  rw [if_pos hden]

theorem withdraw_reverts_on_mul_overflow (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares.raw ≠ 0)
    (hmul : ¬ w.self.totalAssets.raw * sharesIn.raw < wordBound) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .overflow) := by
  rw [withdraw_guards sharesIn hp hpos hbal]
  simp only [run_mulDivDown_ta]
  rw [if_neg hden, if_neg hmul]

theorem withdraw_reverts_on_zero_assets (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares.raw ≠ 0)
    (hmul : w.self.totalAssets.raw * sharesIn.raw < wordBound)
    (hzero : ¬ 0 < redeemedAssets w.self sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .ZeroAssets) := by
  rw [withdraw_guards sharesIn hp hpos hbal]
  simp only [run_mulDivDown_ta]
  rw [if_neg hden, if_pos hmul]
  apply run_req_false
  simpa [redeemedAssets, Amount.lt_iff] using hzero

structure WithdrawOk (ctx : Ctx) (w : World Storage ExtState Event)
    (sharesIn : Amount vShare) : Prop where
  paused : w.self.paused = Flag.off
  pos : 0 < sharesIn
  bal : sharesIn ≤ w.self.shares ctx.sender
  supply : sharesIn ≤ w.self.totalShares
  denom : w.self.totalShares.raw ≠ 0
  prod : w.self.totalAssets.raw * sharesIn.raw < wordBound
  assetsPos : 0 < redeemedAssets w.self sharesIn
  assetsFit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets.raw

theorem withdraw_reverts_on_insufficient_supply (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hden : w.self.totalShares.raw ≠ 0)
    (hmul : w.self.totalAssets.raw * sharesIn.raw < wordBound)
    (hassets : 0 < redeemedAssets w.self sharesIn)
    (hsup : w.self.totalShares < sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .underflow) := by
  rw [withdraw_after_redeem sharesIn hp hpos hbal hden hmul hassets]
  simp only [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hbal), run_storeMap_bind]
  simp only [run_hSub_bind]
  rw [if_neg (Nat.not_le_of_gt ((Amount.lt_iff _ _).mp hsup))]

theorem withdraw_reverts_on_assets_underflow (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hsup : sharesIn ≤ w.self.totalShares) (hden : w.self.totalShares.raw ≠ 0)
    (hmul : w.self.totalAssets.raw * sharesIn.raw < wordBound)
    (hassets : 0 < redeemedAssets w.self sharesIn)
    (hfit : ¬ redeemedAssets w.self sharesIn ≤ w.self.totalAssets.raw) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .underflow) := by
  rw [withdraw_after_redeem sharesIn hp hpos hbal hden hmul hassets]
  simp only [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hbal), run_storeMap_bind]
  simp only [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hsup), run_store_bind]
  simp only [run_hSub_bind]
  rw [if_neg hfit]

theorem withdraw_to_tail (sharesIn : Amount vShare) (h : WithdrawOk ctx w sharesIn) :
    let amt := Amount.ofWord (redeemedAssets w.self sharesIn)
    let σ' := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (
        safeTransfer (E := Event) w.self.asset ctx.sender amt Error.TransferFailed >>=
          fun _ =>
        Tx.emit (.Withdraw ctx.sender amt sharesIn) >>= fun _ =>
        (pure amt : Tx Storage ExtState Event Error (Amount vaultAsset)))
        ctx { w with self := σ' } := by
  rcases h with ⟨hp, hpos, hbal, hsup, hden, hmul, hassets, hfit⟩
  rw [withdraw_after_redeem sharesIn hp hpos hbal hden hmul hassets]
  simp only [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hbal), run_storeMap_shares]
  simp only [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hsup), run_store_ts]
  simp only [run_hSub_bind]
  rw [if_pos hfit, run_store_ta, run_read_asset]
  dsimp
  have hσ :
      { asset := w.self.asset, owner := w.self.owner, paused := w.self.paused,
        totalAssets := w.self.totalAssets -
          Amount.ofWord (redeemedAssets w.self sharesIn),
        totalShares := w.self.totalShares - sharesIn,
        shares := fun k => Amount.ofWord
          (Function.update (fun i => (w.self.shares i).raw) ctx.sender
            ((w.self.shares ctx.sender).raw - sharesIn.raw) k) } =
        withdrawPost w.self ctx.sender sharesIn
          (redeemedAssets w.self sharesIn) := by
    unfold withdrawPost
    have h := Amount.update_raw w.self.shares ctx.sender
      ((w.self.shares ctx.sender).raw - sharesIn.raw)
    rw [Amount.ofWord_sub] at h
    simpa using h
  rw [hσ]
  rfl

theorem withdraw_ok_of_run {sharesIn : Amount vShare} {n : Amount vaultAsset}
    {w' : World Storage ExtState Event}
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    WithdrawOk ctx w sharesIn := by
  have hp : w.self.paused = Flag.off := by
    by_contra h; exact Tx.run_ok_error hrun (withdraw_reverts_when_paused sharesIn h)
  have hpos : 0 < sharesIn := by
    by_contra h; exact Tx.run_ok_error hrun (withdraw_reverts_on_nonpos sharesIn hp h)
  have hbal : sharesIn ≤ w.self.shares ctx.sender := by
    by_contra h
    exact Tx.run_ok_error hrun
      (withdraw_reverts_on_insufficient_shares sharesIn hp hpos
        ((Amount.lt_iff (w.self.shares ctx.sender) sharesIn).mpr
          (Nat.not_le.mp (mt (Amount.le_iff sharesIn _).mpr h))))
  have hden : w.self.totalShares.raw ≠ 0 := by
    by_contra h
    exact Tx.run_ok_error hrun (withdraw_reverts_on_divByZero sharesIn hp hpos hbal h)
  have hmul : w.self.totalAssets.raw * sharesIn.raw < wordBound := by
    by_contra h
    exact Tx.run_ok_error hrun (withdraw_reverts_on_mul_overflow sharesIn hp hpos hbal hden h)
  have hassets : 0 < redeemedAssets w.self sharesIn := by
    by_contra h
    exact Tx.run_ok_error hrun
      (withdraw_reverts_on_zero_assets sharesIn hp hpos hbal hden hmul h)
  have hsup : sharesIn ≤ w.self.totalShares := by
    by_contra h
    exact Tx.run_ok_error hrun (withdraw_reverts_on_insufficient_supply sharesIn
      hp hpos hbal hden hmul hassets
        ((Amount.lt_iff w.self.totalShares sharesIn).mpr
          (Nat.not_le.mp (mt (Amount.le_iff sharesIn _).mpr h))))
  have hfit : redeemedAssets w.self sharesIn ≤ w.self.totalAssets.raw := by
    by_contra h
    exact Tx.run_ok_error hrun (withdraw_reverts_on_assets_underflow sharesIn
      hp hpos hbal hsup hden hmul hassets h)
  exact ⟨hp, hpos, hbal, hsup, hden, hmul, hassets, hfit⟩

theorem withdraw_post (sharesIn : Amount vShare) {n : Amount vaultAsset}
    {w' : World Storage ExtState Event}
    (h : WithdrawOk ctx w sharesIn)
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    n = Amount.ofWord (redeemedAssets w.self sharesIn) ∧
      w'.self = withdrawPost w.self ctx.sender sharesIn
        (redeemedAssets w.self sharesIn) ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Withdraw ctx.sender
        (Amount.ofWord (redeemedAssets w.self sharesIn)) sharesIn] := by
  have heq := withdraw_to_tail sharesIn h
  rw [heq] at hrun
  rw [run_safeTR_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    set σP :=
      withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
    rcases transfer_frame (w := { w with self := σP })
        (by simpa [trCall] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · rw [run_emit_pure] at hrun
      simp [hself1, hor1, hlog1] at hrun
      obtain ⟨hn, rfl⟩ := hrun
      exact ⟨Amount.ext hn.symm, rfl, rfl, rfl⟩

theorem withdraw_call (sharesIn : Amount vShare) {n : Amount vaultAsset}
    {w' : World Storage ExtState Event}
    (h : WithdrawOk ctx w sharesIn)
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    let amt := Amount.ofWord (redeemedAssets w.self sharesIn)
    let σ' := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
    ∃ w1, Tx.run (trCall w.self.asset ctx.sender amt) ctx { w with self := σ' } =
        .ok (true, w1) ∧
      w1.self = σ' ∧ w1.oracle = w.oracle ∧
      w'.ext = w1.ext ∧ w'.oracle = w.oracle ∧ w'.self = σ' := by
  have ⟨_, hσ, hor, _⟩ := withdraw_post sharesIn h hrun
  have heq := withdraw_to_tail sharesIn h
  rw [heq] at hrun
  rw [run_safeTR_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    set σP :=
      withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
    rcases transfer_frame (w := { w with self := σP })
        (by simpa [trCall] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · refine ⟨w1, by simpa [trCall] using hcall, hself1, hor1, ?_, hor, hσ⟩
      rw [run_emit_pure] at hrun
      simp [hself1, hor1, hlog1] at hrun
      obtain ⟨_, rfl⟩ := hrun
      rfl

/-! ### Exchange-rate monotonicity (floor mint / redeem) -/

private theorem div_le_div_of_mul_le {x y c d : Nat}
    (hc : 0 < c) (hd : 0 < d) (h : x * d ≤ y * c) : x / c ≤ y / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hx : x / c * c ≤ x := Nat.div_mul_le_self x c
  have h1 : x / c * c * d ≤ y * c := Nat.le_trans (Nat.mul_le_mul_right d hx) h
  rw [Nat.mul_assoc, Nat.mul_comm c d, ← Nat.mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_right h1 hc

theorem withdraw_rate_nondecreasing (TA TS sa s : Nat)
    (hTS : 0 < TS) (hs : s < TS) :
    sa * TA / TS ≤ sa * (TA - s * TA / TS) / (TS - s) := by
  set a := s * TA / TS
  have hTS' : 0 < TS - s := Nat.sub_pos_of_lt hs
  have hrate : TA * (TS - s) ≤ (TA - a) * TS := by
    have h1 : TA * (TS - s) = TA * TS - TA * s := Nat.mul_sub TA TS s
    have h2 : (TA - a) * TS = TA * TS - a * TS := Nat.sub_mul TA a TS
    have h3 : a * TS ≤ TA * s := by
      calc
        a * TS ≤ s * TA := Nat.div_mul_le_self (s * TA) TS
        _ = TA * s := Nat.mul_comm _ _
    rw [h1, h2]
    exact Nat.sub_le_sub_left h3 _
  have hprod : sa * TA * (TS - s) ≤ sa * (TA - a) * TS := by
    calc
      sa * TA * (TS - s) = sa * (TA * (TS - s)) := Nat.mul_assoc _ _ _
      _ ≤ sa * ((TA - a) * TS) := Nat.mul_le_mul_left sa hrate
      _ = sa * (TA - a) * TS := (Nat.mul_assoc _ _ _).symm
  exact div_le_div_of_mul_le hTS hTS' hprod

theorem deposit_rate_nondecreasing (TA TS sa assets : Nat)
    (hTS : 0 < TS) :
    sa * TA / TS ≤ sa * (TA + assets) / (TS + assets * TS / TA) := by
  set m := assets * TS / TA
  have hTS' : 0 < TS + m := Nat.lt_of_lt_of_le hTS (Nat.le_add_right _ _)
  have hrate : TA * (TS + m) ≤ (TA + assets) * TS := by
    have h1 : TA * (TS + m) = TA * TS + TA * m := Nat.mul_add TA TS m
    have h2 : (TA + assets) * TS = TA * TS + assets * TS := Nat.add_mul TA assets TS
    have h3 : TA * m ≤ assets * TS := by
      calc
        TA * m = m * TA := Nat.mul_comm _ _
        _ ≤ assets * TS := Nat.div_mul_le_self (assets * TS) TA
    rw [h1, h2]
    exact Nat.add_le_add_left h3 _
  have hprod : sa * TA * (TS + m) ≤ sa * (TA + assets) * TS := by
    calc
      sa * TA * (TS + m) = sa * (TA * (TS + m)) := Nat.mul_assoc _ _ _
      _ ≤ sa * ((TA + assets) * TS) := Nat.mul_le_mul_left sa hrate
      _ = sa * (TA + assets) * TS := (Nat.mul_assoc _ _ _).symm
  exact div_le_div_of_mul_le hTS hTS' hprod

namespace Proof

theorem deposit_shares {assets : Amount vaultAsset} {minted : Amount vShare}
    {w' : World Storage ExtState Event}
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender + minted ∧
      w'.self.totalShares = w.self.totalShares + minted ∧
      w'.self.totalAssets = w.self.totalAssets + assets := by
  have hok := deposit_ok_of_run h
  have ⟨hn, hσ, _, _⟩ := deposit_post assets hok h
  subst hn
  simp [hσ, depositPost, Amount.raw_add, Amount.raw_ofWord]

theorem deposit_holdings {assets : Amount vaultAsset} {minted : Amount vShare}
    {w' : World Storage ExtState Event}
    (hT : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    holdings ctx.self w' = holdings ctx.self w + assets.raw := by
  have hok := deposit_ok_of_run h
  have ⟨w1, htf, hself1, hor1, _, hext, hor⟩ := deposit_call assets hok h
  have ⟨_, hσ, _, _⟩ := deposit_post assets hok h
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w) (w' := w1)
    (by simpa [impl_transferFrom] using htf)
  have hdst := hmoves.2.1 hne
  have hbal : holdings ctx.self w1 = holdings ctx.self w + assets.raw := by
    simpa [holdings, IERC20.Ref.impl, Amount.raw_add, hself1, hor1] using
      congrArg Amount.raw hdst
  have heqH : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, depositPost, hself1])
      (hor.trans hor1.symm) hext
  simpa [heqH] using hbal

theorem withdraw_shares {sharesIn : Amount vShare} {paid : Amount vaultAsset}
    {w' : World Storage ExtState Event}
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender - sharesIn ∧
      w'.self.totalShares = w.self.totalShares - sharesIn ∧
      w'.self.totalAssets = w.self.totalAssets - paid := by
  have hok := withdraw_ok_of_run h
  have ⟨hn, hσ, _, _⟩ := withdraw_post sharesIn hok h
  subst hn
  simp [hσ, withdrawPost, Amount.raw_sub, Amount.raw_ofWord]

theorem withdraw_holdings {sharesIn : Amount vShare} {paid : Amount vaultAsset}
    {w' : World Storage ExtState Event}
    (hT : IERC20.Spec (w.self.asset.impl w :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    holdings ctx.self w' + paid.raw = holdings ctx.self w := by
  have hok := withdraw_ok_of_run h
  have ⟨hn, hσ, hor, _⟩ := withdraw_post sharesIn hok h
  obtain ⟨w1, htr, hself1, hor1, hext, _, _⟩ := withdraw_call sharesIn hok h
  subst hn
  set σ' := withdrawPost w.self ctx.sender sharesIn (redeemedAssets w.self sharesIn)
  set amt := Amount.ofWord (redeemedAssets w.self sharesIn)
  let wCall : World Storage ExtState Event := { w with self := σ' }
  have hTcall : IERC20.Spec
      (wCall.self.asset.impl wCall :
        IERC20.Impl vaultAsset (World Storage ExtState Event) Error) := by
    dsimp [wCall]
    simpa [IERC20.Ref.impl, σ', withdrawPost] using hT
  have hrunT :
      (wCall.self.asset.impl wCall :
          IERC20.Impl vaultAsset (World Storage ExtState Event) Error).transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall =
        .ok (true, w1) := by
    dsimp [wCall]
    have htr' :
        Tx.run (trCall w.self.asset ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := w.self.asset) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      simpa [wCall, σ', amt] using htr
    simpa [impl_transfer, σ', amt, withdrawPost, wCall] using htr'
  have hmoves := hTcall.transfer_moves hrunT
  have hto := hmoves.2.1 hne.symm
  have hsumr := congrArg Amount.raw hmoves.1
  rw [Amount.raw_add, Amount.raw_add] at hsumr
  simp at hsumr
  have htor := congrArg Amount.raw hto
  simp [Amount.raw_add] at htor
  have heq1 : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, σ', hself1]) (hor.trans hor1.symm) hext
  have heq0 : holdings ctx.self wCall = holdings ctx.self w :=
    holdings_congr ctx.self (by simp [wCall, σ', withdrawPost]) rfl rfl
  have hs : w1.self = wCall.self := by simp [hself1, wCall]
  rw [heq1, ← heq0]
  clear heq1 heq0
  unfold holdings
  rw [hs]
  dsimp only
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

end Proof

end Vault
