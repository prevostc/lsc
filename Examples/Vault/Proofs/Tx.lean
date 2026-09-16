import Mathlib.Tactic.SplitIfs
import Examples.Vault.Spec
import Stdlib.SafeERC20
import Stdlib.SharesTheorems
import Lsc.Lang.TxTheorems
import Lsc.Lang.AmountTheorems
import Lsc.Lang.InterfaceTheorems

set_option linter.unusedSimpArgs false
/-!
Vault `Tx.run` lemmas. External CALLs are opaque; success lemmas recover
storage, logs, and the oracle, and use `IERC20.Spec` for holdings.
-/

open Lsc Lsc.Syntax Lsc.Stdlib Vault

attribute [local simp] Amount.eq_iff Amount.ne_iff Amount.lt_iff Amount.le_iff

namespace Vault

variable {ctx : Ctx} {w : World}

abbrev tfCall (r : IERC20.Ref vaultAsset) (src dst : Address)
    (amt : Amount vaultAsset) : Tx Storage ExtState Event Error Bool :=
  r.transferFrom src dst amt

abbrev trCall (r : IERC20.Ref vaultAsset) (dst : Address)
    (amt : Amount vaultAsset) : Tx Storage ExtState Event Error Bool :=
  r.transfer dst amt

/-- Shares that `deposit` mints from live holdings `ta` (virtual offset). -/
def mintedShares (ts : Amount vShare) (ta assets : Amount vaultAsset) : Nat :=
  Shares.toSharesRaw offset assets.raw ta.raw ts.raw

private theorem scale_offset : Word.scale offset.decimals = 1000000 := by
  rw [show offset.decimals = 6 from rfl, ← Shares.virtual6_scale, Shares.virtual6_eq]

private theorem mintedShares_formula (ts : Amount vShare)
    (ta assets : Amount vaultAsset) :
    mintedShares ts ta assets =
      (ts.raw + 1000000) * assets.raw / (ta.raw + 1) := by
  unfold mintedShares Shares.toSharesRaw
  rw [scale_offset, Nat.mul_comm]

/-- Storage after a successful `deposit` by `who`. -/
def depositPost (σ : Storage) (who : Address) (minted : Nat) : Storage :=
  let n : Amount vShare := Amount.ofWord minted
  { σ with
    totalShares := σ.totalShares + n
    shares := Function.update σ.shares who (σ.shares who + n) }

/-- Assets `withdraw` pays from live holdings `ta` (virtual offset). -/
def redeemedAssets (ts : Amount vShare) (ta : Amount vaultAsset)
    (sharesIn : Amount vShare) : Nat :=
  Shares.toAssetsRaw offset sharesIn.raw ta.raw ts.raw

private theorem redeemedAssets_formula (ts : Amount vShare)
    (ta : Amount vaultAsset) (sharesIn : Amount vShare) :
    redeemedAssets ts ta sharesIn =
      (ta.raw + 1) * sharesIn.raw / (ts.raw + 1000000) := by
  unfold redeemedAssets Shares.toAssetsRaw
  rw [scale_offset, Nat.mul_comm]

/-- Storage after a successful `withdraw` by `who`. -/
def withdrawPost (σ : Storage) (who : Address) (sharesIn : Amount vShare) :
    Storage :=
  { σ with
    totalShares := σ.totalShares - sharesIn
    shares := Function.update σ.shares who (σ.shares who - sharesIn) }

private theorem depositPost_of_stores (σ : Storage) (who : Address)
    (minted : Nat) :
    { σ with
      totalShares := σ.totalShares + Amount.ofWord minted
      shares := fun k => Amount.ofWord
        (Function.update (fun i => (σ.shares i).raw) who
          ((σ.shares who).raw + minted) k) } =
      depositPost σ who minted := by
  simp [depositPost, Amount.update_raw, Amount.ofWord_add_right, Amount.ofWord_raw]

private theorem withdrawPost_of_stores (σ : Storage) (who : Address)
    (sharesIn : Amount vShare) :
    { σ with
      totalShares := σ.totalShares - sharesIn
      shares := fun i => Amount.ofWord
        (Function.update (fun i => (σ.shares i).raw) who
          ((σ.shares who).raw - sharesIn.raw) i) } =
      withdrawPost σ who sharesIn := by
  simp [withdrawPost, Amount.update_raw, Amount.ofWord_sub]

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

@[simp] theorem balSel_eq : balSel = 0x70a08231 := by decide
@[simp] theorem supplySel_eq : supplySel = 0x18160ddd := by decide

theorem impl_balanceOf (r : IERC20.Ref vaultAsset) (who : Address)
    (w₀ : World) :
    r.impl.balanceOf who w₀.view = viewBal r who w₀.oracle w₀.ext := by
  simp [IERC20.Ref.impl, IERC20.Impl.ofRef, viewBal, World.view]

theorem holdings_view (self : Address) :
    holdings self w = (viewBal w.self.asset self w.oracle w.ext).raw := by
  simp [holdings, holdingsAt, impl_balanceOf]

theorem holdingsAt_congr (self : Address) {w w' : World}
    (ha : w'.self.asset.addr = w.self.asset.addr)
    (ho : w'.oracle = w.oracle) (hx : w'.ext = w.ext) :
    holdingsAt self w' = holdingsAt self w := by
  simp [holdingsAt, IERC20.Ref.impl, IERC20.Impl.ofRef, ha, ho, hx, World.view]

theorem holdings_congr (self : Address) {w w' : World}
    (ha : w'.self.asset.addr = w.self.asset.addr)
    (ho : w'.oracle = w.oracle) (hx : w'.ext = w.ext) :
    holdings self w' = holdings self w :=
  congrArg Amount.raw (holdingsAt_congr self ha ho hx)

theorem transferFrom_frame {r : IERC20.Ref vaultAsset}
    {src dst : Address} {amt : Amount vaultAsset} {b : Bool}
    {w' : World}
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
    {w' : World}
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
    r.impl.transferFrom src dst amt ctx w.view =
      (Tx.run (tfCall r src dst amt) ctx w).toOption.map
        (Prod.map id World.view) := by
  simp only [IERC20.Ref.impl, IERC20.Impl.ofRef, IERC20.Ref.transferFrom, tfCall]
  exact Tx.callDecode_view (α := Bool) (ε := Error) r.addr (0x23b872dd : Nat)
    [AbiType.encode src, AbiType.encode dst, AbiType.encode amt] ctx w

theorem impl_transfer (r : IERC20.Ref vaultAsset)
    (dst : Address) (amt : Amount vaultAsset) :
    r.impl.transfer dst amt ctx w.view =
      (Tx.run (trCall r dst amt) ctx w).toOption.map
        (Prod.map id World.view) := by
  simp only [IERC20.Ref.impl, IERC20.Impl.ofRef, IERC20.Ref.transfer, trCall]
  exact Tx.callDecode_view (α := Bool) (ε := Error) r.addr (0xa9059cbb : Nat)
    [AbiType.encode dst, AbiType.encode amt] ctx w

theorem transfer_run_ctx_irrel {r : IERC20.Ref vaultAsset}
    {dst : Address} {amt : Amount vaultAsset} {ctx' : Ctx}
    {w₀ : World} :
    Tx.run (trCall r dst amt) ctx w₀ =
      Tx.run (trCall r dst amt) ctx' w₀ := by
  simp [IERC20.Ref.transfer, Tx.run_call]

/-- A CALL ignores `self`; success on an updated storage world transports to
the original world with only `ext` changed. -/
theorem transferFrom_call_ignore_self {r : IERC20.Ref vaultAsset}
    {src dst : Address} {amt : Amount vaultAsset} {σ : Storage} {b : Bool}
    {w1 : World}
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

private theorem run_pure_bind {α β : Type} (a : α)
    (k : α → Tx Storage ExtState Event Error β) :
    Tx.run (pure a >>= k) ctx w = Tx.run (k a) ctx w := by
  simp [Tx.run_bind, Tx.run_pure]

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
private theorem run_safeTF_bind {α : Type} {w₀ : World}
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
private theorem run_safeTR_bind {α : Type} {w₀ : World}
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

private theorem run_emit_pure {w₀ : World}
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

/-- `ts mulDiv↓ assets / ta`. Closed; no CALL. -/
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

/-- Decode of `balanceOf` at `r` for `who`. -/
def viewBal? (r : IERC20.Ref vaultAsset) (who : Address)
    (w₀ : World) : Option (Amount vaultAsset) :=
  AbiRetType.decode (α := Amount vaultAsset)
    (w₀.oracle.view r.addr balSel [AbiType.encode who] w₀.ext)

theorem viewBal?_eq (r : IERC20.Ref vaultAsset) (who : Address)
    (w₀ : World) :
    viewBal? r who w₀ =
      AbiRetType.decode (α := Amount vaultAsset)
        (w₀.oracle.view r.addr (0x70a08231) [AbiType.encode who] w₀.ext) := by
  simp [viewBal?, balSel_eq]

private theorem run_balanceOf (r : IERC20.Ref vaultAsset) (who : Address)
    (w₀ : World) :
    Tx.run (r.balanceOf who : Tx Storage ExtState Event Error (Amount vaultAsset))
        ctx w₀ =
      match viewBal? r who w₀ with
      | none => .error .callFailed
      | some v => .ok (v, w₀) := by
  simp only [IERC20.Ref.balanceOf, Tx.run_view, viewBal?, balSel_eq,
    Tx.encode_address]
  generalize hrets : w₀.oracle.view r.addr (0x70a08231) [who.toWord] w₀.ext = rets
  cases AbiRetType.decode (α := Amount vaultAsset) rets <;> rfl

private theorem run_balanceOf_bind {α : Type}
    {w₀ : World}
    (r : IERC20.Ref vaultAsset) (who : Address)
    (k : Amount vaultAsset → Tx Storage ExtState Event Error α) :
    Tx.run (r.balanceOf who >>= k) ctx w₀ =
      match viewBal? r who w₀ with
      | none => .error .callFailed
      | some v => Tx.run (k v) ctx w₀ := by
  rw [Tx.run_bind, run_balanceOf]
  cases viewBal? r who w₀ <;> rfl

theorem viewBal?_some_holdings (self : Address)
    {ta : Amount vaultAsset}
    (h : viewBal? w.self.asset self w = some ta) :
    holdings self w = ta.raw := by
  simp only [holdings_view, viewBal, IERC20.Ref.impl, IERC20.Impl.ofRef,
    decodeOrDefault, viewBal?, balSel_eq] at h ⊢
  rw [h]
  rfl

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

/-- `Shares.toShares offset` then `k`. -/
private theorem run_toShares_binds {α : Type}
    (ts : Amount vShare) (ta assets : Amount vaultAsset)
    (k : Amount vShare → Tx Storage ExtState Event Error α) :
    Tx.run (Shares.toShares (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) offset assets ta ts >>= k) ctx w =
      if ts.raw + 1000000 < wordBound then
        if ta.raw + 1 < wordBound then
          if (ts.raw + 1000000) * assets.raw < wordBound then
            Tx.run (k ⟨mintedShares ts ta assets⟩) ctx w
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Shares.run_toShares]
  simp only [scale_offset]
  by_cases hV : ts.raw + 1000000 < wordBound
  · simp [hV]
    by_cases hA : ta.raw + 1 < wordBound
    · simp [hA]
      by_cases hM : (ts.raw + 1000000) * assets.raw < wordBound
      · simp [hM]
        rfl
      · simp [hM]
    · simp [hA]
  · simp [hV]

/-- `Shares.toAssets offset` then `k`. -/
private theorem run_toAssets_binds {α : Type}
    (ts : Amount vShare) (ta : Amount vaultAsset) (sharesIn : Amount vShare)
    (k : Amount vaultAsset → Tx Storage ExtState Event Error α) :
    Tx.run (Shares.toAssets (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) offset sharesIn ta ts >>= k) ctx w =
      if ta.raw + 1 < wordBound then
        if ts.raw + 1000000 < wordBound then
          if (ta.raw + 1) * sharesIn.raw < wordBound then
            Tx.run (k ⟨redeemedAssets ts ta sharesIn⟩) ctx w
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  rw [Tx.run_bind, Shares.run_toAssets]
  simp only [scale_offset]
  by_cases hA : ta.raw + 1 < wordBound
  · simp [hA]
    by_cases hV : ts.raw + 1000000 < wordBound
    · simp [hV]
      by_cases hM : (ta.raw + 1) * sharesIn.raw < wordBound
      · simp [hM]
        rfl
      · simp [hM]
    · simp [hV]
  · simp [hA]

/-- `previewDeposit` body: `Shares.toShares offset`. -/
private theorem run_toShares_val (ts : Amount vShare) (ta assets : Amount vaultAsset) :
    Tx.run (Shares.toShares (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) offset assets ta ts) ctx w =
      if ts.raw + 1000000 < wordBound then
        if ta.raw + 1 < wordBound then
          if (ts.raw + 1000000) * assets.raw < wordBound then
            .ok (⟨mintedShares ts ta assets⟩, w)
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  rw [Shares.run_toShares]
  simp only [scale_offset]
  by_cases hV : ts.raw + 1000000 < wordBound
  · simp [hV]
    by_cases hA : ta.raw + 1 < wordBound
    · simp [hA]
      by_cases hM : (ts.raw + 1000000) * assets.raw < wordBound
      · simp [hM]; rfl
      · simp [hM]
    · simp [hA]
  · simp [hV]

/-- `previewRedeem` body: `Shares.toAssets offset`. -/
private theorem run_toAssets_val (ts : Amount vShare) (ta : Amount vaultAsset)
    (sharesIn : Amount vShare) :
    Tx.run (Shares.toAssets (S := Storage) (X := ExtState) (E := Event)
        (ε := Error) offset sharesIn ta ts) ctx w =
      if ta.raw + 1 < wordBound then
        if ts.raw + 1000000 < wordBound then
          if (ta.raw + 1) * sharesIn.raw < wordBound then
            .ok (⟨redeemedAssets ts ta sharesIn⟩, w)
          else .error (.arith .overflow)
        else .error (.arith .overflow)
      else .error (.arith .overflow) := by
  rw [Shares.run_toAssets]
  simp only [scale_offset]
  by_cases hA : ta.raw + 1 < wordBound
  · simp [hA]
    by_cases hV : ts.raw + 1000000 < wordBound
    · simp [hV]
      by_cases hM : (ta.raw + 1) * sharesIn.raw < wordBound
      · simp [hM]; rfl
      · simp [hM]
    · simp [hV]
  · simp [hA]

/-- After pause/positivity, `deposit` is a `balanceOf` view then the mint join. -/
private theorem deposit_head (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets) :
    Tx.run (deposit assets) ctx w =
      match viewBal? w.self.asset ctx.self w with
      | none => .error .callFailed
      | some ta =>
        Tx.run (do
          let minted ← Shares.toShares offset assets ta w.self.totalShares
          Tx.require (0 < minted) Error.ZeroShares
          let ts' ← w.self.totalShares +? minted
          Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m })
            ts'.raw
          let bal' ←
            (Tx.loadMap (fun (σ : Storage) k => σ.shares k) ctx.sender) +? minted
          Tx.storeMap (fun σ k => (σ.shares k).raw)
            (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
            ctx.sender bal'.raw
          safeTransferFrom w.self.asset ctx.sender ctx.self assets
            Error.TransferFailed
          Tx.emit (.Deposit ctx.sender assets minted)
          pure minted) ctx w := by
  rw [deposit, run_load_bind, run_req_true hp, run_req_true hpos,
    run_sender_bind, run_self_bind]
  refine (run_read_asset _).trans ?_
  rw [run_balanceOf_bind]
  simp only [run_load_bind, Tx.bind_assoc]

private theorem deposit_head_some (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta) :
    Tx.run (deposit assets) ctx w =
      Tx.run (do
        let minted ← Shares.toShares offset assets ta w.self.totalShares
        Tx.require (0 < minted) Error.ZeroShares
        let ts' ← w.self.totalShares +? minted
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m })
          ts'.raw
        let bal' ←
          (Tx.loadMap (fun (σ : Storage) k => σ.shares k) ctx.sender) +? minted
        Tx.storeMap (fun σ k => (σ.shares k).raw)
          (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
          ctx.sender bal'.raw
        safeTransferFrom w.self.asset ctx.sender ctx.self assets
          Error.TransferFailed
        Tx.emit (.Deposit ctx.sender assets minted)
        pure minted) ctx w := by
  rw [deposit_head (ctx := ctx) assets hp hpos, hview]

/-- `deposit` after a successful mint, at the first `+?` of `totalShares`. -/
private theorem deposit_after_mint (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ta.raw + 1 < wordBound)
    (hmul : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self.totalShares ta assets) :
    Tx.run (deposit assets) ctx w =
      Tx.run (do
        let ts' ← Tx.HAddChecked.hAdd w.self.totalShares
          (⟨mintedShares w.self.totalShares ta assets⟩ : Amount vShare)
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        let bal' ←
          (Tx.loadMap (fun (σ : Storage) k => σ.shares k) ctx.sender) +?
            (⟨mintedShares w.self.totalShares ta assets⟩ : Amount vShare)
        Tx.storeMap (fun σ k => (σ.shares k).raw)
          (fun σ m => { σ with shares := fun k => Amount.ofWord (m k) })
          ctx.sender bal'.raw
        safeTransferFrom w.self.asset ctx.sender ctx.self assets Error.TransferFailed
        Tx.emit (.Deposit ctx.sender assets
          ⟨mintedShares w.self.totalShares ta assets⟩)
        pure (⟨mintedShares w.self.totalShares ta assets⟩ : Amount vShare))
        ctx w := by
  have hposM :
      0 < (⟨mintedShares w.self.totalShares ta assets⟩ : Amount vShare) := by
    simpa [Amount.lt_iff] using hminted
  rw [deposit_head_some assets hp hpos hview]
  conv =>
    lhs
    rw [run_toShares_binds]
    rw [if_pos hV]
    rw [if_pos hA]
    rw [if_pos hmul]
  rw [run_req_true hposM]


private theorem withdraw_head (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender) :
    Tx.run (withdraw sharesIn) ctx w =
      match viewBal? w.self.asset ctx.self w with
      | none => .error .callFailed
      | some ta =>
        Tx.run (do
          let assetsOut ← Shares.toAssets offset sharesIn ta w.self.totalShares
          Tx.require (0 < assetsOut) Error.ZeroAssets
          let bal' ← w.self.shares ctx.sender -? sharesIn
          Tx.storeMap (fun σ i => (σ.shares i).raw)
            (fun σ m => { σ with shares := fun i => Amount.ofWord (m i) })
            ctx.sender bal'.raw
          let ts' ← w.self.totalShares -? sharesIn
          Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
          safeTransfer w.self.asset ctx.sender assetsOut Error.TransferFailed
          Tx.emit (.Withdraw ctx.sender assetsOut sharesIn)
          pure assetsOut) ctx w := by
  rw [withdraw, run_load_bind, run_req_true hp, run_req_true hpos,
    run_sender_bind, run_loadMap_bind, run_req_true hbal, run_self_bind]
  refine (run_read_asset _).trans ?_
  rw [run_balanceOf_bind]
  simp only [run_load_bind, Tx.bind_assoc]

private theorem withdraw_head_some (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta) :
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (do
        let assetsOut ← Shares.toAssets offset sharesIn ta w.self.totalShares
        Tx.require (0 < assetsOut) Error.ZeroAssets
        let bal' ← w.self.shares ctx.sender -? sharesIn
        Tx.storeMap (fun σ i => (σ.shares i).raw)
          (fun σ m => { σ with shares := fun i => Amount.ofWord (m i) })
          ctx.sender bal'.raw
        let ts' ← w.self.totalShares -? sharesIn
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        safeTransfer w.self.asset ctx.sender assetsOut Error.TransferFailed
        Tx.emit (.Withdraw ctx.sender assetsOut sharesIn)
        pure assetsOut) ctx w := by
  rw [withdraw_head (ctx := ctx) sharesIn hp hpos hbal, hview]

/-- `withdraw` after a successful redeem, at the first `-?`. -/
private theorem withdraw_after_redeem (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ta.raw + 1 < wordBound)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hmul : (ta.raw + 1) * sharesIn.raw < wordBound)
    (hassets : 0 < redeemedAssets w.self.totalShares ta sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (do
        let bal' ← Tx.HSubChecked.hSub (w.self.shares ctx.sender) sharesIn
        Tx.storeMap (fun σ i => (σ.shares i).raw)
          (fun σ m => { σ with shares := fun i => Amount.ofWord (m i) })
          ctx.sender bal'.raw
        let ts' ← Tx.HSubChecked.hSub w.self.totalShares sharesIn
        Tx.store (fun σ m => { σ with totalShares := Amount.ofWord m }) ts'.raw
        safeTransfer w.self.asset ctx.sender
          ⟨redeemedAssets w.self.totalShares ta sharesIn⟩ Error.TransferFailed
        Tx.emit (.Withdraw ctx.sender
          ⟨redeemedAssets w.self.totalShares ta sharesIn⟩ sharesIn)
        pure (⟨redeemedAssets w.self.totalShares ta sharesIn⟩ :
          Amount vaultAsset)) ctx w := by
  have hposA :
      0 < (⟨redeemedAssets w.self.totalShares ta sharesIn⟩ :
        Amount vaultAsset) := by
    simpa [Amount.lt_iff] using hassets
  rw [withdraw_head_some sharesIn hp hpos hbal hview]
  conv =>
    lhs
    rw [run_toAssets_binds]
    rw [if_pos hA]
    rw [if_pos hV]
    rw [if_pos hmul]
  rw [run_req_true hposA]

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

private theorem previewDeposit_head (assets : Amount vaultAsset) :
    Tx.run (previewDeposit assets) ctx w =
      match viewBal? w.self.asset ctx.self w with
      | none => .error .callFailed
      | some ta =>
        Tx.run (Shares.toShares offset assets ta w.self.totalShares) ctx w := by
  rw [previewDeposit, run_self_bind]
  refine (run_read_asset _).trans ?_
  rw [run_balanceOf_bind]
  simp only [run_load_bind]

private theorem previewRedeem_head (sharesIn : Amount vShare) :
    Tx.run (previewRedeem sharesIn) ctx w =
      match viewBal? w.self.asset ctx.self w with
      | none => .error .callFailed
      | some ta =>
        Tx.run (Shares.toAssets offset sharesIn ta w.self.totalShares) ctx w := by
  rw [previewRedeem, run_self_bind]
  refine (run_read_asset _).trans ?_
  rw [run_balanceOf_bind]
  simp only [run_load_bind]

theorem previewDeposit_success_world {assets : Amount vaultAsset}
    {n : Amount vShare} {w' : World}
    (h : Tx.run (previewDeposit assets) ctx w = .ok (n, w')) :
    w' = w := by
  rw [previewDeposit_head] at h
  cases hview : viewBal? w.self.asset ctx.self w with
  | none => rw [hview] at h; cases h
  | some ta =>
    rw [hview] at h
    dsimp only at h
    rw [run_toShares_val] at h
    split_ifs at h; cases h
    rfl

theorem previewRedeem_success_world {sharesIn : Amount vShare}
    {n : Amount vaultAsset} {w' : World}
    (h : Tx.run (previewRedeem sharesIn) ctx w = .ok (n, w')) :
    w' = w := by
  rw [previewRedeem_head] at h
  cases hview : viewBal? w.self.asset ctx.self w with
  | none => rw [hview] at h; cases h
  | some ta =>
    rw [hview] at h
    dsimp only at h
    rw [run_toAssets_val] at h
    split_ifs at h; cases h
    rfl

/-! ### deposit

Peel with `deposit_head` + closed `run_*_bind` lemmas. Never `simp [deposit]`:
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

theorem deposit_reverts_on_view (assets : Amount vaultAsset)
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = none) :
    Tx.run (deposit assets) ctx w = .error .callFailed := by
  rw [deposit_head assets hp hpos, hview]

theorem deposit_reverts_on_addV (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : ¬ w.self.totalShares.raw + 1000000 < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_head_some assets hp hpos hview]
  conv => lhs; rw [run_toShares_binds]; rw [if_neg hV]

theorem deposit_reverts_on_addTa (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ¬ ta.raw + 1 < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_head_some assets hp hpos hview]
  conv => lhs; rw [run_toShares_binds]; rw [if_pos hV]; rw [if_neg hA]

theorem deposit_reverts_on_mul_overflow (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ta.raw + 1 < wordBound)
    (hmul : ¬ (w.self.totalShares.raw + 1000000) * assets.raw < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_head_some assets hp hpos hview]
  conv => lhs; rw [run_toShares_binds]; rw [if_pos hV]; rw [if_pos hA]; rw [if_neg hmul]

theorem deposit_reverts_on_zero_shares (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ta.raw + 1 < wordBound)
    (hmul : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound)
    (hminted : ¬ 0 < mintedShares w.self.totalShares ta assets) :
    Tx.run (deposit assets) ctx w = .error (.user .ZeroShares) := by
  rw [deposit_head_some assets hp hpos hview]
  conv => lhs; rw [run_toShares_binds]; rw [if_pos hV]; rw [if_pos hA]; rw [if_pos hmul]
  apply run_req_false
  simpa [Amount.lt_iff] using hminted

theorem deposit_reverts_on_add_shares (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ta.raw + 1 < wordBound)
    (hmul : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self.totalShares ta assets)
    (haddS : ¬ w.self.totalShares.raw +
      mintedShares w.self.totalShares ta assets < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_after_mint assets hp hpos hview hV hA hmul hminted]
  conv => lhs; rw [run_hAdd_bind]; rw [if_neg haddS]

theorem deposit_reverts_on_add_bal (assets : Amount vaultAsset)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < assets)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hA : ta.raw + 1 < wordBound)
    (hmul : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound)
    (hminted : 0 < mintedShares w.self.totalShares ta assets)
    (haddS : w.self.totalShares.raw +
      mintedShares w.self.totalShares ta assets < wordBound)
    (haddB : ¬ (w.self.shares ctx.sender).raw +
      mintedShares w.self.totalShares ta assets < wordBound) :
    Tx.run (deposit assets) ctx w = .error (.arith .overflow) := by
  rw [deposit_after_mint assets hp hpos hview hV hA hmul hminted]
  conv => lhs; rw [run_hAdd_bind]; rw [if_pos haddS]
  rw [run_store_bind, Tx.hAdd_bind_left, Tx.bind_assoc, run_loadMap_bind]
  conv => lhs; rw [run_hAdd_bind]; rw [if_neg haddB]

structure DepositOk (ctx : Ctx) (w : World)
    (assets : Amount vaultAsset) where
  ta : Amount vaultAsset
  paused : w.self.paused = Flag.off
  pos : 0 < assets
  viewOk : viewBal? w.self.asset ctx.self w = some ta
  addV : w.self.totalShares.raw + 1000000 < wordBound
  addTa : ta.raw + 1 < wordBound
  prod : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound
  mintedPos : 0 < mintedShares w.self.totalShares ta assets
  addShares : w.self.totalShares.raw +
    mintedShares w.self.totalShares ta assets < wordBound
  addBal : (w.self.shares ctx.sender).raw +
    mintedShares w.self.totalShares ta assets < wordBound

def depositTailWorld (w : World) (who : Address)
    (minted : Nat) : World :=
  { w with self := depositPost w.self who minted }

def withdrawTailWorld (w : World) (who : Address)
    (sharesIn : Amount vShare) : World :=
  { w with self := withdrawPost w.self who sharesIn }

/-- Reduce a well-formed `deposit` to the token pull + emit on post-storage. -/
theorem deposit_to_tail (assets : Amount vaultAsset) (h : DepositOk ctx w assets) :
    Tx.run (deposit assets) ctx w =
      Tx.run (
        safeTransferFrom (E := Event) w.self.asset ctx.sender ctx.self assets
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.Deposit ctx.sender assets
          (Amount.ofWord (mintedShares w.self.totalShares h.ta assets))) >>=
          fun _ =>
        (pure (Amount.ofWord (mintedShares w.self.totalShares h.ta assets)) :
          Tx Storage ExtState Event Error (Amount vShare)))
        ctx (depositTailWorld w ctx.sender
          (mintedShares w.self.totalShares h.ta assets)) := by
  rcases h with ⟨ta, hp, hpos, hview, hV, hA, hmul, hminted, haddS, haddB⟩
  rw [deposit_after_mint assets hp hpos hview hV hA hmul hminted]
  conv => lhs; rw [run_hAdd_bind]; rw [if_pos haddS]
  rw [run_store_ts, Tx.hAdd_bind_left, Tx.bind_assoc, run_loadMap_bind]
  conv => lhs; rw [run_hAdd_bind]; rw [if_pos haddB]
  rw [run_storeMap_shares]
  dsimp [depositTailWorld]
  rw [depositPost_of_stores]
  rfl

def deposit_ok_of_run {assets : Amount vaultAsset} {n : Amount vShare}
    {w' : World}
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    DepositOk ctx w assets := by
  have hp : w.self.paused = Flag.off := by
    by_contra h; exact Tx.run_ok_error hrun (deposit_reverts_when_paused assets h)
  have hpos : 0 < assets := by
    by_contra h; exact Tx.run_ok_error hrun (deposit_reverts_on_nonpos assets hp h)
  cases hview : viewBal? w.self.asset ctx.self w with
  | none =>
    exact (Tx.run_ok_error hrun (deposit_reverts_on_view assets hp hpos hview)).elim
  | some ta =>
    have hV : w.self.totalShares.raw + 1000000 < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun (deposit_reverts_on_addV assets hp hpos hview h)
    have hA : ta.raw + 1 < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun (deposit_reverts_on_addTa assets hp hpos hview hV h)
    have hmul : (w.self.totalShares.raw + 1000000) * assets.raw < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (deposit_reverts_on_mul_overflow assets hp hpos hview hV hA h)
    have hminted : 0 < mintedShares w.self.totalShares ta assets := by
      by_contra h
      exact Tx.run_ok_error hrun
        (deposit_reverts_on_zero_shares assets hp hpos hview hV hA hmul h)
    have haddS : w.self.totalShares.raw +
        mintedShares w.self.totalShares ta assets < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (deposit_reverts_on_add_shares assets hp hpos hview hV hA hmul hminted h)
    have haddB : (w.self.shares ctx.sender).raw +
        mintedShares w.self.totalShares ta assets < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (deposit_reverts_on_add_bal assets hp hpos hview hV hA hmul hminted haddS h)
    exact ⟨ta, hp, hpos, hview, hV, hA, hmul, hminted, haddS, haddB⟩

/-- Exact storage / log / oracle of a successful `deposit`. -/
theorem deposit_post (assets : Amount vaultAsset) {n : Amount vShare}
    {w' : World}
    (h : DepositOk ctx w assets)
    (hrun : Tx.run (deposit assets) ctx w = .ok (n, w')) :
    n = Amount.ofWord (mintedShares w.self.totalShares (h.ta) assets) ∧
      w'.self = depositPost w.self ctx.sender
        (mintedShares w.self.totalShares (h.ta) assets) ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Deposit ctx.sender assets
        (Amount.ofWord (mintedShares w.self.totalShares (h.ta) assets))] := by
  have heq := deposit_to_tail assets h
  rw [heq] at hrun
  rw [run_safeTF_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    rcases transferFrom_frame
        (w := depositTailWorld w ctx.sender
          (mintedShares w.self.totalShares h.ta assets))
        (by simpa [tfCall, depositTailWorld] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · rw [run_emit_pure] at hrun
      simp [hself1, hor1, hlog1] at hrun
      obtain ⟨hn, rfl⟩ := hrun
      exact ⟨Amount.ext hn.symm, rfl, rfl, rfl⟩

/-- The successful `deposit` CALL, for applying `IERC20.Spec`. -/
theorem deposit_call (assets : Amount vaultAsset) {n : Amount vShare}
    {w' : World}
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
      (σ := depositPost w.self ctx.sender
        (mintedShares w.self.totalShares (h.ta) assets))
      (by simpa [tfCall, depositTailWorld] using hcall)
    cases b
    · simp at hrun
    · refine ⟨{ w with ext := w1.ext }, htf.1, rfl, rfl, rfl, ?_, hor⟩
      rw [run_emit_pure] at hrun
      simp [htf.2.1, htf.2.2.1, htf.2.2.2] at hrun
      obtain ⟨_, rfl⟩ := hrun
      rfl

/-! ### withdraw

Peel with `withdraw_head` + closed `run_*_bind` lemmas. Never `simp [withdraw]`.
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

theorem withdraw_reverts_on_view (sharesIn : Amount vShare)
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = none) :
    Tx.run (withdraw sharesIn) ctx w = .error .callFailed := by
  rw [withdraw_head sharesIn hp hpos hbal, hview]

theorem withdraw_reverts_on_addTa (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ¬ ta.raw + 1 < wordBound) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .overflow) := by
  rw [withdraw_head_some sharesIn hp hpos hbal hview]
  conv => lhs; rw [run_toAssets_binds]; rw [if_neg hA]

theorem withdraw_reverts_on_addV (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ta.raw + 1 < wordBound)
    (hV : ¬ w.self.totalShares.raw + 1000000 < wordBound) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .overflow) := by
  rw [withdraw_head_some sharesIn hp hpos hbal hview]
  conv => lhs; rw [run_toAssets_binds]; rw [if_pos hA]; rw [if_neg hV]

theorem withdraw_reverts_on_mul_overflow (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ta.raw + 1 < wordBound)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hmul : ¬ (ta.raw + 1) * sharesIn.raw < wordBound) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .overflow) := by
  rw [withdraw_head_some sharesIn hp hpos hbal hview]
  conv => lhs; rw [run_toAssets_binds]; rw [if_pos hA]; rw [if_pos hV]; rw [if_neg hmul]

theorem withdraw_reverts_on_zero_assets (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ta.raw + 1 < wordBound)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hmul : (ta.raw + 1) * sharesIn.raw < wordBound)
    (hzero : ¬ 0 < redeemedAssets w.self.totalShares ta sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.user .ZeroAssets) := by
  rw [withdraw_head_some sharesIn hp hpos hbal hview]
  conv => lhs; rw [run_toAssets_binds]; rw [if_pos hA]; rw [if_pos hV]; rw [if_pos hmul]
  apply run_req_false
  simpa [Amount.lt_iff] using hzero

structure WithdrawOk (ctx : Ctx) (w : World)
    (sharesIn : Amount vShare) where
  ta : Amount vaultAsset
  paused : w.self.paused = Flag.off
  pos : 0 < sharesIn
  bal : sharesIn ≤ w.self.shares ctx.sender
  viewOk : viewBal? w.self.asset ctx.self w = some ta
  supply : sharesIn ≤ w.self.totalShares
  addTa : ta.raw + 1 < wordBound
  addV : w.self.totalShares.raw + 1000000 < wordBound
  prod : (ta.raw + 1) * sharesIn.raw < wordBound
  assetsPos : 0 < redeemedAssets w.self.totalShares ta sharesIn

theorem withdraw_reverts_on_insufficient_supply (sharesIn : Amount vShare)
    {ta : Amount vaultAsset}
    (hp : w.self.paused = Flag.off) (hpos : 0 < sharesIn)
    (hbal : sharesIn ≤ w.self.shares ctx.sender)
    (hview : viewBal? w.self.asset ctx.self w = some ta)
    (hA : ta.raw + 1 < wordBound)
    (hV : w.self.totalShares.raw + 1000000 < wordBound)
    (hmul : (ta.raw + 1) * sharesIn.raw < wordBound)
    (hassets : 0 < redeemedAssets w.self.totalShares ta sharesIn)
    (hsup : w.self.totalShares < sharesIn) :
    Tx.run (withdraw sharesIn) ctx w = .error (.arith .underflow) := by
  rw [withdraw_after_redeem sharesIn hp hpos hbal hview hA hV hmul hassets]
  conv => lhs; rw [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hbal), run_storeMap_bind]
  conv => lhs; rw [run_hSub_bind]
  rw [if_neg (Nat.not_le_of_gt ((Amount.lt_iff _ _).mp hsup))]

theorem withdraw_to_tail (sharesIn : Amount vShare) (h : WithdrawOk ctx w sharesIn) :
    Tx.run (withdraw sharesIn) ctx w =
      Tx.run (
        safeTransfer (E := Event) w.self.asset ctx.sender
          (Amount.ofWord (redeemedAssets w.self.totalShares h.ta sharesIn))
          Error.TransferFailed >>= fun _ =>
        Tx.emit (.Withdraw ctx.sender
          (Amount.ofWord (redeemedAssets w.self.totalShares h.ta sharesIn))
          sharesIn) >>= fun _ =>
        (pure (Amount.ofWord (redeemedAssets w.self.totalShares h.ta sharesIn)) :
          Tx Storage ExtState Event Error (Amount vaultAsset)))
        ctx (withdrawTailWorld w ctx.sender sharesIn) := by
  rcases h with ⟨ta, hp, hpos, hbal, hview, hsup, hA, hV, hmul, hassets⟩
  rw [withdraw_after_redeem sharesIn hp hpos hbal hview hA hV hmul hassets]
  conv => lhs; rw [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hbal), run_storeMap_shares]
  conv => lhs; rw [run_hSub_bind]
  rw [if_pos (Amount.le_iff _ _ |>.mp hsup), run_store_ts]
  dsimp [withdrawTailWorld]
  rw [withdrawPost_of_stores]
  rfl

def withdraw_ok_of_run {sharesIn : Amount vShare} {n : Amount vaultAsset}
    {w' : World}
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
  cases hview : viewBal? w.self.asset ctx.self w with
  | none =>
    exact (Tx.run_ok_error hrun
      (withdraw_reverts_on_view sharesIn hp hpos hbal hview)).elim
  | some ta =>
    have hA : ta.raw + 1 < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (withdraw_reverts_on_addTa sharesIn hp hpos hbal hview h)
    have hV : w.self.totalShares.raw + 1000000 < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (withdraw_reverts_on_addV sharesIn hp hpos hbal hview hA h)
    have hmul : (ta.raw + 1) * sharesIn.raw < wordBound := by
      by_contra h
      exact Tx.run_ok_error hrun
        (withdraw_reverts_on_mul_overflow sharesIn hp hpos hbal hview hA hV h)
    have hassets : 0 < redeemedAssets w.self.totalShares ta sharesIn := by
      by_contra h
      exact Tx.run_ok_error hrun
        (withdraw_reverts_on_zero_assets sharesIn hp hpos hbal hview hA hV hmul h)
    have hsup : sharesIn ≤ w.self.totalShares := by
      by_contra h
      exact Tx.run_ok_error hrun (withdraw_reverts_on_insufficient_supply sharesIn
        hp hpos hbal hview hA hV hmul hassets
          ((Amount.lt_iff w.self.totalShares sharesIn).mpr
            (Nat.not_le.mp (mt (Amount.le_iff sharesIn _).mpr h))))
    exact ⟨ta, hp, hpos, hbal, hview, hsup, hA, hV, hmul, hassets⟩

theorem withdraw_post (sharesIn : Amount vShare) {n : Amount vaultAsset}
    {w' : World}
    (h : WithdrawOk ctx w sharesIn)
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    n = Amount.ofWord (redeemedAssets w.self.totalShares (h.ta) sharesIn) ∧
      w'.self = withdrawPost w.self ctx.sender sharesIn ∧
      w'.oracle = w.oracle ∧
      w'.log = w.log ++ [.Withdraw ctx.sender
        (Amount.ofWord (redeemedAssets w.self.totalShares (h.ta) sharesIn))
        sharesIn] := by
  have heq := withdraw_to_tail sharesIn h
  rw [heq] at hrun
  rw [run_safeTR_bind] at hrun
  split at hrun
  · cases hrun
  · next b w1 hcall =>
    set σP := withdrawPost w.self ctx.sender sharesIn
    rcases transfer_frame (w := { w with self := σP })
        (by simpa [trCall, withdrawTailWorld] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · rw [run_emit_pure] at hrun
      simp [hself1, hor1, hlog1] at hrun
      obtain ⟨hn, rfl⟩ := hrun
      exact ⟨Amount.ext hn.symm, rfl, rfl, rfl⟩

theorem withdraw_call (sharesIn : Amount vShare) {n : Amount vaultAsset}
    {w' : World}
    (h : WithdrawOk ctx w sharesIn)
    (hrun : Tx.run (withdraw sharesIn) ctx w = .ok (n, w')) :
    let amt := Amount.ofWord (redeemedAssets w.self.totalShares (h.ta) sharesIn)
    let σ' := withdrawPost w.self ctx.sender sharesIn
    ∃ w1, Tx.run (trCall w.self.asset ctx.sender amt) ctx
        (withdrawTailWorld w ctx.sender sharesIn) =
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
    set σP := withdrawPost w.self ctx.sender sharesIn
    rcases transfer_frame (w := { w with self := σP })
        (by simpa [trCall, withdrawTailWorld] using hcall) with ⟨hself1, hor1, hlog1⟩
    cases b
    · simp at hrun
    · refine ⟨w1, by simpa [trCall, withdrawTailWorld] using hcall, hself1, hor1, ?_, hor, hσ⟩
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
    {w' : World}
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender + minted ∧
      w'.self.totalShares = w.self.totalShares + minted := by
  have hok := deposit_ok_of_run h
  have ⟨hn, hσ, _, _⟩ := deposit_post assets hok h
  subst hn
  simp [hσ, depositPost, Amount.raw_add, Amount.raw_ofWord]

theorem deposit_holdings_of_spec {assets : Amount vaultAsset}
    {minted : Amount vShare} {w' : World}
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    holdingsAt ctx.self w' = holdingsAt ctx.self w + assets := by
  have hok := deposit_ok_of_run h
  have ⟨w1, htf, hself1, hor1, _, hext, hor⟩ := deposit_call assets hok h
  have ⟨_, hσ, _, _⟩ := deposit_post assets hok h
  have hmoves := hT.transferFrom_moves (ctx := ctx) (w := w.view) (w' := w1.view)
    (by
      have hopt := Tx.run_ok_toOption htf
      have := congrArg (Option.map (Prod.map id World.view)) hopt
      simpa [impl_transferFrom] using this)
  have hdst := hmoves.2.1 hne
  have hbal : holdingsAt ctx.self w1 = holdingsAt ctx.self w + assets := by
    simpa [holdingsAt, IERC20.Ref.impl, hself1, hor1, World.view] using hdst
  have heqH : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, depositPost, hself1])
      (hor.trans hor1.symm) hext
  apply Amount.ext
  have hraw := congrArg Amount.raw hbal
  rw [Amount.raw_add] at hraw
  simpa [holdings] using heqH.trans hraw

theorem withdraw_shares {sharesIn : Amount vShare} {paid : Amount vaultAsset}
    {w' : World}
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender - sharesIn ∧
      w'.self.totalShares = w.self.totalShares - sharesIn := by
  have hok := withdraw_ok_of_run h
  have ⟨hn, hσ, _, _⟩ := withdraw_post sharesIn hok h
  subst hn
  simp [hσ, withdrawPost, Amount.raw_sub, Amount.raw_ofWord]

theorem withdraw_holdings_of_spec {sharesIn : Amount vShare}
    {paid : Amount vaultAsset} {w' : World}
    (hT : IERC20.Spec (w.self.asset.impl : AssetImpl))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    holdingsAt ctx.self w' + paid = holdingsAt ctx.self w := by
  have hok := withdraw_ok_of_run h
  have ⟨hn, hσ, hor, _⟩ := withdraw_post sharesIn hok h
  obtain ⟨w1, htr, hself1, hor1, hext, _, _⟩ := withdraw_call sharesIn hok h
  subst hn
  set σ' := withdrawPost w.self ctx.sender sharesIn
  set amt := Amount.ofWord (redeemedAssets w.self.totalShares hok.ta sharesIn)
  let wCall : World :=
    withdrawTailWorld w ctx.sender sharesIn
  have hTcall : IERC20.Spec (wCall.self.asset.impl : AssetImpl) := by
    dsimp [wCall, withdrawTailWorld, withdrawPost]
    simpa [IERC20.Ref.impl] using hT
  have hrunT :
      wCall.self.asset.impl.transfer
        ctx.sender amt { ctx with sender := ctx.self } wCall.view =
        some (true, w1.view) := by
    dsimp [wCall, withdrawTailWorld, withdrawPost]
    have htr' :
        Tx.run (trCall w.self.asset ctx.sender amt)
          { ctx with sender := ctx.self } wCall = .ok (true, w1) := by
      rw [← transfer_run_ctx_irrel (r := w.self.asset) (dst := ctx.sender)
          (amt := amt) (ctx' := { ctx with sender := ctx.self }) (w₀ := wCall)]
      simpa [wCall, amt, withdrawTailWorld] using htr
    dsimp [wCall, withdrawTailWorld, withdrawPost] at htr' ⊢
    have hopt := Tx.run_ok_toOption htr'
    have := congrArg (Option.map (Prod.map id World.view)) hopt
    simpa [impl_transfer, amt] using this
  have hmoves := hTcall.transfer_moves hrunT
  have hto := hmoves.2.1 hne.symm
  have hsumr := congrArg Amount.raw hmoves.1
  rw [Amount.raw_add, Amount.raw_add] at hsumr
  simp at hsumr
  have htor := congrArg Amount.raw hto
  simp [Amount.raw_add] at htor
  have heq1 : holdings ctx.self w' = holdings ctx.self w1 :=
    holdings_congr ctx.self (by simp [hσ, σ', hself1, withdrawPost])
      (hor.trans hor1.symm) hext
  have heq0 : holdings ctx.self wCall = holdings ctx.self w :=
    holdings_congr ctx.self
      (by simp [wCall, withdrawTailWorld, withdrawPost]) rfl rfl
  have hs : w1.self = wCall.self := by
    simp [hself1, wCall, withdrawTailWorld, σ', withdrawPost]
  apply Amount.ext
  change holdings ctx.self w' + amt.raw = holdings ctx.self w
  rw [heq1, ← heq0]
  clear heq1 heq0
  simp [holdings, holdingsAt, hs, wCall, withdrawTailWorld, withdrawPost]
    at hsumr htor ⊢
  rw [htor] at hsumr
  rw [Nat.add_assoc, Nat.add_comm amt.raw] at hsumr
  exact Nat.add_left_cancel hsumr

theorem deposit_inflation_bounded {assets : Amount vaultAsset}
    {minted : Amount vShare} {w' : World}
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    let V := Shares.virtualShares (s := vShare) offset
    let A := holdingsAt ctx.self w
    let S := w.self.totalShares
    let r := Shares.toAssetsRaw offset minted.raw (A.raw + assets.raw)
      (S.raw + minted.raw)
    V.raw * (assets.raw - r) ≤ A.raw + V.raw := by
  have hok := deposit_ok_of_run h
  have ⟨hn, _, _, _⟩ := deposit_post assets hok h
  have hTA : (holdingsAt ctx.self w).raw = hok.ta.raw :=
    viewBal?_some_holdings ctx.self hok.viewOk
  subst hn
  simp [hTA, mintedShares, Amount.raw_ofWord, Shares.virtualShares,
    Shares.virtualShares_raw]
  exact Shares.inflation_bound_raw offset assets.raw hok.ta.raw
    w.self.totalShares.raw

end Proof

end Vault
