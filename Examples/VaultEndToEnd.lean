import Lsc.Compiler.TransportTheorems
import Examples.VaultCompileTheorems
import Examples.VaultSecurity
import Examples.VaultSecurityTheorems
import Lsc.Lang.CoreTheorems
import YulEvmCompiler.Compile
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Bytecode-level Vault theorems via `Transport`. Main theorems are universal over
arbitrary halted calldata (`EvmTraceRunExtAll`); `_exists` encodes a Security
trace (`callsOf`, env dropped). Trace-predicted-calldata forms are dropped.
`w'` is the fo-adjusted fold (not necessarily `Security.run tr w`).
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Vault
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

lsc_codec Vault

namespace Vault

def vaultClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  let ta := (σ (BitVec.ofNat 256 0)).toNat
  let ts := (σ (BitVec.ofNat 256 1)).toNat
  let sh := (σ (mapSlot1 κ 2 a)).toNat
  if ts = 0 then 0 else sh * ta / ts

theorem vault_field_totalAssets :
    Vault.contract.fields[0]? =
      some { name := "totalAssets", kind := .scalar, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_field_totalShares :
    Vault.contract.fields[1]? =
      some { name := "totalShares", kind := .scalar, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_field_shares :
    Vault.contract.fields[2]? =
      some { name := "shares", kind := .map1, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_schema_totalAssets (s : Storage) :
    Vault.schema.st.scalar 0 s = s.totalAssets := rfl

theorem vault_schema_totalShares (s : Storage) :
    Vault.schema.st.scalar 1 s = s.totalShares := rfl

theorem vault_schema_shares (s : Storage) (k : Address) :
    Vault.schema.st.map1 2 s k = s.shares k := rfl

theorem vault_claim_of_rel (s : Storage) (σ : U256 → U256) (a : Address)
    (hs : storageRel Vault.contract Vault.schema evmKeccak s σ)
    (ha : Nat.lt a wordBound)
    (hta : s.totalAssets < wordBound) (hts : s.totalShares < wordBound)
    (hsh : s.shares a < wordBound) :
    vaultClaimRead evmKeccak σ a = claim a s := by
  have h0 := storageRel_scalar_toNat hs vault_field_totalAssets rfl
    (by rw [vault_schema_totalAssets]) hta
  have h1 := storageRel_scalar_toNat hs vault_field_totalShares rfl
    (by rw [vault_schema_totalShares]) hts
  have h2 := storageRel_map1_toNat hs vault_field_shares rfl
    (by rw [vault_schema_shares]) ha hsh
  simp [vaultClaimRead, claim, h0, h1, h2]

theorem vault_wf_scalar (w : World Storage Ext Event) (i : Nat) (fd : FieldDef)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hfd : Vault.contract.fields[i]? = some fd) (hk : fd.kind = .scalar) :
    Vault.schema.st.scalar i w.self < wordBound := by
  have h := hwf i fd hfd
  simpa [hk] using h

theorem vault_ta_bound (w : World Storage Ext Event)
    (hwf : WorldWF Vault.contract Vault.schema w) :
    w.self.totalAssets < wordBound := by
  simpa [vault_schema_totalAssets] using
    vault_wf_scalar w 0 _ hwf vault_field_totalAssets rfl

theorem vault_ts_bound (w : World Storage Ext Event)
    (hwf : WorldWF Vault.contract Vault.schema w) :
    w.self.totalShares < wordBound := by
  simpa [vault_schema_totalShares] using
    vault_wf_scalar w 1 _ hwf vault_field_totalShares rfl

theorem vault_shares_bound (w : World Storage Ext Event) (a : Address)
    (hwf : WorldWF Vault.contract Vault.schema w) (ha : Nat.lt a wordBound) :
    w.self.shares a < wordBound := by
  have h := hwf 2 _ vault_field_shares
  simpa [vault_schema_shares] using h a ha

@[reducible] def mkVaultSetup (hκ : KeccakSep Vault.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is) :
    TransportSetup Storage Ext Event Error where
  c := Vault.contract
  Γ := Vault.schema
  spec := Vault.spec
  codec := Vault.codec
  lawful := Vault.schema_lawful
  hκ := hκ
  hctor := fun f hf => vault_fn_not_ctor hf
  hlen := vault_fields_lt
  hbound := fun f hf => vault_fn_params_bound hf
  rt := rt
  hrt := hrt
  is := is
  hcomp := hcomp

theorem vault_inv_faults (self : Address) (w : World Storage Ext Event) (fo : Nat → Bool)
    (h : Inv self w) : Inv self { w with faults := fo } := h

theorem vault_inv_log (self : Address) (w : World Storage Ext Event) (log' : List Event)
    (h : Inv self w) : Inv self { w with log := log' } := h

theorem vault_auth_storage (a : Address) (c : Call spec) (s s' : Storage) :
    Auth a c s = Auth a c s' := rfl

theorem vault_inv_clear (self : Address) (w : World Storage Ext Event)
    (fo : Nat → Bool) (h : Inv self w) :
    Inv self { w with log := [], faults := fo } :=
  vault_inv_faults self { w with log := [] } fo (vault_inv_log self w [] h)

theorem noAuthAlong_irrel (a : Address) :
    ∀ (tr : List (Step spec)) (w w' : World Storage Ext Event),
      NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w' := by
  intro tr
  induction tr with
  | nil => intro w w'; simp [NoAuthAlong]
  | cons s rest ih =>
    intro w w'
    cases s with
    | env x' =>
      simpa [NoAuthAlong] using ih (w := { w with ext := x' }) (w' := { w' with ext := x' })
    | call c =>
      simp [NoAuthAlong]
      exact and_congr
        (iff_of_eq (congrArg Not (vault_auth_storage a c w.self w'.self)))
        (ih (step (.call c) w) (step (.call c) w'))

def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (Vault.assetB.addr w'.self) ext α

/-- Holdings of `self` according to `α` at the token address, from bytecode `σ`/`ξ`. -/
def vaultHoldingsRead (α : Abs IERC20.Ghost) (σ : U256 → U256) (ξ : Foreign)
    (self assetAddr : Address) : Nat :=
  (α.ofState (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self))
    assetAddr).balances self

/-- Storage-level solvency: finite support of `vaultClaimRead` on addresses below
`wordBound`, and that support's sum is ≤ holdings read through `α` from `ξ`.
Addresses `≥ wordBound` are outside `storageRel`. Trailing `env` steps may raise
Spec holdings while `ξ'` stays at the last EVM call; this statement tracks `ξ'`. -/
def vaultSolventRead (α : Abs IERC20.Ghost) (σ : U256 → U256) (ξ : Foreign)
    (self assetAddr : Address) : Prop :=
  ∃ H : Finset Address,
    (∀ a, Nat.lt a wordBound → a ∉ H → vaultClaimRead evmKeccak σ a = 0) ∧
    H.sum (vaultClaimRead evmKeccak σ) ≤ vaultHoldingsRead α σ ξ self assetAddr

theorem vaultSolventRead_of_inv (α : Abs IERC20.Ghost)
    (self : Address) (w : World Storage Ext Event) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self))) :
    vaultSolventRead α σ ξ self (Vault.assetB.addr w.self) := by
  obtain ⟨H, h0, hsum⟩ := inv_solvent self w hw
  let pred : Address → Prop := fun a => Nat.lt (a : Nat) wordBound
  let inst : DecidablePred pred := fun a => Nat.decLt (a : Nat) wordBound
  let H' : Finset Address := @Finset.filter Address pred inst H
  refine ⟨H', ?_, ?_⟩
  · intro a ha hnin
    have hninH : a ∉ H := by
      intro hin
      have : a ∈ H' := (@Finset.mem_filter Address pred inst H a).mpr ⟨hin, ha⟩
      exact hnin this
    have hcl := vault_claim_of_rel w.self σ a hs ha
      (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
    simpa [hcl] using h0 a hninH
  · have hhold :
        vaultHoldingsRead α σ ξ self (Vault.assetB.addr w.self) = holdings self w := by
      simpa [vaultHoldingsRead, holdings, RX, Vault.assetB] using
        congrArg (fun g : IERC20.Ghost => g.balances self) hRX
    have hsum' :
        H'.sum (vaultClaimRead evmKeccak σ) = H'.sum (fun a => claim a w.self) := by
      apply Finset.sum_congr rfl
      intro a ha'
      have hlt : Nat.lt (a : Nat) wordBound :=
        ((@Finset.mem_filter Address pred inst H a).mp ha').2
      exact vault_claim_of_rel w.self σ a hs hlt
        (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf hlt)
    have hsub : H' ⊆ H := @Finset.filter_subset Address pred inst H
    have hle :
        H'.sum (fun a => claim a w.self) ≤ H.sum (fun a => claim a w.self) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    simpa [hhold, hsum'] using Nat.le_trans hle hsum

private theorem vault_scalarUpd_asset (i : Nat) (σ : Storage) (v : Nat)
    (h : 5 ≠ i) : (Vault.schema.st.scalarUpd i σ v).asset = σ.asset := by
  cases i with
  | zero => simp [Vault.schema]
  | succ i =>
    cases i with
    | zero => simp [Vault.schema]
    | succ i =>
      cases i with
      | zero => simp [Vault.schema]
      | succ i =>
        cases i with
        | zero => simp [Vault.schema]
        | succ i =>
          cases i with
          | zero => simp [Vault.schema]
          | succ i =>
            cases i with
            | zero => cases h rfl
            | succ i =>
              cases i with
              | zero => simp [Vault.schema]
              | succ _ => simp [Vault.schema]

private theorem vault_map1Upd_asset (i : Nat) (σ : Storage) (m : Nat → Nat) :
    (Vault.schema.st.map1Upd i σ m).asset = σ.asset := by
  cases i with
  | zero => simp [Vault.schema]
  | succ i =>
    cases i with
    | zero => simp [Vault.schema]
    | succ i =>
      cases i with
      | zero => simp [Vault.schema]
      | succ i =>
        cases i with
        | zero => simp [Vault.schema]
        | succ i =>
          cases i with
          | zero => simp [Vault.schema]
          | succ i =>
            cases i with
            | zero => simp [Vault.schema]
            | succ i =>
              cases i with
              | zero => simp [Vault.schema]
              | succ _ => simp [Vault.schema]

private theorem vault_map2Upd_asset (i : Nat) (σ : Storage) (m : Nat → Nat → Nat) :
    (Vault.schema.st.map2Upd i σ m).asset = σ.asset := by
  cases i with
  | zero => simp [Vault.schema]
  | succ i =>
    cases i with
    | zero => simp [Vault.schema]
    | succ i =>
      cases i with
      | zero => simp [Vault.schema]
      | succ i =>
        cases i with
        | zero => simp [Vault.schema]
        | succ i =>
          cases i with
          | zero => simp [Vault.schema]
          | succ i =>
            cases i with
            | zero => simp [Vault.schema]
            | succ i =>
              cases i with
              | zero => simp [Vault.schema]
              | succ _ => simp [Vault.schema]

private theorem vault_ext_call_self
    {b m : Nat} {args : List Nat} {ctx : Ctx}
    {w : World Storage Ext Event} {v : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (Vault.schema.ext.call b m args) ctx w = .ok (v, w')) :
    w'.self = w.self := by
  simp [Vault.schema] at h
  split at h
  · split at h
    · exact Tx.call_self (E := Event) (ε := Error) Vault.assetB _ args h
    · simp [Tx.run] at h
  · simp [Tx.run] at h

theorem vault_asset_stable_core (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    (worldAfter (Core.denote Vault.schema (Vault.fnDef fn).core
      (Vault.encode fn args).reverse) ctx w).self.asset = w.self.asset := by
  cases htx : Tx.run (Core.denote Vault.schema (Vault.fnDef fn).core
      (Vault.encode fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.asset)
      (Vault.fnDef fn).core (Vault.encode fn args).reverse 5
      (fun i σ v hne => vault_scalarUpd_asset i σ v hne)
      (fun i σ m _hne => vault_map1Upd_asset i σ m)
      (fun i σ m _hne => vault_map2Upd_asset i σ m)
      (fun b m args ctx w v w' hok => vault_ext_call_self hok)
      (coreAvoids_not_write (vault_fn_avoids (Vault.fnDef_mem fn))) htx

@[reducible] def vaultEnv (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, Vault.assetB⟩

@[reducible] def mkVaultBindings
    (hκ : KeccakSep Vault.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign) :
    TransportBindings Storage Ext Event Error IERC20
      (mkVaultSetup hκ rt hrt is hcomp) where
  bs := [vaultEnv α]
  extCalls := ext
  hCalls := hCalls
  htot := htot
  hS2 := fun f hf => vault_fn_s2 hf
  hign := BindEnvs.ignoresLocal_singleton (vaultEnv α) hign
  hF := BindEnvs.ofState_foreign_singleton (vaultEnv α) hF
  hsame := BindEnvs.sameAbs_singleton (vaultEnv α)
  horth := BindEnvs.orthogonal_singleton (vaultEnv α)
  hBind := BindEnvs.lookupWF_singleton (α := α) (bind := Vault.assetB) vault_bindWF
  hslot := fun f hf => BindEnvs.avoids_singleton (vault_hslot hf)
  bindAddr_stable := fun e he fn args ctx w => by
    have : e = vaultEnv α := List.mem_singleton.mp he
    subst this
    simp [vaultEnv, Vault.assetB]
    rw [← Vault.codec.core_exec fn args ctx w]
    exact vault_asset_stable_core fn args ctx w

theorem vault_RXs_of (α : Abs IERC20.Ghost) (w : World Storage Ext Event) (st : EvmState)
    (h : RX α Vault.assetB w st) : RXs [vaultEnv α] w st :=
  (RXs_singleton (vaultEnv α) w st).mpr h

theorem vault_RX_of (α : Abs IERC20.Ghost) (w : World Storage Ext Event) (st : EvmState)
    (h : RXs [vaultEnv α] w st) : RX α Vault.assetB w st :=
  (RXs_singleton (vaultEnv α) w st).mp h

theorem vault_neSelf_of (α : Abs IERC20.Ghost) (self : Address) (σ : Storage)
    (h : accountKey (BitVec.ofNat 256 (Vault.assetB.addr σ)) ≠
          accountKey (BitVec.ofNat 256 self)) :
    BindEnvs.neSelf [vaultEnv α] self σ :=
  BindEnvs.neSelf_singleton (vaultEnv α) self σ h

theorem vault_confs_of (α : Abs IERC20.Ghost) (self : Address) (ext : ExternalCalls)
    (h : ConfFun self ext α) (w' : World Storage Ext Event) :
    BindEnvs.conforms [vaultEnv α] self w'.self ext :=
  BindEnvs.conforms_singleton (vaultEnv α) self w'.self ext (h w')

theorem vault_inj_of (α : Abs IERC20.Ghost) (σ : Storage) :
    BindEnvs.addrInj [vaultEnv α] σ :=
  BindEnvs.addrInj_singleton (vaultEnv α) σ

theorem vault_noAuthAlong_callsOf (a : Address) (tr : List (Step spec))
    (w : World Storage Ext Event) (h : NoAuthAlong Auth a tr w) :
    NoAuthAlong Auth a (callsOf tr) w := by
  induction tr generalizing w with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env x' =>
      simpa [callsOf] using
        (noAuthAlong_irrel a (callsOf rest) { w with ext := x' } w).mp
          (ih (w := { w with ext := x' }) (by simpa [NoAuthAlong] using h))
    | .call c =>
      rcases h with ⟨hAc, hAtl⟩
      exact ⟨hAc, ih (w := step (.call c) w) hAtl⟩

/-- Solidity ERC20 layout: `balances[o]` at `keccak(abi(o) ‖ abi(0))`, `decimals` at slot 1.
`Ghost` has no allowances or `totalSupply`; both are unread. Uses the fixed `evmKeccak`
oracle (not `st.env.keccakOf`) so `ofState_foreign` holds. -/
def vaultGhostOf (sto : U256 → U256) : IERC20.Ghost where
  balances := fun o =>
    (sto (mapSlot1 evmKeccak IERC20.balancesMappingSlot (o : Nat))).toNat
  decimals := (sto (BitVec.ofNat 256 IERC20.decimalsSlot)).toNat

def vaultAbsSolidity : Abs IERC20.Ghost where
  ofState st a := vaultGhostOf (evmForeign st (BitVec.ofNat 256 (a : Nat)))
  ofWorld w a := vaultGhostOf (w.storageOf (BitVec.ofNat 256 (a : Nat)))
  ofState_proj := fun _ _ => rfl
  ofWorld_install := fun _ _ _ => rfl

theorem vaultAbsSolidity_ignoresLocal : vaultAbsSolidity.ignoresLocal := by
  intro st σ τ sto tro a hfr hsto _htro
  apply congrArg vaultGhostOf
  funext k
  exact hsto (BitVec.ofNat 256 (a : Nat)) k hfr

theorem vaultAbsSolidity_ofState_foreign : vaultAbsSolidity.ofState_foreign := by
  intro st st' a hξ
  apply congrArg vaultGhostOf
  funext k
  exact hξ k

example : ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨vaultAbsSolidity, vaultAbsSolidity_ignoresLocal, vaultAbsSolidity_ofState_foreign⟩

end Vault
