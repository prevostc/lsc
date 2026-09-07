import Lsc.Compiler.Transport
import Lsc.Compiler.Proof.Vault
import Lsc.Examples.VaultSecurity
import Lsc.Lang.CoreProof
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

def vaultFnDef : Fn → FnDef
  | .deposit =>
    { name := "deposit", decl := ``Vault.deposit, kind := .view,
      params := [{ name := "assets", ty := .uint256 }],
      ret := .word, core := Vault.deposit.core }
  | .withdraw =>
    { name := "withdraw", decl := ``Vault.withdraw, kind := .view,
      params := [{ name := "sharesIn", ty := .uint256 }],
      ret := .word, core := Vault.withdraw.core }
  | .previewDeposit =>
    { name := "previewDeposit", decl := ``Vault.previewDeposit, kind := .view,
      params := [{ name := "assets", ty := .uint256 }],
      ret := .word, core := Vault.previewDeposit.core }
  | .previewRedeem =>
    { name := "previewRedeem", decl := ``Vault.previewRedeem, kind := .view,
      params := [{ name := "sharesIn", ty := .uint256 }],
      ret := .word, core := Vault.previewRedeem.core }
  | .pause =>
    { name := "pause", decl := ``Vault.pause, kind := .tx,
      params := [], ret := .unit, core := Vault.pause.core }
  | .unpause =>
    { name := "unpause", decl := ``Vault.unpause, kind := .tx,
      params := [], ret := .unit, core := Vault.unpause.core }
  | .paused? =>
    { name := "paused?", decl := ``Vault.paused?, kind := .view,
      params := [], ret := .flag, core := Vault.paused?.core }
  | .decimals =>
    { name := "decimals", decl := ``Vault.decimals, kind := .view,
      params := [], ret := .word, core := Vault.decimals.core }

theorem vaultFnDef_mem (fn : Fn) : vaultFnDef fn ∈ Vault.contract.functions := by
  cases fn <;> simp [vaultFnDef, Vault.contract]

def encodeVault : (fn : Fn) → spec.Args fn → List Nat
  | .deposit, assets => [assets.toNat]
  | .withdraw, sharesIn => [sharesIn.toNat]
  | .previewDeposit, assets => [assets.toNat]
  | .previewRedeem, sharesIn => [sharesIn.toNat]
  | .pause, _ => []
  | .unpause, _ => []
  | .paused?, _ => []
  | .decimals, _ => []

theorem encodeVault_length (fn : Fn) (args : spec.Args fn) :
    (encodeVault fn args).length = (vaultFnDef fn).params.length := by
  cases fn <;> simp [encodeVault, vaultFnDef]

theorem vault_worldAfter_core_eq (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    worldAfter (Core.denote Vault.schema (vaultFnDef fn).core
      (encodeVault fn args).reverse) ctx w =
    worldAfter (Spec.exec spec fn args) ctx w := by
  cases fn with
  | deposit =>
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.deposit.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .deposit args) ctx w
    rw [Vault.deposit.core_denote, Vault.spec_exec_deposit]
    rfl
  | withdraw =>
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.withdraw.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .withdraw args) ctx w
    rw [Vault.withdraw.core_denote, Vault.spec_exec_withdraw]
    rfl
  | previewDeposit =>
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.previewDeposit.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .previewDeposit args) ctx w
    rw [Vault.previewDeposit.core_denote, Vault.spec_exec_previewDeposit]
    rfl
  | previewRedeem =>
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.previewRedeem.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .previewRedeem args) ctx w
    rw [Vault.previewRedeem.core_denote, Vault.spec_exec_previewRedeem]
    rfl
  | pause =>
    cases args
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.pause.core []) ctx w =
      worldAfter (Spec.exec spec .pause ()) ctx w
    rw [Vault.pause.core_denote, Vault.spec_exec_pause]
    rfl
  | unpause =>
    cases args
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.unpause.core []) ctx w =
      worldAfter (Spec.exec spec .unpause ()) ctx w
    rw [Vault.unpause.core_denote, Vault.spec_exec_unpause]
    rfl
  | paused? =>
    cases args
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.paused?.core []) ctx w =
      worldAfter (Spec.exec spec .paused? ()) ctx w
    rw [Vault.paused?.core_denote, Vault.spec_exec_paused?]
    rfl
  | decimals =>
    cases args
    dsimp [vaultFnDef, encodeVault]
    change worldAfter (Core.denote Vault.schema Vault.decimals.core []) ctx w =
      worldAfter (Spec.exec spec .decimals ()) ctx w
    rw [Vault.decimals.core_denote, Vault.spec_exec_decimals]
    rfl

def decodeVaultFn (f : FnDef) : Option Fn :=
  if f.name = "deposit" then some .deposit
  else if f.name = "withdraw" then some .withdraw
  else if f.name = "previewDeposit" then some .previewDeposit
  else if f.name = "previewRedeem" then some .previewRedeem
  else if f.name = "pause" then some .pause
  else if f.name = "unpause" then some .unpause
  else if f.name = "paused?" then some .paused?
  else if f.name = "decimals" then some .decimals
  else none

theorem decodeVaultFn_fnDef (fn : Fn) : decodeVaultFn (vaultFnDef fn) = some fn := by
  cases fn <;> simp [decodeVaultFn, vaultFnDef]

theorem decodeVaultFn_of_mem (f : FnDef) (hf : f ∈ Vault.contract.functions) :
    ∃ fn, decodeVaultFn f = some fn ∧ f = vaultFnDef fn := by
  simp [Vault.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.deposit, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.withdraw, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.previewDeposit, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.previewRedeem, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.pause, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.unpause, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.paused?, by simp [decodeVaultFn, vaultFnDef], rfl⟩
  · exact ⟨.decimals, by simp [decodeVaultFn, vaultFnDef], rfl⟩

def decodeVault : (fn : Fn) → List Nat → spec.Args fn
  | .deposit, n :: _ => Amount.ofNat n
  | .deposit, _ => Amount.ofNat 0
  | .withdraw, n :: _ => Amount.ofNat n
  | .withdraw, _ => Amount.ofNat 0
  | .previewDeposit, n :: _ => Amount.ofNat n
  | .previewDeposit, _ => Amount.ofNat 0
  | .previewRedeem, n :: _ => Amount.ofNat n
  | .previewRedeem, _ => Amount.ofNat 0
  | .pause, _ => ()
  | .unpause, _ => ()
  | .paused?, _ => ()
  | .decimals, _ => ()

theorem encodeVault_decode (fn : Fn) (ns : List Nat)
    (h : ns.length = (vaultFnDef fn).params.length) :
    encodeVault fn (decodeVault fn ns) = ns := by
  cases fn <;> simp [vaultFnDef] at h
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · cases ns <;> simp at h; rfl
  · cases ns <;> simp at h; rfl
  · cases ns <;> simp at h; rfl
  · cases ns <;> simp at h; rfl

theorem decodeVault_encode (fn : Fn) (args : spec.Args fn) :
    decodeVault fn (encodeVault fn args) = args := by
  cases fn <;> simp [decodeVault, encodeVault]

@[reducible] def vaultCodec : TransportCodec Vault.contract Vault.schema Vault.spec where
  fnDef := vaultFnDef
  encode := encodeVault
  decodeFn := decodeVaultFn
  decode := decodeVault
  mem := vaultFnDef_mem
  encode_length := encodeVault_length
  decodeFn_fnDef := decodeVaultFn_fnDef
  decodeFn_of_mem := decodeVaultFn_of_mem
  encode_decode := encodeVault_decode
  decode_encode := decodeVault_encode
  core_exec := vault_worldAfter_core_eq

@[reducible] def mkVaultSetup (hκ : KeccakSep Vault.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is) :
    TransportSetup Storage Ext Event Error where
  c := Vault.contract
  Γ := Vault.schema
  spec := Vault.spec
  codec := vaultCodec
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
    (worldAfter (Core.denote Vault.schema (vaultFnDef fn).core
      (encodeVault fn args).reverse) ctx w).self.asset = w.self.asset := by
  cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef fn).core
      (encodeVault fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.asset)
      (vaultFnDef fn).core (encodeVault fn args).reverse 5
      (fun i σ v hne => vault_scalarUpd_asset i σ v hne)
      (fun i σ m _hne => vault_map1Upd_asset i σ m)
      (fun i σ m _hne => vault_map2Upd_asset i σ m)
      (fun b m args ctx w v w' hok => vault_ext_call_self hok)
      (coreAvoids_not_write (vault_fn_avoids (vaultFnDef_mem fn))) htx

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
    simpa [vaultEnv, Vault.assetB, vault_worldAfter_core_eq] using
      vault_asset_stable_core fn args ctx w

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

theorem vault_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkVaultSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkVaultSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (ha : Nat.lt a wordBound)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  intro σ' ξ' hE
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨w', hs', hwf', _, _, hle⟩ :=
    transport_claim_ext T Xpkg (Inv self) claim Auth self a
      (vault_no_unauth self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      calls w σ ξ σ' ξ' hs hlog hwf hWF
      (vault_RXs_of α w _ hRX) (vault_neSelf_of α self w.self hBindNe)
      (vault_confs_of α self ext hconf) (vault_inj_of α w.self) hA hw hE
  have hpre := vault_claim_of_rel w.self σ a hs ha
    (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
  have hpost := vault_claim_of_rel w'.self σ' a hs' ha
    (vault_ta_bound w' hwf') (vault_ts_bound w' hwf') (vault_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

theorem vault_bytecode_no_unauthorized_extraction_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr) (hlog : w.log = [])
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : EncodeBounded (mkVaultSetup hκ rt hrt is hcomp) tr)
    (ha : Nat.lt a wordBound)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∃ σ' ξ', EvmTraceRunExt is
        (encodeCalls (mkVaultSetup hκ rt hrt is hcomp) tr) σ ξ σ' ξ' ∧
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have hwlog : { w with log := ([] : List Event) } = w := by
    cases w; simp at hlog; subst hlog; rfl
  obtain ⟨σ', ξ', w', hE, hs', hwf', _, _, hle⟩ :=
    transport_exists_claim_ext T Xpkg (Inv self) claim Auth self a
      (vault_no_unauth self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      tr w σ ξ hs hwf hb hW hw (vault_noAuthAlong_callsOf a tr w hA)
      (by simpa [hwlog] using vault_RXs_of α w _ hRX)
      (vault_neSelf_of α self w.self hBindNe) (vault_confs_of α self ext hconf)
      (vault_inj_of α w.self)
  refine ⟨σ', ξ', hE, ?_⟩
  have hpre := vault_claim_of_rel w.self σ a hs ha
    (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
  have hpost := vault_claim_of_rel w'.self σ' a hs' ha
    (vault_ta_bound w' hwf') (vault_ts_bound w' hwf') (vault_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

theorem vault_bytecode_solvent
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkVaultSetup hκ rt hrt is hcomp) self calls)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) := by
  intro σ' ξ' hE
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨_, w', hs', hwf', hRX', hInv', haddr⟩ :=
    transport_trace_ext T Xpkg self calls w σ ξ σ' ξ' hs hlog hwf hWF
      (vault_RXs_of α w _ hRX) (vault_neSelf_of α self w.self hBindNe)
      (vault_confs_of α self ext hconf) (vault_inj_of α w.self) (Inv self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      hw hE
  have hsol := vaultSolventRead_of_inv α self w' σ' ξ' hInv' hs' hwf'
    (vault_RX_of α w' _ hRX')
  have haddr' : Vault.assetB.addr w'.self = Vault.assetB.addr w.self :=
    haddr (vaultEnv α) (List.mem_singleton.mpr rfl)
  rw [← haddr']
  exact hsol

theorem vault_bytecode_solvent_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr) (hlog : w.log = [])
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : EncodeBounded (mkVaultSetup hκ rt hrt is hcomp) tr)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∃ σ' ξ', EvmTraceRunExt is
        (encodeCalls (mkVaultSetup hκ rt hrt is hcomp) tr) σ ξ σ' ξ' ∧
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) := by
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have hwlog : { w with log := ([] : List Event) } = w := by
    cases w; simp at hlog; subst hlog; rfl
  obtain ⟨σ', ξ', w', hE, hs', hwf', hRX', hInv', haddr⟩ :=
    transport_exists_ext T Xpkg (Inv self) self
      (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      tr w σ ξ hs hwf hb hW hw
      (by simpa [hwlog] using vault_RXs_of α w _ hRX)
      (vault_neSelf_of α self w.self hBindNe) (vault_confs_of α self ext hconf)
      (vault_inj_of α w.self)
  refine ⟨σ', ξ', hE, ?_⟩
  have hsol := vaultSolventRead_of_inv α self w' σ' ξ' hInv' hs' hwf'
    (vault_RX_of α w' _ hRX')
  have haddr' : Vault.assetB.addr w'.self = Vault.assetB.addr w.self :=
    haddr (vaultEnv α) (List.mem_singleton.mpr rfl)
  rw [← haddr']
  exact hsol

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

theorem vault_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨vaultAbsSolidity, vaultAbsSolidity_ignoresLocal, vaultAbsSolidity_ofState_foreign⟩

example : ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  vault_abs_nonvacuous

end Vault
