import Lsc.Compiler.EndToEndExt
import Lsc.Compiler.Proof.Vault
import Lsc.Examples.VaultSecurity
import YulEvmCompiler.Compile
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Bytecode-level Vault theorems. `CallsTotal` + `yul_progress` + EVM determinism
give `EvmCallRunξ` / `EvmTraceRunExtAll` (S2 threads foreign storage `ξ`).
`claim` is read through the shares schema (`vaultClaimRead`). Initial `hRX0`
plus `ofState_foreign` re-establish `RX` at each `mkEvmStateExt`. Amount ABI
agrees with Core via `deposit.core_denote` / `withdraw.core_denote`.
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
  have h0 : σ (BitVec.ofNat 256 0) = BitVec.ofNat 256 s.totalAssets := by
    simpa [vault_schema_totalAssets] using hs 0 _ vault_field_totalAssets
  have h1 : σ (BitVec.ofNat 256 1) = BitVec.ofNat 256 s.totalShares := by
    simpa [vault_schema_totalShares] using hs 1 _ vault_field_totalShares
  have h2 : σ (mapSlot1 evmKeccak 2 a) = BitVec.ofNat 256 (s.shares a) := by
    simpa [vault_schema_shares] using hs 2 _ vault_field_shares a ha
  simp [vaultClaimRead, claim, h0, h1, h2,
    Lsc.Compiler.toNat_ofNat_of_lt hta, Lsc.Compiler.toNat_ofNat_of_lt hts,
    Lsc.Compiler.toNat_ofNat_of_lt hsh]

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

def vaultCalls : List (Step spec) → List (Ctx × FnDef × List Nat)
  | [] => []
  | .call c :: tr => (c.toCtx, vaultFnDef c.fn, encodeVault c.fn c.args) :: vaultCalls tr
  | .env _ :: tr => vaultCalls tr

def CallsBounded : List (Step spec) → Prop
  | [] => True
  | .call c :: tr =>
    CtxWF c.toCtx ∧ (∀ n ∈ encodeVault c.fn c.args, n < wordBound) ∧ CallsBounded tr
  | .env _ :: tr => CallsBounded tr

theorem vault_fnCalldata_bound (fn : Fn) (args : spec.Args fn) :
    (fnCalldata (vaultFnDef fn) (encodeVault fn args)).length < wordBound := by
  rw [length_fnCalldata, encodeVault_length]
  exact vault_fn_params_bound (vaultFnDef_mem fn)

theorem vaultCalls_spec (tr : List (Step spec)) (hb : CallsBounded tr) :
    ∀ p ∈ vaultCalls tr,
      p.2.1 ∈ Vault.contract.functions ∧ p.2.1.kind ≠ .constructor ∧
      p.2.2.length = p.2.1.params.length ∧ (∀ n ∈ p.2.2, n < wordBound) ∧
      CtxWF p.1 ∧ (fnCalldata p.2.1 p.2.2).length < wordBound := by
  induction tr with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
    match s with
    | .env _ =>
      intro p hp
      exact ih (by simpa [CallsBounded] using hb) p hp
    | .call c =>
      intro p hp
      rcases hb with ⟨hctx, hW, htl⟩
      simp [vaultCalls] at hp
      rcases hp with rfl | hp
      · exact ⟨vaultFnDef_mem c.fn, vault_fn_not_ctor (vaultFnDef_mem c.fn),
          encodeVault_length c.fn c.args, hW, hctx, vault_fnCalldata_bound c.fn c.args⟩
      · exact ih htl p hp

/-- Compiled Vault runtime: every Yul `Run` is predicted (`∃ fo`) and has
matching EVM `Steps`. -/
theorem vault_bytecode_call_correct_ext
    (α : Abs IERC20.Ghost) (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal)
    (ctx : Ctx) (w : World Storage Ext Event) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R Vault.contract Vault.schema evmKeccak w yst0)
    (hRX : RX α Vault.assetB w yst0)
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt α Vault.assetB Vault.contract Vault.schema evmKeccak
      calls ctx w yst0 rt is :=
  bytecode_call_correct_ext (I := IERC20) α Vault.assetB Vault.contract Vault.schema
    Vault.schema_lawful hκ calls hCalls
    (fun f hf => vault_fn_not_ctor hf) (fun f hf => vault_fn_s2 hf)
    vault_fields_lt (fun f hf => vault_fn_params_bound hf)
    rt hrt is hcomp ctx w yst0 hctx hR hRX hign hconf vault_bindWF
    (fun f hf => vault_hslot hf) himm0

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

private theorem noAuthAlong_irrel (a : Address) :
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

/-- Dummy context used only to pin `env.address` for `RX` / `ofState_foreign`. -/
private def rxCtx (self : Address) : Ctx where
  sender := 0
  self := self

/-- Initial `RX` snapshot: empty calldata, threaded foreign `ξ`. -/
@[reducible] private def rxStart (α : Abs IERC20.Ghost) (self : Address)
    (w : World Storage Ext Event) (σ : U256 → U256) (ξ : Foreign) : Prop :=
  RX (I := IERC20) (E := Event) α Vault.assetB
    ({ w with log := ([] : List Event) } : World Storage Ext Event)
    (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (rxCtx self))

private def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (Vault.assetB.addr w'.self) ext α

/-- Runtime Vault steps do not write `Storage.asset` (field 5, `coreAvoids`).
Named hypothesis: connecting `Tx.run` success to `depositPost` / `withdrawPost`
/ `{σ with paused := _}` is not yet a lemma. -/
def AssetStable : Prop :=
  ∀ (c : Call spec) (w : World Storage Ext Event),
    (step (.call c) w).self.asset = w.self.asset

theorem vault_bytecode_no_unauthorized_extraction_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : CallsBounded tr) (ha : Nat.lt a wordBound)
    (hRX : rxStart α self w σ ξ)
    (hconf : ConfFun self ext α)
    (hAssetNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hAssetStable : AssetStable) :
    ∃ σ' ξ', EvmTraceRunExt is
        ((vaultCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ ξ σ' ξ' ∧
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  have hnd : selectorsNodup Vault.contract = true := (runtimeBlock_inv hrt).1
  clear hRely
  induction tr generalizing w σ ξ with
  | nil =>
    exact ⟨σ, ξ, EvmTraceRunExt.nil σ ξ, Nat.le_refl _⟩
  | cons s rest ih =>
    match s with
    | .env x' =>
      simpa [vaultCalls] using
        ih (w := w) (σ := σ) (ξ := ξ) hw hW
          ((noAuthAlong_irrel a rest { w with ext := x' } w).mp
            (by simpa [NoAuthAlong] using hA))
          hs hwf hb hRX hAssetNe
    | .call c =>
      rcases hb with ⟨hctxWF, hWargs, htlB⟩
      rcases hW with ⟨htgt, hne, hWtl⟩
      rcases hA with ⟨hAc, hAtl⟩
      have hf := vaultFnDef_mem c.fn
      have hk := vault_fn_not_ctor hf
      have hlenA := encodeVault_length c.fn c.args
      have hcd := vault_fnCalldata_bound c.fn c.args
      have hself : (rxCtx self).self = c.toCtx.self := by
        simp [rxCtx, Call.toCtx, htgt]
      have hRXcall :
          RX α Vault.assetB { w with log := [] }
            (mkEvmStateExt (fnCalldata (vaultFnDef c.fn) (encodeVault c.fn c.args))
              σ ξ evmKeccak c.toCtx) :=
        RX_mkEvmStateExt_ctx (I := IERC20) (bind := Vault.assetB) hF hself hRX
      obtain ⟨σ₁, ξ₁, h1, fo, hpost⟩ :=
        evmCallRun_fnCalldata_ext (I := IERC20) α Vault.assetB Vault.contract Vault.schema
          Vault.schema_lawful hκ ext hCalls htot
          (fun f hf => vault_fn_not_ctor hf) (fun f hf => vault_fn_s2 hf)
          vault_fields_lt (fun f hf => vault_fn_params_bound hf) hnd rt hrt is hcomp
          hign vault_bindWF (fun f hf => vault_hslot hf)
          c.toCtx (vaultFnDef c.fn) (encodeVault c.fn c.args)
          { w with log := [] } σ ξ hf hk hlenA hWargs hctxWF
          (by simpa using hs) rfl (WorldWF_log [] hwf) hcd hRXcall
          (by
            simpa [Call.toCtx, htgt] using hconf { w with log := [] })
      let wfo : World Storage Ext Event := { w with log := [], faults := fo }
      let w1 : World Storage Ext Event :=
        { worldAfter (Core.denote Vault.schema (vaultFnDef c.fn).core
            (encodeVault c.fn c.args).reverse) c.toCtx wfo with log := [] }
      have hs1 : storageRel Vault.contract Vault.schema evmKeccak w1.self σ₁ := by
        dsimp [w1, wfo]
        cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
            (encodeVault c.fn c.args).reverse) c.toCtx wfo with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp [worldAfter, htx, wfo] at hpost ⊢
          exact hpost.1
        | error e =>
          simp [worldAfter, htx, wfo] at hpost ⊢
          simpa [hpost.1] using hs
      have hwf1 : WorldWF Vault.contract Vault.schema w1 := by
        dsimp [w1, wfo]
        cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
            (encodeVault c.fn c.args).reverse) c.toCtx wfo with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp [worldAfter, htx, wfo] at hpost ⊢
          exact WorldWF_log [] hpost.2.1
        | error e =>
          simp [worldAfter, htx, wfo] at hpost ⊢
          exact WorldWF_of_self (by rfl) (WorldWF_log [] hwf)
      have hwfo : Inv self wfo := vault_inv_clear self w fo hw
      have hw1 : Inv self w1 := by
        have hstep : Inv self (step (.call c) wfo) :=
          vault_preserves_inv self c wfo htgt hne hwfo
        have hlog := vault_inv_log self (step (.call c) wfo) [] hstep
        simpa [w1, wfo, step, vault_worldAfter_core_eq] using hlog
      have hpre0 := vault_claim_of_rel w.self σ a hs ha
        (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
      have hpre1 := vault_claim_of_rel w1.self σ₁ a hs1 ha
        (vault_ta_bound w1 hwf1) (vault_ts_bound w1 hwf1)
        (vault_shares_bound w1 a hwf1 ha)
      have hstepLe : vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ₁ a := by
        have hsec1 := vault_no_unauthorized_extraction self [.call c] wfo a
          hwfo ⟨htgt, hne, trivial⟩ trivial
          ⟨by simpa [wfo] using hAc, trivial⟩
        have hcl : claim a w.self ≤ claim a w1.self := by
          have hself : (run [.call c] wfo).self = w1.self := by
            simp [w1, wfo, run, step, vault_worldAfter_core_eq]
          rw [← hself]
          simpa [wfo] using hsec1
        simpa [hpre0, hpre1] using hcl
      have hAssetNe1 :
          accountKey (BitVec.ofNat 256 (Vault.assetB.addr w1.self)) ≠
            accountKey (BitVec.ofNat 256 self) := by
        have : w1.self.asset = w.self.asset := by
          have hstep : (step (.call c) wfo).self.asset = wfo.self.asset :=
            hAssetStable c wfo
          have hw1s : w1.self = (step (.call c) wfo).self := by
            simp [w1, wfo, step, vault_worldAfter_core_eq]
          simpa [hw1s, wfo] using hstep
        simpa [Vault.assetB, this] using hAssetNe
      have hRX1 : rxStart α self w1 σ₁ ξ₁ := by
        dsimp [w1, wfo]
        cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
            (encodeVault c.fn c.args).reverse) c.toCtx wfo with
        | ok prod =>
          rcases prod with ⟨_, w'⟩
          simp [worldAfter, htx, wfo] at hpost ⊢
          rcases hpost with ⟨_, _, stObs, hσ, hξ, hRXobs⟩
          have hRXw' : RX (I := IERC20) (E := Event) α Vault.assetB w' stObs := hRXobs
          exact RX_mkEvmStateExt_ne (I := IERC20) (bind := Vault.assetB) hF hRXw'
            (Eq.symm hξ) (by simpa [Vault.assetB, rxCtx, w1, wfo, worldAfter, htx]
              using hAssetNe1)
        | error e =>
          simp [worldAfter, htx, wfo] at hpost ⊢
          rcases hpost with ⟨hσeq, hξeq⟩
          subst hσeq
          refine RX_of_foreign hF ?_ hRX
          intro k
          have hneCtx : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
              accountKey (BitVec.ofNat 256 c.toCtx.self) := by
            simpa [Call.toCtx, htgt] using hAssetNe
          simp [mkEvmStateExt_foreign, rxCtx, hξeq, hAssetNe, hneCtx]
      have ⟨σ', ξ', htl, hle⟩ :=
        ih (w := w1) (σ := σ₁) (ξ := ξ₁) hw1 hWtl
          ((noAuthAlong_irrel a rest (step (.call c) w) w1).mp hAtl)
          hs1 hwf1 htlB (by simpa [rxStart] using hRX1) hAssetNe1
      exact ⟨σ', ξ', EvmTraceRunExt.cons h1 (by simpa [vaultCalls] using htl),
        Nat.le_trans hstepLe hle⟩

theorem vault_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : CallsBounded tr) (ha : Nat.lt a wordBound)
    (hRX : rxStart α self w σ ξ)
    (hconf : ConfFun self ext α)
    (hAssetNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hAssetStable : AssetStable) :
    ∀ σ' ξ', EvmTraceRunExtAll is
        ((vaultCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ ξ σ' ξ' →
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  intro σ' ξ' hE
  have hnd : selectorsNodup Vault.contract = true := (runtimeBlock_inv hrt).1
  clear hRely
  induction tr generalizing w σ ξ σ' ξ' with
  | nil =>
    have hE' : EvmTraceRunExtAll is [] σ ξ σ' ξ' := by simpa [vaultCalls] using hE
    cases hE'
    exact Nat.le_refl _
  | cons s rest ih =>
    match s with
    | .env x' =>
      exact ih (w := w) (σ := σ) (ξ := ξ) (σ' := σ') (ξ' := ξ') hw hW
        ((noAuthAlong_irrel a rest { w with ext := x' } w).mp
          (by simpa [NoAuthAlong] using hA))
        hs hwf hb hRX hAssetNe (by simpa [vaultCalls] using hE)
    | .call c =>
      have hE' : EvmTraceRunExtAll is
          (⟨c.toCtx, fnCalldata (vaultFnDef c.fn) (encodeVault c.fn c.args)⟩ ::
            (vaultCalls rest).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ ξ σ' ξ' := by
        simpa [vaultCalls] using hE
      cases hE' with
      | cons hstart h1 htl =>
        rcases hb with ⟨hctxWF, hWargs, htlB⟩
        rcases hW with ⟨htgt, hne, hWtl⟩
        rcases hA with ⟨hAc, hAtl⟩
        have hf := vaultFnDef_mem c.fn
        have hk := vault_fn_not_ctor hf
        have hlenA := encodeVault_length c.fn c.args
        have hcd := vault_fnCalldata_bound c.fn c.args
        have hself : (rxCtx self).self = c.toCtx.self := by
          simp [rxCtx, Call.toCtx, htgt]
        have hRXcall :
            RX α Vault.assetB { w with log := [] }
              (mkEvmStateExt (fnCalldata (vaultFnDef c.fn) (encodeVault c.fn c.args))
                σ ξ evmKeccak c.toCtx) :=
          RX_mkEvmStateExt_ctx (I := IERC20) (bind := Vault.assetB) hF hself hRX
        obtain ⟨σp, ξp, hRun, fo, hpost⟩ :=
          evmCallRun_fnCalldata_ext (I := IERC20) α Vault.assetB Vault.contract Vault.schema
            Vault.schema_lawful hκ ext hCalls htot
            (fun f hf => vault_fn_not_ctor hf) (fun f hf => vault_fn_s2 hf)
            vault_fields_lt (fun f hf => vault_fn_params_bound hf) hnd rt hrt is hcomp
            hign vault_bindWF (fun f hf => vault_hslot hf)
            c.toCtx (vaultFnDef c.fn) (encodeVault c.fn c.args)
            { w with log := [] } σ ξ hf hk hlenA hWargs hctxWF
            (by simpa using hs) rfl (WorldWF_log [] hwf) hcd hRXcall
            (by simpa [Call.toCtx, htgt] using hconf { w with log := [] })
        have heq := evmCallRunξ_eq_of_start h1 hRun hstart
        rw [heq.1, heq.2] at htl
        let wfo : World Storage Ext Event := { w with log := [], faults := fo }
        let w1 : World Storage Ext Event :=
          { worldAfter (Core.denote Vault.schema (vaultFnDef c.fn).core
              (encodeVault c.fn c.args).reverse) c.toCtx wfo with log := [] }
        have hs1 : storageRel Vault.contract Vault.schema evmKeccak w1.self σp := by
          dsimp [w1, wfo]
          cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
              (encodeVault c.fn c.args).reverse) c.toCtx wfo with
          | ok prod =>
            rcases prod with ⟨_, w'⟩
            simp [worldAfter, htx, wfo] at hpost ⊢
            exact hpost.1
          | error e =>
            simp [worldAfter, htx, wfo] at hpost ⊢
            simpa [hpost.1] using hs
        have hwf1 : WorldWF Vault.contract Vault.schema w1 := by
          dsimp [w1, wfo]
          cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
              (encodeVault c.fn c.args).reverse) c.toCtx wfo with
          | ok prod =>
            rcases prod with ⟨_, w'⟩
            simp [worldAfter, htx, wfo] at hpost ⊢
            exact WorldWF_log [] hpost.2.1
          | error e =>
            simp [worldAfter, htx, wfo] at hpost ⊢
            exact WorldWF_of_self (by rfl) (WorldWF_log [] hwf)
        have hwfo : Inv self wfo := vault_inv_clear self w fo hw
        have hw1 : Inv self w1 := by
          have hstep : Inv self (step (.call c) wfo) :=
            vault_preserves_inv self c wfo htgt hne hwfo
          have hlog := vault_inv_log self (step (.call c) wfo) [] hstep
          simpa [w1, wfo, step, vault_worldAfter_core_eq] using hlog
        have hpre0 := vault_claim_of_rel w.self σ a hs ha
          (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
        have hpre1 := vault_claim_of_rel w1.self σp a hs1 ha
          (vault_ta_bound w1 hwf1) (vault_ts_bound w1 hwf1)
          (vault_shares_bound w1 a hwf1 ha)
        have hstepLe : vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σp a := by
          have hsec1 := vault_no_unauthorized_extraction self [.call c] wfo a
            hwfo ⟨htgt, hne, trivial⟩ trivial
            ⟨by simpa [wfo] using hAc, trivial⟩
          have hcl : claim a w.self ≤ claim a w1.self := by
            have hself : (run [.call c] wfo).self = w1.self := by
              simp [w1, wfo, run, step, vault_worldAfter_core_eq]
            rw [← hself]
            simpa [wfo] using hsec1
          simpa [hpre0, hpre1] using hcl
        have hAssetNe1 :
            accountKey (BitVec.ofNat 256 (Vault.assetB.addr w1.self)) ≠
              accountKey (BitVec.ofNat 256 self) := by
          have : w1.self.asset = w.self.asset := by
            have hstep : (step (.call c) wfo).self.asset = wfo.self.asset :=
              hAssetStable c wfo
            have hw1s : w1.self = (step (.call c) wfo).self := by
              simp [w1, wfo, step, vault_worldAfter_core_eq]
            simpa [hw1s, wfo] using hstep
          simpa [Vault.assetB, this] using hAssetNe
        have hRX1 : rxStart α self w1 σp ξp := by
          dsimp [w1, wfo]
          cases htx : Tx.run (Core.denote Vault.schema (vaultFnDef c.fn).core
              (encodeVault c.fn c.args).reverse) c.toCtx wfo with
          | ok prod =>
            rcases prod with ⟨_, w'⟩
            simp [worldAfter, htx, wfo] at hpost ⊢
            rcases hpost with ⟨_, _, stObs, hσ, hξ, hRXobs⟩
            have hRXw' : RX (I := IERC20) (E := Event) α Vault.assetB w' stObs := hRXobs
            exact RX_mkEvmStateExt_ne (I := IERC20) (bind := Vault.assetB) hF hRXw'
              (Eq.symm hξ) (by simpa [Vault.assetB, rxCtx, w1, wfo, worldAfter, htx]
                using hAssetNe1)
          | error e =>
            simp [worldAfter, htx, wfo] at hpost ⊢
            rcases hpost with ⟨hσeq, hξeq⟩
            subst hσeq
            refine RX_of_foreign hF ?_ hRX
            intro k
            have hneCtx : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 c.toCtx.self) := by
              simpa [Call.toCtx, htgt] using hAssetNe
            simp [mkEvmStateExt_foreign, rxCtx, hξeq, hAssetNe, hneCtx]
        have htail := ih (w := w1) (σ := σp) (ξ := ξp) (σ' := σ') (ξ' := ξ') hw1 hWtl
          ((noAuthAlong_irrel a rest (step (.call c) w) w1).mp hAtl)
          hs1 hwf1 htlB (by simpa [rxStart] using hRX1) hAssetNe1 htl
        exact Nat.le_trans hstepLe htail

theorem vault_bytecode_solvent_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : CallsBounded tr) (ha : Nat.lt a wordBound)
    (hRX : rxStart α self w σ ξ)
    (hconf : ConfFun self ext α)
    (hAssetNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hAssetStable : AssetStable) :
    ∃ σ' ξ', EvmTraceRunExt is
        ((vaultCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ ξ σ' ξ' ∧
      Solvent claim holdings self (run tr w) := by
  have ⟨σ', ξ', hE, _⟩ :=
    vault_bytecode_no_unauthorized_extraction_exists α ext hCalls htot rt hrt is hcomp
      hκ hign hF self tr w a σ ξ hw hW hRely hA hs hwf hb ha hRX hconf hAssetNe
      hAssetStable
  exact ⟨σ', ξ', hE, vault_solvent self tr w hW hRely hw⟩

theorem vault_bytecode_solvent
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : CallsBounded tr)
    (hRX : rxStart α self w σ ξ)
    (hconf : ConfFun self ext α)
    (hAssetNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hAssetStable : AssetStable) :
    ∀ σ' ξ', EvmTraceRunExtAll is
        ((vaultCalls tr).map fun p => ⟨p.1, fnCalldata p.2.1 p.2.2⟩) σ ξ σ' ξ' →
      Solvent claim holdings self (run tr w) := by
  intro σ' ξ' _hE
  exact vault_solvent self tr w hW hRely hw

/-- Constant ghost: inhabits `ignoresLocal ∧ ofState_foreign`. A layout that
reads `storageOf[a]` (balances at slot `owner`, decimals at slot 0) satisfies
`ofState_foreign` but not `ignoresLocal` for every `a` (executor alias). -/
def vaultAbsConst : Abs IERC20.Ghost where
  ofState := fun _ _ => ({} : IERC20.Ghost)
  ofWorld := fun _ _ => ({} : IERC20.Ghost)
  ofState_proj := fun _ _ => rfl
  ofWorld_install := fun _ _ _ => rfl

theorem vaultAbsConst_ignoresLocal : vaultAbsConst.ignoresLocal := by
  intro st σ τ sto tro a hsto htro; rfl

theorem vaultAbsConst_ofState_foreign : vaultAbsConst.ofState_foreign := by
  intro st st' a hξ; rfl

theorem vault_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨vaultAbsConst, vaultAbsConst_ignoresLocal, vaultAbsConst_ofState_foreign⟩

example : ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  vault_abs_nonvacuous

end Vault
