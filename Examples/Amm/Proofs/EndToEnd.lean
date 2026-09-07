import Lsc.Compiler.TransportTheorems
import Examples.Amm.Spec
import Examples.Amm.Proofs.Compile
import Examples.Amm.Proofs.Security
import Examples.Vault.Spec
import Examples.Vault.Proofs.EndToEnd
import Lsc.Lang.CoreTheorems
import YulEvmCompiler.Compile
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Bytecode-level AMM theorems via multi-binding `Transport`. Headline is universal
over arbitrary halted calldata (`EvmTraceRunExtAll`), transporting
`amm_no_unauthorized_extraction` to the shares mapping slot.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Amm
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Amm

theorem amm_field_shares :
    Amm.contract.fields[3]? =
      some { name := "shares", kind := .map1, ty := .uint256 } := by
  simp [Amm.contract]

theorem amm_schema_shares (s : Storage) (k : Address) :
    Amm.schema.st.map1 3 s k = s.shares k := rfl

theorem amm_claim_of_rel (s : Storage) (σ : U256 → U256) (a : Address)
    (hs : storageRel Amm.contract Amm.schema evmKeccak s σ)
    (ha : Nat.lt a wordBound) (hsh : s.shares a < wordBound) :
    ammClaimRead evmKeccak σ a = claim a s := by
  simpa [ammClaimRead, claim, amm_schema_shares] using
    storageRel_map1_toNat hs amm_field_shares rfl (by rw [amm_schema_shares]) ha hsh

theorem amm_shares_bound (w : World Storage Ext Event) (a : Address)
    (hwf : WorldWF Amm.contract Amm.schema w) (ha : Nat.lt a wordBound) :
    w.self.shares a < wordBound := by
  have h := hwf 3 _ amm_field_shares
  simpa [amm_schema_shares] using h a ha

@[reducible] def mkAmmSetup (hκ : KeccakSep Amm.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is) :
    TransportSetup Storage Ext Event Error where
  c := Amm.contract
  Γ := Amm.schema
  spec := Amm.spec
  codec := Amm.codec
  lawful := Amm.schema_lawful
  hκ := hκ
  hctor := fun f hf => amm_fn_not_ctor hf
  hlen := amm_fields_lt
  hbound := fun f hf => amm_fn_params_bound hf
  rt := rt
  hrt := hrt
  is := is
  hcomp := hcomp

theorem amm_inv_faults (self : Address) (w : World Storage Ext Event) (fo : Nat → Bool)
    (h : Inv self w) : Inv self { w with faults := fo } := h

theorem amm_inv_log (self : Address) (w : World Storage Ext Event) (log' : List Event)
    (h : Inv self w) : Inv self { w with log := log' } := h

theorem amm_auth_storage (a : Address) (c : Call spec) (s s' : Storage) :
    Auth a c s = Auth a c s' := rfl

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
        (iff_of_eq (congrArg Not (amm_auth_storage a c w.self w'.self)))
        (ih (step (.call c) w) (step (.call c) w'))

private theorem amm_scalarUpd_token0 (i : Nat) (σ : Storage) (v : Nat)
    (h : 4 ≠ i) : (Amm.schema.st.scalarUpd i σ v).token0 = σ.token0 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => cases h rfl
          | succ i =>
            cases i with
            | zero => simp [Amm.schema]
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ i =>
                cases i with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_scalarUpd_token1 (i : Nat) (σ : Storage) (v : Nat)
    (h : 5 ≠ i) : (Amm.schema.st.scalarUpd i σ v).token1 = σ.token1 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => simp [Amm.schema]
          | succ i =>
            cases i with
            | zero => cases h rfl
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ i =>
                cases i with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_map1Upd_token0 (i : Nat) (σ : Storage) (m : Nat → Nat) :
    (Amm.schema.st.map1Upd i σ m).token0 = σ.token0 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => simp [Amm.schema]
          | succ i =>
            cases i with
            | zero => simp [Amm.schema]
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ i =>
                cases i with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_map1Upd_token1 (i : Nat) (σ : Storage) (m : Nat → Nat) :
    (Amm.schema.st.map1Upd i σ m).token1 = σ.token1 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => simp [Amm.schema]
          | succ i =>
            cases i with
            | zero => simp [Amm.schema]
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ i =>
                cases i with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_map2Upd_token0 (i : Nat) (σ : Storage) (m : Nat → Nat → Nat) :
    (Amm.schema.st.map2Upd i σ m).token0 = σ.token0 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => simp [Amm.schema]
          | succ i =>
            cases i with
            | zero => simp [Amm.schema]
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ n =>
                cases n with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_map2Upd_token1 (i : Nat) (σ : Storage) (m : Nat → Nat → Nat) :
    (Amm.schema.st.map2Upd i σ m).token1 = σ.token1 := by
  cases i with
  | zero => simp [Amm.schema]
  | succ i =>
    cases i with
    | zero => simp [Amm.schema]
    | succ i =>
      cases i with
      | zero => simp [Amm.schema]
      | succ i =>
        cases i with
        | zero => simp [Amm.schema]
        | succ i =>
          cases i with
          | zero => simp [Amm.schema]
          | succ i =>
            cases i with
            | zero => simp [Amm.schema]
            | succ i =>
              cases i with
              | zero => simp [Amm.schema]
              | succ n =>
                cases n with
                | zero => simp [Amm.schema]
                | succ _ => simp [Amm.schema]

private theorem amm_ext_call_self
    {b m : Nat} {args : List Nat} {ctx : Ctx}
    {w : World Storage Ext Event} {v : Nat} {w' : World Storage Ext Event}
    (h : Tx.run (Amm.schema.ext.call b m args) ctx w = .ok (v, w')) :
    w'.self = w.self := by
  simp [Amm.schema] at h
  split at h
  · split at h
    · exact Tx.call_self (E := Event) (ε := Error) token0B _ args h
    · simp [Tx.run] at h
  · split at h
    · split at h
      · exact Tx.call_self (E := Event) (ε := Error) token1B _ args h
      · simp [Tx.run] at h
    · simp [Tx.run] at h

theorem amm_token0_stable_core (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    (worldAfter (Core.denote Amm.schema (Amm.fnDef fn).core
      (Amm.encode fn args).reverse) ctx w).self.token0 = w.self.token0 := by
  cases htx : Tx.run (Core.denote Amm.schema (Amm.fnDef fn).core
      (Amm.encode fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.token0)
      (Amm.fnDef fn).core (Amm.encode fn args).reverse 4
      (fun i σ v hne => amm_scalarUpd_token0 i σ v hne)
      (fun i σ m _hne => amm_map1Upd_token0 i σ m)
      (fun i σ m _hne => amm_map2Upd_token0 i σ m)
      (fun b m args ctx w v w' hok => amm_ext_call_self hok)
      (coreAvoids_not_write (amm_fn_avoids0 (Amm.fnDef_mem fn))) htx

theorem amm_token1_stable_core (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    (worldAfter (Core.denote Amm.schema (Amm.fnDef fn).core
      (Amm.encode fn args).reverse) ctx w).self.token1 = w.self.token1 := by
  cases htx : Tx.run (Core.denote Amm.schema (Amm.fnDef fn).core
      (Amm.encode fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.token1)
      (Amm.fnDef fn).core (Amm.encode fn args).reverse 5
      (fun i σ v hne => amm_scalarUpd_token1 i σ v hne)
      (fun i σ m _hne => amm_map1Upd_token1 i σ m)
      (fun i σ m _hne => amm_map2Upd_token1 i σ m)
      (fun b m args ctx w v w' hok => amm_ext_call_self hok)
      (coreAvoids_not_write (amm_fn_avoids1 (Amm.fnDef_mem fn))) htx

@[reducible] def mkAmmBindings
    (hκ : KeccakSep Amm.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign) :
    TransportBindings Storage Ext Event Error IERC20
      (mkAmmSetup hκ rt hrt is hcomp) where
  bs := ammBs α
  extCalls := ext
  hCalls := hCalls
  htot := htot
  hS2 := fun f hf => amm_fn_s2 hf
  hign := amm_ignoresLocal α hign
  hF := amm_ofState_foreign α hF
  hsame := amm_sameAbs α
  horth := amm_orthogonal α
  hBind := amm_lookupWF α
  hslot := fun f hf => amm_hslot α hf
  bindAddr_stable := fun e he fn args ctx w => by
    have : e = ammEnv0 α ∨ e = ammEnv1 α := by
      simpa [ammBs, ammEnv0, ammEnv1, List.mem_cons, List.mem_singleton] using he
    rcases this with rfl | rfl
    · simp [ammEnv0, token0B]
      rw [← Amm.codec.core_exec fn args ctx w]
      exact amm_token0_stable_core fn args ctx w
    · simp [ammEnv1, token1B]
      rw [← Amm.codec.core_exec fn args ctx w]
      exact amm_token1_stable_core fn args ctx w

theorem amm_RXs_of (α : Abs IERC20.Ghost) (w : World Storage Ext Event) (st : EvmState)
    (h0 : RX α token0B w st) (h1 : RX α token1B w st) :
    RXs (ammBs α) w st :=
  (RXs_pair (ammEnv0 α) (ammEnv1 α) w st).mpr ⟨h0, h1⟩

theorem amm_neSelf_of (α : Abs IERC20.Ghost) (self : Address) (σ : Storage)
    (h0 : accountKey (BitVec.ofNat 256 (token0B.addr σ)) ≠
          accountKey (BitVec.ofNat 256 self))
    (h1 : accountKey (BitVec.ofNat 256 (token1B.addr σ)) ≠
          accountKey (BitVec.ofNat 256 self)) :
    BindEnvs.neSelf (ammBs α) self σ := by
  intro e he
  have : e = ammEnv0 α ∨ e = ammEnv1 α := by
    simpa [ammBs, ammEnv0, ammEnv1, List.mem_cons, List.mem_singleton] using he
  rcases this with rfl | rfl
  · exact h0
  · exact h1

theorem amm_confs_of (α : Abs IERC20.Ghost) (self : Address) (ext : ExternalCalls)
    (h : ConfFun self ext α) (w' : World Storage Ext Event) :
    BindEnvs.conforms (ammBs α) self w'.self ext := by
  intro e he
  have : e = ammEnv0 α ∨ e = ammEnv1 α := by
    simpa [ammBs, ammEnv0, ammEnv1, List.mem_cons, List.mem_singleton] using he
  rcases this with rfl | rfl
  · exact (h w').1
  · exact (h w').2

theorem amm_inj_of (α : Abs IERC20.Ghost) (σ : Storage) (h : σ.token0 ≠ σ.token1) :
    BindEnvs.addrInj (ammBs α) σ := by
  intro e1 h1 e2 h2 heq
  have h1' : e1 = ammEnv0 α ∨ e1 = ammEnv1 α := by
    simpa [ammBs, ammEnv0, ammEnv1, List.mem_cons, List.mem_singleton] using h1
  have h2' : e2 = ammEnv0 α ∨ e2 = ammEnv1 α := by
    simpa [ammBs, ammEnv0, ammEnv1, List.mem_cons, List.mem_singleton] using h2
  rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact (h heq).elim
  · exact (h heq.symm).elim
  · exact ⟨rfl, rfl⟩

theorem amm_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨Vault.vaultAbsSolidity, Vault.vaultAbsSolidity_ignoresLocal,
    Vault.vaultAbsSolidity_ofState_foreign⟩

example : ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  amm_abs_nonvacuous


namespace Proof

theorem amm_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (hκ : KeccakSep Amm.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkAmmSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkAmmSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Amm.contract Amm.schema evmKeccak w.self σ)
    (hwf : WorldWF Amm.contract Amm.schema w)
    (ha : Nat.lt a wordBound)
    (hRX0 : RX α token0B w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hRX1 : RX α token1B w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe0 : accountKey (BitVec.ofNat 256 (token0B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hBindNe1 : accountKey (BitVec.ofNat 256 (token1B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hneq : w.self.token0 ≠ w.self.token1) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      ammClaimRead evmKeccak σ a ≤ ammClaimRead evmKeccak σ' a := by
  intro σ' ξ' hE
  let T := mkAmmSetup hκ rt hrt is hcomp
  let Xpkg := mkAmmBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨w', hs', hwf', _, _, hle⟩ :=
    transport_claim_ext T Xpkg (Inv self) claim Auth self a
      (amm_no_unauth self) (amm_preserves_inv self)
      (fun w fo h => amm_inv_faults self w fo h)
      (fun w log h => amm_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      calls w σ ξ σ' ξ' hs hlog hwf hWF
      (amm_RXs_of α w _ hRX0 hRX1) (amm_neSelf_of α self w.self hBindNe0 hBindNe1)
      (amm_confs_of α self ext hconf) (amm_inj_of α w.self hneq) hA hw hE
  have hpre := amm_claim_of_rel w.self σ a hs ha (amm_shares_bound w a hwf ha)
  have hpost := amm_claim_of_rel w'.self σ' a hs' ha (amm_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

end Proof

end Amm
