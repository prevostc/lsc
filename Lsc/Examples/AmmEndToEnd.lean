import Lsc.Compiler.Transport
import Lsc.Compiler.Proof.Amm
import Lsc.Examples.AmmSecurity
import Lsc.Examples.VaultEndToEnd
import Lsc.Lang.CoreProof
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

def ammClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  (σ (mapSlot1 κ 3 a)).toNat

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

@[reducible] def asWord (a : Address) : Nat := a

def ammFnDef : Fn → FnDef
  | .addLiquidity =>
    { name := "addLiquidity", decl := ``Amm.addLiquidity, kind := .view,
      params := [{ name := "a0", ty := .uint256 }, { name := "a1", ty := .uint256 }],
      ret := .word, core := Amm.addLiquidity.core }
  | .removeLiquidity =>
    { name := "removeLiquidity", decl := ``Amm.removeLiquidity, kind := .view,
      params := [{ name := "s", ty := .uint256 }],
      ret := .pair .word .word, core := Amm.removeLiquidity.core }
  | .swap0for1 =>
    { name := "swap0for1", decl := ``Amm.swap0for1, kind := .view,
      params := [{ name := "amountIn", ty := .uint256 }, { name := "minOut", ty := .uint256 }],
      ret := .word, core := Amm.swap0for1.core }
  | .swap1for0 =>
    { name := "swap1for0", decl := ``Amm.swap1for0, kind := .view,
      params := [{ name := "amountIn", ty := .uint256 }, { name := "minOut", ty := .uint256 }],
      ret := .word, core := Amm.swap1for0.core }
  | .getReserves =>
    { name := "getReserves", decl := ``Amm.getReserves, kind := .view,
      params := [], ret := .pair .word .word, core := Amm.getReserves.core }
  | .sharesOf =>
    { name := "sharesOf", decl := ``Amm.sharesOf, kind := .view,
      params := [{ name := "who", ty := .address }],
      ret := .word, core := Amm.sharesOf.core }
  | .quote0for1 =>
    { name := "quote0for1", decl := ``Amm.quote0for1, kind := .view,
      params := [{ name := "amountIn", ty := .uint256 }],
      ret := .word, core := Amm.quote0for1.core }

theorem ammFnDef_mem (fn : Fn) : ammFnDef fn ∈ Amm.contract.functions := by
  cases fn <;> simp [ammFnDef, Amm.contract]

def encodeAmm : (fn : Fn) → spec.Args fn → List Nat
  | .addLiquidity, (a0, a1) => [a0.toNat, a1.toNat]
  | .removeLiquidity, s => [s.toNat]
  | .swap0for1, (amountIn, minOut) => [amountIn.toNat, minOut.toNat]
  | .swap1for0, (amountIn, minOut) => [amountIn.toNat, minOut.toNat]
  | .getReserves, _ => []
  | .sharesOf, who => [asWord who]
  | .quote0for1, amountIn => [amountIn.toNat]

theorem encodeAmm_length (fn : Fn) (args : spec.Args fn) :
    (encodeAmm fn args).length = (ammFnDef fn).params.length := by
  cases fn <;> simp [encodeAmm, ammFnDef]

theorem amm_worldAfter_core_eq (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    worldAfter (Core.denote Amm.schema (ammFnDef fn).core
      (encodeAmm fn args).reverse) ctx w =
    worldAfter (Spec.exec spec fn args) ctx w := by
  cases fn with
  | addLiquidity =>
    rcases args with ⟨a0, a1⟩
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.addLiquidity.core [a1.toNat, a0.toNat]) ctx w =
      worldAfter (Spec.exec spec .addLiquidity (a0, a1)) ctx w
    rw [Amm.addLiquidity.core_denote, Amm.spec_exec_addLiquidity]
    rfl
  | removeLiquidity =>
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.removeLiquidity.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .removeLiquidity args) ctx w
    rw [Amm.removeLiquidity.core_denote, Amm.spec_exec_removeLiquidity]
    rfl
  | swap0for1 =>
    rcases args with ⟨amountIn, minOut⟩
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.swap0for1.core
        [minOut.toNat, amountIn.toNat]) ctx w =
      worldAfter (Spec.exec spec .swap0for1 (amountIn, minOut)) ctx w
    rw [Amm.swap0for1.core_denote, Amm.spec_exec_swap0for1]
    rfl
  | swap1for0 =>
    rcases args with ⟨amountIn, minOut⟩
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.swap1for0.core
        [minOut.toNat, amountIn.toNat]) ctx w =
      worldAfter (Spec.exec spec .swap1for0 (amountIn, minOut)) ctx w
    rw [Amm.swap1for0.core_denote, Amm.spec_exec_swap1for0]
    rfl
  | getReserves =>
    cases args
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.getReserves.core []) ctx w =
      worldAfter (Spec.exec spec .getReserves ()) ctx w
    rw [Amm.getReserves.core_denote, Amm.spec_exec_getReserves]
    rfl
  | sharesOf =>
    dsimp [ammFnDef, encodeAmm, asWord]
    change worldAfter (Core.denote Amm.schema Amm.sharesOf.core [args]) ctx w =
      worldAfter (Spec.exec spec .sharesOf args) ctx w
    rw [Amm.sharesOf.core_denote, Amm.spec_exec_sharesOf]
    rfl
  | quote0for1 =>
    dsimp [ammFnDef, encodeAmm]
    change worldAfter (Core.denote Amm.schema Amm.quote0for1.core [args.toNat]) ctx w =
      worldAfter (Spec.exec spec .quote0for1 args) ctx w
    rw [Amm.quote0for1.core_denote, Amm.spec_exec_quote0for1]
    rfl

def decodeAmmFn (f : FnDef) : Option Fn :=
  if f.name = "addLiquidity" then some .addLiquidity
  else if f.name = "removeLiquidity" then some .removeLiquidity
  else if f.name = "swap0for1" then some .swap0for1
  else if f.name = "swap1for0" then some .swap1for0
  else if f.name = "getReserves" then some .getReserves
  else if f.name = "sharesOf" then some .sharesOf
  else if f.name = "quote0for1" then some .quote0for1
  else none

theorem decodeAmmFn_fnDef (fn : Fn) : decodeAmmFn (ammFnDef fn) = some fn := by
  cases fn <;> simp [decodeAmmFn, ammFnDef]

theorem decodeAmmFn_of_mem (f : FnDef) (hf : f ∈ Amm.contract.functions) :
    ∃ fn, decodeAmmFn f = some fn ∧ f = ammFnDef fn := by
  simp [Amm.contract] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.addLiquidity, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.removeLiquidity, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.swap0for1, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.swap1for0, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.getReserves, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.sharesOf, by simp [decodeAmmFn, ammFnDef], rfl⟩
  · exact ⟨.quote0for1, by simp [decodeAmmFn, ammFnDef], rfl⟩

def decodeAmm : (fn : Fn) → List Nat → spec.Args fn
  | .addLiquidity, a0 :: a1 :: _ => (Amount.ofNat a0, Amount.ofNat a1)
  | .addLiquidity, _ => (Amount.ofNat 0, Amount.ofNat 0)
  | .removeLiquidity, n :: _ => Amount.ofNat n
  | .removeLiquidity, _ => Amount.ofNat 0
  | .swap0for1, a :: b :: _ => (Amount.ofNat a, Amount.ofNat b)
  | .swap0for1, _ => (Amount.ofNat 0, Amount.ofNat 0)
  | .swap1for0, a :: b :: _ => (Amount.ofNat a, Amount.ofNat b)
  | .swap1for0, _ => (Amount.ofNat 0, Amount.ofNat 0)
  | .getReserves, _ => ()
  | .sharesOf, who :: _ => who
  | .sharesOf, _ => 0
  | .quote0for1, n :: _ => Amount.ofNat n
  | .quote0for1, _ => Amount.ofNat 0

theorem encodeAmm_decode (fn : Fn) (ns : List Nat)
    (h : ns.length = (ammFnDef fn).params.length) :
    encodeAmm fn (decodeAmm fn ns) = ns := by
  cases fn <;> simp [ammFnDef] at h
  · obtain ⟨a0, a1, rfl⟩ := length_eq_two.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨a, b, rfl⟩ := length_eq_two.mp h; rfl
  · obtain ⟨a, b, rfl⟩ := length_eq_two.mp h; rfl
  · cases ns <;> simp at h; rfl
  · obtain ⟨who, rfl⟩ := length_eq_one.mp h; rfl
  · obtain ⟨n, rfl⟩ := length_eq_one.mp h; rfl

theorem decodeAmm_encode (fn : Fn) (args : spec.Args fn) :
    decodeAmm fn (encodeAmm fn args) = args := by
  cases fn <;> simp [decodeAmm, encodeAmm, asWord]

@[reducible] def ammCodec : TransportCodec Amm.contract Amm.schema Amm.spec where
  fnDef := ammFnDef
  encode := encodeAmm
  decodeFn := decodeAmmFn
  decode := decodeAmm
  mem := ammFnDef_mem
  encode_length := encodeAmm_length
  decodeFn_fnDef := decodeAmmFn_fnDef
  decodeFn_of_mem := decodeAmmFn_of_mem
  encode_decode := encodeAmm_decode
  decode_encode := decodeAmm_encode
  core_exec := amm_worldAfter_core_eq

@[reducible] def mkAmmSetup (hκ : KeccakSep Amm.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is) :
    TransportSetup Storage Ext Event Error where
  c := Amm.contract
  Γ := Amm.schema
  spec := Amm.spec
  codec := ammCodec
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

def ConfFun (self : Address) (ext : ExternalCalls) (α : Abs IERC20.Ghost) : Prop :=
  ∀ (w' : World Storage Ext Event),
    Conforms IERC20 self (token0B.addr w'.self) ext α ∧
    Conforms IERC20 self (token1B.addr w'.self) ext α

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
    (worldAfter (Core.denote Amm.schema (ammFnDef fn).core
      (encodeAmm fn args).reverse) ctx w).self.token0 = w.self.token0 := by
  cases htx : Tx.run (Core.denote Amm.schema (ammFnDef fn).core
      (encodeAmm fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.token0)
      (ammFnDef fn).core (encodeAmm fn args).reverse 4
      (fun i σ v hne => amm_scalarUpd_token0 i σ v hne)
      (fun i σ m _hne => amm_map1Upd_token0 i σ m)
      (fun i σ m _hne => amm_map2Upd_token0 i σ m)
      (fun b m args ctx w v w' hok => amm_ext_call_self hok)
      (coreAvoids_not_write (amm_fn_avoids0 (ammFnDef_mem fn))) htx

theorem amm_token1_stable_core (fn : Fn) (args : spec.Args fn) (ctx : Ctx)
    (w : World Storage Ext Event) :
    (worldAfter (Core.denote Amm.schema (ammFnDef fn).core
      (encodeAmm fn args).reverse) ctx w).self.token1 = w.self.token1 := by
  cases htx : Tx.run (Core.denote Amm.schema (ammFnDef fn).core
      (encodeAmm fn args).reverse) ctx w with
  | error _ => simp [worldAfter, htx]
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp [worldAfter, htx]
    exact effects_frame_on (P := fun s : Storage => s.token1)
      (ammFnDef fn).core (encodeAmm fn args).reverse 5
      (fun i σ v hne => amm_scalarUpd_token1 i σ v hne)
      (fun i σ m _hne => amm_map1Upd_token1 i σ m)
      (fun i σ m _hne => amm_map2Upd_token1 i σ m)
      (fun b m args ctx w v w' hok => amm_ext_call_self hok)
      (coreAvoids_not_write (amm_fn_avoids1 (ammFnDef_mem fn))) htx

@[reducible] def ammEnv0 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token0B⟩

@[reducible] def ammEnv1 (α : Abs IERC20.Ghost) : BindEnv IERC20 Storage Ext :=
  ⟨α, token1B⟩

@[reducible] def mkAmmBindings
    (hκ : KeccakSep Amm.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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
    · simpa [ammEnv0, token0B, amm_worldAfter_core_eq] using
        amm_token0_stable_core fn args ctx w
    · simpa [ammEnv1, token1B, amm_worldAfter_core_eq] using
        amm_token1_stable_core fn args ctx w

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

theorem amm_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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

theorem amm_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨Vault.vaultAbsSolidity, Vault.vaultAbsSolidity_ignoresLocal,
    Vault.vaultAbsSolidity_ofState_foreign⟩

example : ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  amm_abs_nonvacuous

end Amm
