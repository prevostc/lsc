import Lsc.Compiler.Proof.Maps
import Mathlib.Logic.Function.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Nested mapping slots: inner `keccak256(0,64)` to `[32]`, then `mstore(0, k₂)`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Function

theorem storeWord_comm_0_32 (mem : Nat → UInt8) (v0 v32 : U256) :
    storeWord (storeWord mem 0 v0) 32 v32 = storeWord (storeWord mem 32 v32) 0 v0 := by
  funext a
  simp only [storeWord]
  split_ifs <;> first | rfl | omega

theorem storeWord_overwrite (mem : Nat → UInt8) (p : Nat) (v w : U256) :
    storeWord (storeWord mem p v) p w = storeWord mem p w := by
  funext a
  simp only [storeWord]
  by_cases h : p ≤ a ∧ a < p + 32
  · simp [h]
  · simp [h]

theorem emitMap2SlotPrep_stmts (slot : Nat) (k₁ k₂ : YExpr) :
    (emitMap2SlotPrep {} slot k₁ k₂).stmts =
      (emitMapSlotPrep {} slot k₁).stmts ++
        [.exprStmt (bop Op.mstore [lit 32, keccak064]),
          .exprStmt (bop Op.mstore [lit 0, k₂])] := by
  simp [emitMap2SlotPrep, emitMapSlotPrep, emitDo, Emit.push, Emit.stmts, bop]

theorem emitLet_map2_stmts (slot : Nat) (k₁ k₂ : YExpr) (name : YIdent) (x : YExpr) :
    (emitLet (emitMap2SlotPrep {} slot k₁ k₂) name x).stmts =
      (emitMap2SlotPrep {} slot k₁ k₂).stmts ++ [.letDecl [name] (some x)] := by
  rw [emitLet_acc, Emit.cat_stmts]
  simp [emitLet, Emit.push, Emit.stmts]

theorem map2SlotPrep_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    {k1E k2E : YExpr} {k1v k2v : U256} (slot : Nat)
    (he1 : EvalExpr evm funs V st k1E (.vals [k1v] st))
    (he2 : ∀ st', EvalExpr evm funs V st' k2E (.vals [k2v] st'))
    (hs : slot < wordBound) :
    ∃ st' hash,
      ExecStmts evm funs V st (emitMap2SlotPrep {} slot k1E k2E).stmts V st' .normal ∧
        hash = st.env.keccakOf
          (readBytes (storeWord (storeWord st.memory 0 k1v) 32 (BitVec.ofNat 256 slot)) 0 64) ∧
        st'.memory = storeWord (storeWord st.memory 0 k2v) 32 hash ∧
        MemOnly st st' := by
  obtain ⟨stP, hexecP, hmem, hmP⟩ := mapSlotPrep_exec funs V st slot he1 hs
  have hekecc := eval_keccak064 funs V stP
  let hash := stP.env.keccakOf (readBytes stP.memory 0 64)
  let stK := touchMemory stP 0 64
  let stH :=
    { touchMemory stK 32 32 with memory := storeWord stK.memory 32 hash }
  have hmH :
      ExecStmt evm funs V stP (.exprStmt (bop Op.mstore [lit 32, keccak064])) V stH .normal :=
    Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hekecc) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, toNat_32]; rfl))
  let stF :=
    { touchMemory stH 0 32 with memory := storeWord stH.memory 0 k2v }
  have hmF :
      ExecStmt evm funs V stH (.exprStmt (bop Op.mstore [lit 0, k2E])) V stF .normal :=
    Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (he2 stH)) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, toNat_0]; rfl))
  have hκP : stP.env.keccakOf = st.env.keccakOf := by
    rcases hmP with ⟨_, _, _, _, _, _, _, _, hκeq, _, _⟩; exact hκeq
  refine ⟨stF, hash, ?_, ?_, ?_, ?_⟩
  · simp only [emitMap2SlotPrep_stmts]
    exact execStmts_append hexecP (Step.seqCons hmH (Step.seqCons hmF Step.seqNil))
  · simp only [hash, hmem, hκP]
  · simp only [stF, stH, stK, touchMemory, hash, hmem]
    rw [storeWord_overwrite, storeWord_comm_0_32, storeWord_overwrite,
      ← storeWord_comm_0_32]
  · refine MemOnly.trans hmP ?_
    simp [MemOnly, stK, stH, stF, touchMemory]

theorem map2SlotPrep_hash (st : EvmState) (κ : List UInt8 → U256)
    (k₁ k₂ slot : Nat) (hk1 : k₁ < wordBound) (hk2 : k₂ < wordBound) (hs : slot < wordBound)
    (hκ : st.env.keccakOf = κ)
    {hash : U256} {st' : EvmState}
    (hhash : hash = κ (wordBytes k₁ ++ wordBytes slot))
    (hmem : st'.memory = storeWord (storeWord st.memory 0 (BitVec.ofNat 256 k₂)) 32 hash)
    (hκ' : st'.env.keccakOf = st.env.keccakOf) :
    st'.env.keccakOf (readBytes st'.memory 0 64) = mapSlot2 κ slot k₁ k₂ := by
  have hhash' : hash.toNat < wordBound := by simpa [wordBound] using hash.isLt
  have henc : BitVec.ofNat 256 hash.toNat = hash :=
    BitVec.eq_of_toNat_eq (toNat_ofNat_of_lt hhash')
  rw [hκ', hκ, hmem, ← henc, readBytes_storeWord_pair _ _ _ hk2 hhash']
  unfold mapSlot2 mapSlot1
  rw [hhash]

theorem storageRel_storeMap2 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ σ} {storage : U256 → U256}
    (hR : storageRel c Γ κ σ storage) (hΓ : Γ.st.Lawful c.fields)
    (hκ : KeccakSep c κ) (hlen : c.fields.length < wordBound)
    {f k₁ k₂ v : Nat} (hok : fieldKindOK c f .map2 = true)
    (hk1 : k₁ < wordBound) (hk2 : k₂ < wordBound) (_hv : v < wordBound) :
    storageRel c Γ κ
      (Γ.st.map2Upd f σ (update (Γ.st.map2 f σ) k₁ (update (Γ.st.map2 f σ k₁) k₂ v)))
      (upd storage (mapSlot2 κ f k₁ k₂) (BitVec.ofNat 256 v)) := by
  intro i fd hi
  have ⟨fd', hf, hknd⟩ := (fieldKindOK_iff c f .map2).mp hok
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map2 := by simp [hf, hknd]
  have hfi : f < c.fields.length := (List.getElem?_eq_some_iff.mp hf).1
  have hii : i < c.fields.length := (List.getElem?_eq_some_iff.mp hi).1
  cases hkind : fd.kind with
  | scalar =>
    have hne : mapSlot2 κ f k₁ k₂ ≠ BitVec.ofNat 256 i :=
      hκ.map2_ne_scalar hfi hii hk1 hk2 hfkind (by simp [hi, hkind])
    simp only [upd]
    split_ifs with hslot
    · exact (hne hslot.symm).elim
    · rw [hΓ.map2_scalar i f σ _ hfkind]
      have this := hR i fd hi
      simp [hkind] at this
      exact this
  | map1 =>
    intro k' hk'
    have hne : mapSlot2 κ f k₁ k₂ ≠ mapSlot1 κ i k' :=
      hκ.map2_ne_map1 hfi hii hk1 hk2 hk' hfkind (by simp [hi, hkind])
    simp only [upd]
    split_ifs with hslot
    · exact (hne hslot.symm).elim
    · rw [hΓ.map2_map1 i f σ _ hfkind]
      have this := hR i fd hi
      simp [hkind] at this
      exact this k' hk'
  | map2 =>
    intro a₁ a₂ ha1 ha2
    have hikind : (c.fields[i]?).map (·.kind) = some FieldKind.map2 := by simp [hi, hkind]
    simp only [upd]
    split_ifs with hslot
    · have heq := hκ.map2_inj hii hfi ha1 ha2 hk1 hk2 hikind hfkind hslot
      have hieq : i = f := heq.1
      have hk1eq : a₁ = k₁ := heq.2.1
      have hk2eq : a₂ = k₂ := heq.2.2
      subst hieq; subst hk1eq; subst hk2eq
      rw [hΓ.map2_map2 i i σ _ hfkind, if_pos rfl, update_self, update_self]
    · rw [hΓ.map2_map2 i f σ _ hfkind]
      split_ifs with hieq
      · subst hieq
        by_cases hk1eq : a₁ = k₁
        · subst hk1eq
          have hk2ne : a₂ ≠ k₂ := fun he => hslot (he ▸ rfl)
          rw [update_self, update_of_ne hk2ne]
          have this := hR i fd hi
          simp [hkind] at this
          exact this _ a₂ hk1 ha2
        · rw [update_of_ne hk1eq]
          have this := hR i fd hi
          simp [hkind] at this
          exact this a₁ a₂ ha1 ha2
      · have this := hR i fd hi
        simp [hkind] at this
        exact this a₁ a₂ ha1 ha2

theorem worldWF_storeMap2 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} (h : WorldWF c Γ w) (hΓ : Γ.st.Lawful c.fields)
    {f k₁ k₂ v : Nat} (hok : fieldKindOK c f .map2 = true)
    (hk1 : k₁ < wordBound) (hk2 : k₂ < wordBound) (hv : v < wordBound) :
    WorldWF c Γ
      { w with self :=
        Γ.st.map2Upd f w.self (update (Γ.st.map2 f w.self) k₁
          (update (Γ.st.map2 f w.self k₁) k₂ v)) } := by
  intro i fd hi
  have ⟨_, hf, hknd⟩ := (fieldKindOK_iff c f .map2).mp hok
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map2 := by simp [hf, hknd]
  have hold := h i fd hi
  cases hkind : fd.kind with
  | scalar =>
    simp [hkind] at hold ⊢
    rw [hΓ.map2_scalar i f w.self _ hfkind]; exact hold
  | map1 =>
    simp [hkind] at hold ⊢
    rw [hΓ.map2_map1 i f w.self _ hfkind]; exact hold
  | map2 =>
    simp [hkind] at hold ⊢
    rw [hΓ.map2_map2 i f w.self _ hfkind]
    split_ifs with hieq
    · subst hieq
      intro a₁ a₂ ha1 ha2
      by_cases hk1eq : a₁ = k₁
      · subst hk1eq
        by_cases hk2eq : a₂ = k₂
        · subst hk2eq; rw [update_self, update_self]; exact hv
        · rw [update_self, update_of_ne hk2eq]; exact hold _ a₂ hk1 ha2
      · rw [update_of_ne hk1eq]; exact hold a₁ a₂ ha1 ha2
    · exact hold

theorem R_sstoreMap2 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {st : EvmState} {f k₁ k₂ v : Nat}
    (hR : R c Γ κ w st) (_hctx : ctxRel ctx st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hok : fieldKindOK c f .map2 = true)
    (hk1 : k₁ < wordBound) (hk2 : k₂ < wordBound) (hv : v < wordBound) :
    R c Γ κ
      { w with self :=
        Γ.st.map2Upd f w.self (update (Γ.st.map2 f w.self) k₁
          (update (Γ.st.map2 f w.self k₁) k₂ v)) }
      { st with
        storage := upd st.storage (mapSlot2 κ f k₁ k₂) (BitVec.ofNat 256 v)
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address
            (mapSlot2 κ f k₁ k₂) (BitVec.ofNat 256 v) } } := by
  rcases hR with ⟨hs, hl, hkκ, hwf⟩
  refine ⟨storageRel_storeMap2 hs hΓ hκ hlen hok hk1 hk2 hv, ?_, hkκ,
    worldWF_storeMap2 hwf hΓ hok hk1 hk2 hv⟩
  unfold logsRel at hl ⊢; exact hl

theorem op_sim_loadMap2 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat} {k₁ k₂ : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hlen : c.fields.length < wordBound)
    (hwf : opWF c (.loadMap2 f k₁ k₂) = true)
    (hn : identsNodup (env.length + 1) = true) :
    let v := Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env)
    ∃ st',
      ExecStmts evm funs V st
        (emitLet (emitMap2SlotPrep {} f (atomE env.length k₁) (atomE env.length k₂))
          (identV env.length) (bop Op.sload [keccak064])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  rcases hR with ⟨hs, hl, hκe, hW⟩
  have hwf' : (fieldKindOK c f .map2 = true ∧ atomWF k₁ = true) ∧ atomWF k₂ = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ⟨fd, hfd, hknd⟩ := (fieldKindOK_iff c f FieldKind.map2).mp hwf'.1.1
  have hn0 : identsNodup env.length = true := identsNodup_mono (by omega) hn
  have hk1 := atom_eval_lt henv hwf'.1.2
  have hk2 := atom_eval_lt henv hwf'.2
  have hfB := field_lt_wordBound hlen hfd
  have he1 := eval_atom funs (st := st) hV hn0 k₁
  obtain ⟨stP, hash, hexecP, hhashEq, hmem, hmP⟩ :=
    map2SlotPrep_exec funs V st f he1 (fun st' => eval_atom funs (st := st') hV hn0 k₂) hfB
  have hκP : stP.env.keccakOf = st.env.keccakOf := by
    rcases hmP with ⟨_, _, _, _, _, _, _, _, hκeq, _, _⟩; exact hκeq
  have hinner :
      hash = κ (wordBytes (k₁.eval env) ++ wordBytes f) := by
    rw [hhashEq, hκe, readBytes_storeWord_pair _ _ _ hk1 hfB]
  have hslot2 :
      stP.env.keccakOf (readBytes stP.memory 0 64) =
        mapSlot2 κ f (k₁.eval env) (k₂.eval env) :=
    map2SlotPrep_hash (st := st) κ (k₁.eval env) (k₂.eval env) f hk1 hk2 hfB hκe
      hinner hmem hκP
  have hv : Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env) < wordBound := by
    have this := hW f fd hfd
    simp [hknd] at this
    exact this (k₁.eval env) (k₂.eval env) hk1 hk2
  have hsto : stP.storage = st.storage := by rcases hmP with ⟨hsto, _⟩; exact hsto
  have hslot :
      stP.storage (mapSlot2 κ f (k₁.eval env) (k₂.eval env)) =
        BitVec.ofNat 256 (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env)) := by
    have this := hs f fd hfd
    simp [hknd] at this
    simpa [hsto] using this (k₁.eval env) (k₂.eval env) hk1 hk2
  let stK := touchMemory stP 0 64
  have hsload :
      EvalExpr evm funs V stP (bop Op.sload [keccak064])
        (.vals [stP.storage (mapSlot2 κ f (k₁.eval env) (k₂.eval env))] stK) := by
    have hekecc := eval_keccak064 funs V stP
    rw [hslot2] at hekecc
    exact Step.builtinOk (Step.argsCons Step.argsNil hekecc) (by simp only [step_sload]; rfl)
  rw [hslot] at hsload
  have hlet :
      ExecStmt evm funs V stP
        (.letDecl [identV env.length] (some (bop Op.sload [keccak064])))
        ((identV env.length,
          BitVec.ofNat 256 (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env))) :: V)
        stK .normal :=
    Step.letVal hsload rfl
  refine ⟨stK, ?_, ?_⟩
  · rw [emitLet_map2_stmts]
    exact execStmts_append hexecP (Step.seqCons hlet Step.seqNil)
  · have hmK : MemOnly st stK := MemOnly.trans hmP (memOnly_touch stP 0 64)
    exact ⟨by rw [hV, toVEnv_cons], envWF_cons hv henv,
      R_memOnly ⟨hs, hl, hκe, hW⟩ hmK, ctxRel_memOnly hctx hmK⟩

theorem stmt_sim_storeMap2 {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat} {k₁ k₂ val : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hwf : stmtWF c (.storeMap2 f k₁ k₂ val) = true)
    (hn : identsNodup env.length = true) :
    let kn1 := k₁.eval env
    let kn2 := k₂.eval env
    let v := val.eval env
    let w' := { w with self := Γ.st.map2Upd f w.self (update (Γ.st.map2 f w.self) kn1 (update (Γ.st.map2 f w.self kn1) kn2 v)) }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.storeMap2 f k₁ k₂ val)).stmts
        V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  rcases hR with ⟨hs, hl, hκe, hW⟩
  have hwf' :
      ((fieldKindOK c f .map2 = true ∧ atomWF k₁ = true) ∧ atomWF k₂ = true) ∧
        atomWF val = true := by
    simpa [stmtWF, Bool.and_eq_true] using hwf
  have ⟨fd, hfd, hknd⟩ := (fieldKindOK_iff c f FieldKind.map2).mp hwf'.1.1.1
  have hk1 := atom_eval_lt henv hwf'.1.1.2
  have hk2 := atom_eval_lt henv hwf'.1.2
  have hv := atom_eval_lt henv hwf'.2
  have hfB := field_lt_wordBound hlen hfd
  have he1 := eval_atom funs (st := st) hV hn k₁
  obtain ⟨stP, hash, hexecP, hhashEq, hmem, hmP⟩ :=
    map2SlotPrep_exec funs V st f he1 (fun st' => eval_atom funs (st := st') hV hn k₂) hfB
  have hκP : stP.env.keccakOf = st.env.keccakOf := by
    rcases hmP with ⟨_, _, _, _, _, _, _, _, hκeq, _, _⟩; exact hκeq
  have hinner :
      hash = κ (wordBytes (k₁.eval env) ++ wordBytes f) := by
    rw [hhashEq, hκe, readBytes_storeWord_pair _ _ _ hk1 hfB]
  have hslot2 :
      stP.env.keccakOf (readBytes stP.memory 0 64) =
        mapSlot2 κ f (k₁.eval env) (k₂.eval env) :=
    map2SlotPrep_hash (st := st) κ (k₁.eval env) (k₂.eval env) f hk1 hk2 hfB hκe
      hinner hmem hκP
  have hev := eval_atom funs (st := stP) hV hn val
  have hctxP := ctxRel_memOnly hctx hmP
  have hstatic := ctxRel_static hctxP
  let stK := touchMemory stP 0 64
  have hekecc := eval_keccak064 funs V stP
  rw [hslot2] at hekecc
  have hsstore :
      EvalExpr evm funs V stP (bop Op.sstore [keccak064, atomE env.length val])
        (.vals []
          { stK with
            storage := upd stK.storage (mapSlot2 κ f (k₁.eval env) (k₂.eval env))
              (BitVec.ofNat 256 (val.eval env))
            env := { stK.env with
              storageOf := updAccount stK.env.storageOf stK.env.address
                (mapSlot2 κ f (k₁.eval env) (k₂.eval env))
                (BitVec.ofNat 256 (val.eval env)) } }) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hev) hekecc)
      (by
        have hstaticK : stK.env.static = false := by simp [stK, touchMemory, hstatic]
        simp only [stK, step_sstore (touchMemory stP 0 64) _ _ hstaticK])
  let st' :=
    { stK with
      storage := upd stK.storage (mapSlot2 κ f (k₁.eval env) (k₂.eval env))
        (BitVec.ofNat 256 (val.eval env))
      env := { stK.env with
        storageOf := updAccount stK.env.storageOf stK.env.address
          (mapSlot2 κ f (k₁.eval env) (k₂.eval env))
          (BitVec.ofNat 256 (val.eval env)) } }
  have hexpr :
      ExecStmt evm funs V stP
        (.exprStmt (bop Op.sstore [keccak064, atomE env.length val])) V st' .normal :=
    Step.exprStmt hsstore
  refine ⟨st', ?_, ?_⟩
  · rw [emitStmt_storeMap2]
    exact execStmts_append hexecP (Step.seqCons hexpr Step.seqNil)
  · have hmK : MemOnly st stK := MemOnly.trans hmP (memOnly_touch stP 0 64)
    have hRK : R c Γ κ w stK := R_memOnly ⟨hs, hl, hκe, hW⟩ hmK
    exact ⟨hV, henv,
      R_sstoreMap2 hRK (ctxRel_memOnly hctx hmK) hΓ hκ hlen hwf'.1.1.1 hk1 hk2 hv,
      ctxRel_sstore (ctxRel_memOnly hctx hmK) _ _⟩

end Lsc.Compiler
