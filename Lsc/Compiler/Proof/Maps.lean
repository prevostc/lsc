import Lsc.Compiler.Proof.Ops
import Mathlib.Logic.Function.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Mapping slots: `mstore(0,k) mstore(32,f) keccak256(0,64)`, plus the nested `map2` prep.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Function

theorem toNat_0 : (BitVec.ofNat 256 0).toNat = 0 :=
  toNat_ofNat_of_lt zero_lt_wordBound

theorem toNat_64 : (BitVec.ofNat 256 64).toNat = 64 :=
  toNat_ofNat_of_lt (lt_256_wordBound (by decide))

theorem step_keccak256 (st : EvmState) (p n : U256) :
    stepOp Op.keccak256 [p, n] st = some (.ok
      [st.env.keccakOf (readBytes st.memory p.toNat n.toNat)]
      (touchMemory st p.toNat n.toNat)) := rfl

theorem emitMapSlotPrep_stmts (slot : Nat) (k : YExpr) :
    (emitMapSlotPrep {} slot k).stmts =
      [.exprStmt (bop Op.mstore [lit 0, k]),
        .exprStmt (bop Op.mstore [lit 32, lit slot])] := by
  simp [emitMapSlotPrep, emitDo, Emit.push, Emit.stmts, bop]

theorem emitLetOp_loadMap (c : ContractDef) (e : Emit) (d f : Nat) (k : Atom) :
    emitLetOp c e d (.loadMap f k) =
      some (emitLet (emitMapSlotPrep e f (atomE d k)) (identV d)
        (bop Op.sload [keccak064])) := rfl

theorem emitStmt_storeMap (c : ContractDef) (e : Emit) (d f : Nat) (k v : Atom) :
    (emitStmt c e d (.storeMap f k v)).stmts =
      (emitMapSlotPrep e f (atomE d k)).stmts ++
        [.exprStmt (bop Op.sstore [keccak064, atomE d v])] := by
  simp [emitStmt, emitMapSlotPrep, emitDo, Emit.push, Emit.stmts, List.append_assoc, bop]

theorem emitLetOp_loadMap2 (c : ContractDef) (e : Emit) (d f : Nat) (k₁ k₂ : Atom) :
    emitLetOp c e d (.loadMap2 f k₁ k₂) =
      some (emitLet (emitMap2SlotPrep e f (atomE d k₁) (atomE d k₂)) (identV d)
        (bop Op.sload [keccak064])) := rfl

theorem emitStmt_storeMap2 (c : ContractDef) (e : Emit) (d f : Nat) (k₁ k₂ v : Atom) :
    (emitStmt c e d (.storeMap2 f k₁ k₂ v)).stmts =
      (emitMap2SlotPrep e f (atomE d k₁) (atomE d k₂)).stmts ++
        [.exprStmt (bop Op.sstore [keccak064, atomE d v])] := by
  simp [emitStmt, emitMap2SlotPrep, emitMapSlotPrep, emitDo, Emit.push, Emit.stmts,
    List.append_assoc, bop]

theorem eval_keccak064 (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) :
    EvalExpr evm funs V st keccak064
      (.vals [st.env.keccakOf (readBytes st.memory 0 64)] (touchMemory st 0 64)) :=
  Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
    (by
      simp only [evm_litValue_number, step_keccak256, toNat_0, toNat_64]
      rfl)

theorem mapSlotPrep_exec (funs : FunEnv evm) (V : VEnv evm) (st : EvmState)
    {kE : YExpr} {kv : U256} (slot : Nat)
    (he : EvalExpr evm funs V st kE (.vals [kv] st)) (hs : slot < wordBound) :
    ∃ st', ExecStmts evm funs V st (emitMapSlotPrep {} slot kE).stmts V st' .normal ∧
      st'.memory = storeWord (storeWord st.memory 0 kv) 32 (BitVec.ofNat 256 slot) ∧
      MemOnly st st' := by
  have h0 := toNat_0
  have h32 := toNat_32
  let st1 := { touchMemory st 0 32 with memory := storeWord st.memory 0 kv }
  have hm1 :
      ExecStmt evm funs V st (.exprStmt (bop Op.mstore [lit 0, kE])) V st1 .normal :=
    Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil he) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, h0]; rfl))
  let st2 :=
    { touchMemory st1 32 32 with
      memory := storeWord st1.memory 32 (BitVec.ofNat 256 slot) }
  have hm2 :
      ExecStmt evm funs V st1 (.exprStmt (bop Op.mstore [lit 32, lit slot])) V st2 .normal :=
    Step.exprStmt (Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
      (by simp only [evm_litValue_number, step_mstore, h32]; rfl))
  refine ⟨st2, ?_, rfl, ?_⟩
  · simp only [emitMapSlotPrep_stmts]
    exact Step.seqCons hm1 (Step.seqCons hm2 Step.seqNil)
  · refine MemOnly.trans (memOnly_mstore st 0 kv) ?_
    simp [MemOnly, st1, st2, touchMemory]

theorem mapSlotPrep_hash (st : EvmState) (κ : List UInt8 → U256)
    (k slot : Nat) (hk : k < wordBound) (hs : slot < wordBound)
    (hκ : st.env.keccakOf = κ)
    {kv : U256} (hkv : kv = BitVec.ofNat 256 k)
    {st' : EvmState}
    (hmem : st'.memory =
      storeWord (storeWord st.memory 0 kv) 32 (BitVec.ofNat 256 slot))
    (hκ' : st'.env.keccakOf = st.env.keccakOf) :
    st'.env.keccakOf (readBytes st'.memory 0 64) = mapSlot1 κ slot k := by
  rw [hκ', hκ, hmem, hkv, readBytes_storeWord_pair _ _ _ hk hs]
  rfl

theorem storageRel_storeMap {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ σ} {storage : U256 → U256}
    (hR : storageRel c Γ κ σ storage) (hΓ : Γ.st.Lawful c.fields)
    (hκ : KeccakSep c κ) (hlen : c.fields.length < wordBound)
    {f k v : Nat} (hok : fieldKindOK c f .map1 = true)
    (hk : k < wordBound) (_hv : v < wordBound) :
    storageRel c Γ κ (Γ.st.map1Upd f σ (update (Γ.st.map1 f σ) k v))
      (upd storage (mapSlot1 κ f k) (BitVec.ofNat 256 v)) := by
  intro i fd hi
  have ⟨fd', hf, hknd⟩ := (fieldKindOK_iff c f .map1).mp hok
  have hiB := field_lt_wordBound hlen hi
  have hfB := field_lt_wordBound hlen hf
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map1 := by simp [hf, hknd]
  have hfi : f < c.fields.length := (List.getElem?_eq_some_iff.mp hf).1
  have hii : i < c.fields.length := (List.getElem?_eq_some_iff.mp hi).1
  cases hkind : fd.kind with
  | scalar =>
    have hne : mapSlot1 κ f k ≠ BitVec.ofNat 256 i :=
      hκ.map1_ne_scalar hfi hii hk hfkind (by simp [hi, hkind])
    simp only [upd]
    split_ifs with hslot
    · exact (hne hslot.symm).elim
    · rw [hΓ.map1_scalar i f σ _ hfkind]
      have this := hR i fd hi
      simp [hkind] at this
      exact this
  | map1 =>
    intro k' hk'
    have hikind : (c.fields[i]?).map (·.kind) = some FieldKind.map1 := by simp [hi, hkind]
    simp only [upd]
    split_ifs with hslot
    · have heq := hκ.map1_inj hii hfi hk' hk hikind hfkind hslot
      have hieq : i = f := heq.1
      have hkeq : k' = k := heq.2
      subst hieq; subst hkeq
      rw [hΓ.map1_map1 i i σ _ hfkind, if_pos rfl, update_self]
    · rw [hΓ.map1_map1 i f σ _ hfkind]
      split_ifs with hieq
      · subst hieq
        have hkne : k' ≠ k := fun he => hslot (he ▸ rfl)
        rw [update_of_ne hkne]
        have this := hR i fd hi
        simp [hkind] at this
        exact this k' hk'
      · have this := hR i fd hi
        simp [hkind] at this
        exact this k' hk'
  | map2 =>
    intro k₁ k₂ hk1 hk2
    have hne : mapSlot2 κ i k₁ k₂ ≠ mapSlot1 κ f k :=
      hκ.map2_ne_map1 hii hfi hk1 hk2 hk (by simp [hi, hkind]) hfkind
    simp [upd, hne]
    rw [hΓ.map1_map2 i f σ _ hfkind]
    have this := hR i fd hi
    simp [hkind] at this
    exact this k₁ k₂ hk1 hk2

theorem worldWF_storeMap {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} (h : WorldWF c Γ w) (hΓ : Γ.st.Lawful c.fields)
    {f k v : Nat} (hok : fieldKindOK c f .map1 = true)
    (hk : k < wordBound) (hv : v < wordBound) :
    WorldWF c Γ { w with self := Γ.st.map1Upd f w.self (update (Γ.st.map1 f w.self) k v) } := by
  intro i fd hi
  have ⟨_, hf, hknd⟩ := (fieldKindOK_iff c f .map1).mp hok
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map1 := by simp [hf, hknd]
  have hold := h i fd hi
  cases hkind : fd.kind with
  | scalar =>
    simp [hkind] at hold ⊢
    rw [hΓ.map1_scalar i f w.self _ hfkind]; exact hold
  | map1 =>
    simp [hkind] at hold ⊢
    rw [hΓ.map1_map1 i f w.self _ hfkind]
    split_ifs with hieq
    · subst hieq
      intro k' hk'
      by_cases hkeq : k' = k
      · subst hkeq; rw [update_self]; exact hv
      · rw [update_of_ne hkeq]; exact hold k' hk'
    · exact hold
  | map2 =>
    simp [hkind] at hold ⊢
    rw [hΓ.map1_map2 i f w.self _ hfkind]; exact hold

theorem R_sstoreMap {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {st : EvmState} {f k v : Nat}
    (hR : R c Γ κ w st) (_hctx : ctxRel ctx st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hok : fieldKindOK c f .map1 = true) (hk : k < wordBound) (hv : v < wordBound) :
    R c Γ κ { w with self := Γ.st.map1Upd f w.self (update (Γ.st.map1 f w.self) k v) }
      { st with
        storage := upd st.storage (mapSlot1 κ f k) (BitVec.ofNat 256 v)
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address
            (mapSlot1 κ f k) (BitVec.ofNat 256 v) } } := by
  rcases hR with ⟨hs, hl, hkκ, hwf⟩
  refine ⟨storageRel_storeMap hs hΓ hκ hlen hok hk hv, ?_, hkκ,
    worldWF_storeMap hwf hΓ hok hk hv⟩
  unfold logsRel at hl ⊢; exact hl

theorem emitLet_mapSlot_stmts (slot : Nat) (k : YExpr) (name : YIdent) (x : YExpr) :
    (emitLet (emitMapSlotPrep {} slot k) name x).stmts =
      (emitMapSlotPrep {} slot k).stmts ++ [.letDecl [name] (some x)] := by
  rw [emitLet_acc, Emit.cat_stmts]
  simp [emitLet, Emit.push, Emit.stmts]

theorem op_sim_loadMap {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat} {k : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hlen : c.fields.length < wordBound)
    (hwf : opWF c (.loadMap f k) = true)
    (hn : identsNodup (env.length + 1) = true) :
    let kn := k.eval env
    let v := Γ.st.map1 f w.self kn
    ∃ st',
      ExecStmts evm funs V st
        (emitLet (emitMapSlotPrep {} f (atomE env.length k)) (identV env.length)
          (bop Op.sload [keccak064])).stmts
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
      Inv Γ c κ ctx w (v :: env)
        ((identV env.length, BitVec.ofNat 256 v) :: V) st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  rcases hR with ⟨hs, hl, hκe, hW⟩
  have hwf' : fieldKindOK c f .map1 = true ∧ atomWF k = true := by
    simpa [opWF, Bool.and_eq_true] using hwf
  have ⟨fd, hfd, hknd⟩ := (fieldKindOK_iff c f FieldKind.map1).mp hwf'.1
  have hn0 : identsNodup env.length = true := identsNodup_mono (by omega) hn
  have hk := atom_eval_lt henv hwf'.2
  have hfB := field_lt_wordBound hlen hfd
  have hek := eval_atom funs (st := st) hV hn0 k
  obtain ⟨stP, hexecP, hmem, hmP⟩ := mapSlotPrep_exec funs V st f hek hfB
  have hhash :
      stP.env.keccakOf (readBytes stP.memory 0 64) = mapSlot1 κ f (k.eval env) :=
    mapSlotPrep_hash (st := st) κ (k.eval env) f hk hfB hκe rfl hmem
      (by rcases hmP with ⟨_, _, _, _, _, _, _, _, hκeq, _, _⟩; exact hκeq)
  have hv : Γ.st.map1 f w.self (k.eval env) < wordBound := by
    have this := hW f fd hfd
    simp [hknd] at this
    exact this (k.eval env) hk
  have hsto : stP.storage = st.storage := by rcases hmP with ⟨hsto, _⟩; exact hsto
  have hslot :
      stP.storage (mapSlot1 κ f (k.eval env)) =
        BitVec.ofNat 256 (Γ.st.map1 f w.self (k.eval env)) := by
    have this := hs f fd hfd
    simp [hknd] at this
    simpa [hsto] using this (k.eval env) hk
  let stK := touchMemory stP 0 64
  have hsload :
      EvalExpr evm funs V stP (bop Op.sload [keccak064])
        (.vals [stP.storage (mapSlot1 κ f (k.eval env))] stK) := by
    have hekecc := eval_keccak064 funs V stP
    rw [hhash] at hekecc
    exact Step.builtinOk (Step.argsCons Step.argsNil hekecc) (by simp only [step_sload]; rfl)
  rw [hslot] at hsload
  have hlet :
      ExecStmt evm funs V stP
        (.letDecl [identV env.length] (some (bop Op.sload [keccak064])))
        ((identV env.length, BitVec.ofNat 256 (Γ.st.map1 f w.self (k.eval env))) :: V)
        stK .normal :=
    Step.letVal hsload rfl
  refine ⟨stK, ?_, ?_⟩
  · rw [emitLet_mapSlot_stmts]
    exact execStmts_append hexecP (Step.seqCons hlet Step.seqNil)
  · have hmK : MemOnly st stK := MemOnly.trans hmP (memOnly_touch stP 0 64)
    exact ⟨by rw [hV, toVEnv_cons], envWF_cons hv henv,
      R_memOnly ⟨hs, hl, hκe, hW⟩ hmK, ctxRel_memOnly hctx hmK⟩

theorem stmt_sim_storeMap {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {f : Nat} {k val : Atom}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hwf : stmtWF c (.storeMap f k val) = true)
    (hn : identsNodup env.length = true) :
    let kn := k.eval env
    let v := val.eval env
    let w' := { w with self := Γ.st.map1Upd f w.self (update (Γ.st.map1 f w.self) kn v) }
    ∃ st',
      ExecStmts evm funs V st (emitStmt c {} env.length (.storeMap f k val)).stmts V st' .normal ∧
      Inv Γ c κ ctx w' env V st' := by
  rcases hinv with ⟨hV, henv, hR, hctx⟩
  rcases hR with ⟨hs, hl, hκe, hW⟩
  have hwf' : (fieldKindOK c f .map1 = true ∧ atomWF k = true) ∧ atomWF val = true := by
    simpa [stmtWF, Bool.and_eq_true] using hwf
  have ⟨fd, hfd, hknd⟩ := (fieldKindOK_iff c f FieldKind.map1).mp hwf'.1.1
  have hk := atom_eval_lt henv hwf'.1.2
  have hv := atom_eval_lt henv hwf'.2
  have hfB := field_lt_wordBound hlen hfd
  have hek := eval_atom funs (st := st) hV hn k
  obtain ⟨stP, hexecP, hmem, hmP⟩ := mapSlotPrep_exec funs V st f hek hfB
  have hhash :
      stP.env.keccakOf (readBytes stP.memory 0 64) = mapSlot1 κ f (k.eval env) :=
    mapSlotPrep_hash (st := st) κ (k.eval env) f hk hfB hκe rfl hmem
      (by rcases hmP with ⟨_, _, _, _, _, _, _, _, hκeq, _, _⟩; exact hκeq)
  have hev := eval_atom funs (st := stP) hV hn val
  have hctxP := ctxRel_memOnly hctx hmP
  have hstatic := ctxRel_static hctxP
  let stK := touchMemory stP 0 64
  have hekecc := eval_keccak064 funs V stP
  rw [hhash] at hekecc
  have hsstore :
      EvalExpr evm funs V stP (bop Op.sstore [keccak064, atomE env.length val])
        (.vals []
          { stK with
            storage := upd stK.storage (mapSlot1 κ f (k.eval env))
              (BitVec.ofNat 256 (val.eval env))
            env := { stK.env with
              storageOf := updAccount stK.env.storageOf stK.env.address
                (mapSlot1 κ f (k.eval env)) (BitVec.ofNat 256 (val.eval env)) } }) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hev) hekecc)
      (by
        have hstaticK : stK.env.static = false := by simp [stK, touchMemory, hstatic]
        simp only [stK, step_sstore (touchMemory stP 0 64) _ _ hstaticK])
  let st' :=
    { stK with
      storage := upd stK.storage (mapSlot1 κ f (k.eval env))
        (BitVec.ofNat 256 (val.eval env))
      env := { stK.env with
        storageOf := updAccount stK.env.storageOf stK.env.address
          (mapSlot1 κ f (k.eval env)) (BitVec.ofNat 256 (val.eval env)) } }
  have hexpr :
      ExecStmt evm funs V stP
        (.exprStmt (bop Op.sstore [keccak064, atomE env.length val])) V st' .normal :=
    Step.exprStmt hsstore
  refine ⟨st', ?_, ?_⟩
  · rw [emitStmt_storeMap]
    exact execStmts_append hexecP (Step.seqCons hexpr Step.seqNil)
  · have hmK : MemOnly st stK := MemOnly.trans hmP (memOnly_touch stP 0 64)
    have hRK : R c Γ κ w stK := R_memOnly ⟨hs, hl, hκe, hW⟩ hmK
    exact ⟨hV, henv, R_sstoreMap hRK (ctxRel_memOnly hctx hmK) hΓ hκ hlen hwf'.1.1 hk hv,
      ctxRel_sstore (ctxRel_memOnly hctx hmK) _ _⟩

end Lsc.Compiler
