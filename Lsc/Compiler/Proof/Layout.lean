import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.Words
import Lsc.Compiler.Proof.Env
import Lsc.Compiler.Proof.Memory
import YulSemantics.Dialect.EVM

/-!
Layout / `Inv` lemmas for `toYulFn_correct` (M1: scalar `sstore`, one-word `log1`).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- Simulation invariant: Yul `VEnv` is `toVEnv env`, locals are words, `R` and `ctxRel` hold. -/
structure Inv {S X E ε} (Γ : ContractSchema S X E ε) (c : ContractDef)
    (κ : List UInt8 → U256) (ctx : Ctx) (w : World S X E)
    (env : List Nat) (V : VEnv evm) (st : EvmState) : Prop where
  venv : V = toVEnv env
  wf : EnvWF env
  rel : R c Γ κ w st
  ctxr : ctxRel ctx st

def MemOnly (st st' : EvmState) : Prop :=
  st'.storage = st.storage ∧
  st'.logs = st.logs ∧
  st'.env.caller = st.env.caller ∧
  st'.env.callvalue = st.env.callvalue ∧
  st'.env.timestamp = st.env.timestamp ∧
  st'.env.number = st.env.number ∧
  st'.env.address = st.env.address ∧
  st'.env.static = st.env.static ∧
  st'.env.keccakOf = st.env.keccakOf ∧
  st'.env.calldata = st.env.calldata ∧
  st'.halted = st.halted

theorem ctxRel_memOnly {ctx st st'} (h : ctxRel ctx st) (hm : MemOnly st st') :
    ctxRel ctx st' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, hcd, hwf⟩
  rcases hm with ⟨_, _, hc, hv, ht, hn, ha, hs, _, hcall, hh⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf⟩
  · rw [hc, h1]
  · rw [hv, h2]
  · rw [ht, h3]
  · rw [hn, h4]
  · rw [ha, h5]
  · rw [hs, h6]
  · rw [hh, h7]
  · rw [hcall]; exact hcd

theorem selfLogs_eq_of_all_self (st : EvmState)
    (h : ∀ l ∈ st.logs, l.address = st.env.address) :
    selfLogs st = st.logs :=
  List.filter_eq_self.mpr (fun l hl => by simp [h l hl])

/-- When every log is ours, the address filter is a no-op. S1 emit/store proofs use this. -/
theorem logsRel_of_self {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} {st : EvmState}
    (h : List.Forall₂ (fun ev l =>
        ∃ i args, ev = Γ.ev.build i args ∧ ∃ hi : i < c.events.length,
          l = LogEntry.mk st.env.address
            [BitVec.ofNat 256 (c.events[i]).topic0] (abiBytes args))
      w.log st.logs)
    (hall : ∀ l ∈ st.logs, l.address = st.env.address) :
    logsRel c Γ w st := by
  unfold logsRel
  rwa [selfLogs_eq_of_all_self st hall]

theorem selfLogs_memOnly {st st' : EvmState} (hm : MemOnly st st') :
    selfLogs st' = selfLogs st := by
  rcases hm with ⟨_, hl, _, _, _, _, ha, _, _, _, _⟩
  simp [selfLogs, hl, ha]

theorem logsRel_memOnly {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} {st st'} (h : logsRel c Γ w st) (hm : MemOnly st st') :
    logsRel c Γ w st' := by
  rcases hm with ⟨_, hl, _, _, _, _, ha, _, _, _, _⟩
  unfold logsRel selfLogs at h ⊢
  rw [hl, ha]
  exact h

theorem R_memOnly {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st st'} (h : R c Γ κ w st) (hm : MemOnly st st') :
    R c Γ κ w st' := by
  rcases h with ⟨hs, hl, hk, hwf⟩
  have hm' := hm
  rcases hm with ⟨hsto, _, _, _, _, _, _, _, hκ, _, _⟩
  refine ⟨?_, logsRel_memOnly hl hm', ?_, hwf⟩
  · simpa [hsto] using hs
  · rw [hκ, hk]

theorem Inv_memOnly {S X E ε} {Γ : ContractSchema S X E ε} {c κ ctx w env V st st'}
    (h : Inv Γ c κ ctx w env V st) (hm : MemOnly st st') :
    Inv Γ c κ ctx w env V st' :=
  ⟨h.venv, h.wf, R_memOnly h.rel hm, ctxRel_memOnly h.ctxr hm⟩

theorem ctxRel_static {ctx st} (h : ctxRel ctx st) : st.env.static = false := by
  rcases h with ⟨_, _, _, _, _, hs, _, _, _⟩
  exact hs

theorem ctxRel_halted {ctx st} (h : ctxRel ctx st) : st.halted = none := by
  rcases h with ⟨_, _, _, _, _, _, hh, _, _⟩
  exact hh

theorem ctxRel_calldata_lt {ctx st} (h : ctxRel ctx st) :
    st.env.calldata.length < wordBound := by
  rcases h with ⟨_, _, _, _, _, _, _, hcd, _⟩
  exact hcd

theorem atom_eval_lt {env a} (hwf : EnvWF env) (ha : atomWF a = true) :
    a.eval env < wordBound := by
  cases a with
  | var i =>
    if hi : i < env.length then
      simp only [Atom.eval]
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact hwf _ (List.getElem_mem hi)
    else
      simp only [Atom.eval, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      exact zero_lt_wordBound
  | lit n =>
    simp only [atomWF, decide_eq_true_eq] at ha
    simpa [Atom.eval] using ha

theorem field_lt_wordBound {c : ContractDef} (hlen : c.fields.length < wordBound)
    {i : Nat} {fd : FieldDef} (h : c.fields[i]? = some fd) : i < wordBound :=
  Nat.lt_trans (List.getElem?_eq_some_iff.mp h).1 hlen

theorem storageRel_store {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ σ} {storage : U256 → U256}
    (hR : storageRel c Γ κ σ storage) (hΓ : Γ.st.Lawful c.fields)
    (hκ : KeccakSep c κ) (hlen : c.fields.length < wordBound)
    {f v : Nat} (hok : fieldKindOK c f .scalar = true) (_hv : v < wordBound) :
    storageRel c Γ κ (Γ.st.scalarUpd f σ v)
      (upd storage (BitVec.ofNat 256 f) (BitVec.ofNat 256 v)) := by
  intro i fd hi
  have ⟨fd', hf, hk⟩ := (fieldKindOK_iff c f .scalar).mp hok
  have hiB := field_lt_wordBound hlen hi
  have hfB := field_lt_wordBound hlen hf
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar := by
    simp [hf, hk]
  cases hkind : fd.kind with
  | scalar =>
    simp only [upd]
    split_ifs with hslot
    · have heq : i = f := ofNat_inj_of_lt hiB hfB hslot
      subst heq
      rw [hΓ.scalar_scalar i i σ v hfkind, if_pos rfl]
    · have hne : i ≠ f := fun he => hslot (he ▸ rfl)
      rw [hΓ.scalar_scalar i f σ v hfkind, if_neg hne]
      have := hR i fd hi
      simp [hkind] at this
      exact this
  | map1 =>
    intro k hkB
    have hne : mapSlot1 κ i k ≠ BitVec.ofNat 256 f :=
      hκ.map1_ne_scalar (List.getElem?_eq_some_iff.mp hi).1
        (List.getElem?_eq_some_iff.mp hf).1 hkB
        (by simp [hi, hkind]) hfkind
    simp [upd, hne]
    rw [hΓ.scalar_map1 i f σ v hfkind]
    have this := hR i fd hi
    simp [hkind] at this
    exact this k hkB
  | map2 =>
    intro k₁ k₂ hk1 hk2
    have hne : mapSlot2 κ i k₁ k₂ ≠ BitVec.ofNat 256 f :=
      hκ.map2_ne_scalar (List.getElem?_eq_some_iff.mp hi).1
        (List.getElem?_eq_some_iff.mp hf).1 hk1 hk2
        (by simp [hi, hkind]) hfkind
    simp [upd, hne]
    rw [hΓ.scalar_map2 i f σ v hfkind]
    have this := hR i fd hi
    simp [hkind] at this
    exact this k₁ k₂ hk1 hk2

theorem worldWF_store {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} (h : WorldWF c Γ w) (hΓ : Γ.st.Lawful c.fields)
    {f v : Nat} (hok : fieldKindOK c f .scalar = true) (hv : v < wordBound) :
    WorldWF c Γ { w with self := Γ.st.scalarUpd f w.self v } := by
  intro i fd hi
  have ⟨fd', hf, hk⟩ := (fieldKindOK_iff c f .scalar).mp hok
  have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar := by
    simp [hf, hk]
  have hold := h i fd hi
  cases hkind : fd.kind with
  | scalar =>
    simp [hkind] at hold ⊢
    rw [hΓ.scalar_scalar i f w.self v hfkind]
    split_ifs
    · exact hv
    · exact hold
  | map1 =>
    simp [hkind] at hold ⊢
    rw [hΓ.scalar_map1 i f w.self v hfkind]
    exact hold
  | map2 =>
    simp [hkind] at hold ⊢
    rw [hΓ.scalar_map2 i f w.self v hfkind]
    exact hold

theorem forall₂_append {α β} {R : α → β → Prop} :
    ∀ {l₁ l₂ l₁' l₂'}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁' l₂' →
      List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha t, h => .cons ha (forall₂_append t h)

theorem selfLogs_append_self (st : EvmState) (l : LogEntry)
    (haddr : l.address = st.env.address) :
    selfLogs { st with logs := st.logs ++ [l] } = selfLogs st ++ [l] := by
  simp [selfLogs, List.filter_append, haddr]

theorem logsRel_emit {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {w : World S X E} {st : EvmState} {i : Nat} {args : List Nat}
    (h : logsRel c Γ w st) (hev : i < c.events.length) :
    logsRel c Γ { w with log := w.log ++ [Γ.ev.build i args] }
      { st with logs := st.logs ++
        [LogEntry.mk st.env.address [BitVec.ofNat 256 (c.events[i]).topic0] (abiBytes args)] } := by
  unfold logsRel at h ⊢
  have hl :=
    selfLogs_append_self st
      (LogEntry.mk st.env.address [BitVec.ofNat 256 (c.events[i]).topic0] (abiBytes args)) rfl
  rw [hl]
  refine forall₂_append h (List.Forall₂.cons ?_ .nil)
  exact ⟨i, args, rfl, hev, rfl⟩

theorem R_halted_update {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState}
    (h : R c Γ κ w st) (h' : Option (HaltKind × List UInt8)) :
    R c Γ κ w { st with halted := h' } := by
  rcases h with ⟨hs, hl, hk, hwf⟩
  exact ⟨hs, hl, hk, hwf⟩

theorem R_rollback_obs {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st0 st' : EvmState} {k bytes}
    (hR : R c Γ κ w st0) (hh : st'.halted = some (k, bytes)) (hk : k.commits = false) :
    R c Γ κ w (committedState st0 st') := by
  rw [committedState_rollback hh hk]
  rcases hR with ⟨hs, hl, hk', hwf⟩
  exact ⟨hs, hl, hk', hwf⟩

theorem ctxRel_sstore {ctx st} (h : ctxRel ctx st) (k v : U256) :
    ctxRel ctx
      { st with
        storage := upd st.storage k v
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address k v } } := by
  rcases h with ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩
  exact ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩

theorem ctxRel_touch {ctx st} (h : ctxRel ctx st) (p n : Nat) :
    ctxRel ctx (touchMemory st p n) := by
  rcases h with ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩
  exact ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩

theorem ctxRel_appendLog {ctx st} (h : ctxRel ctx st) (topics : List U256) (p n : U256) :
    ctxRel ctx (appendLog st topics p n) := by
  rcases h with ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩
  simp [appendLog, touchMemory]
  exact ⟨h1, h2, h3, h4, h5, hs, hh, hcd, hwf⟩

theorem memOnly_touch (st : EvmState) (p n : Nat) : MemOnly st (touchMemory st p n) := by
  simp [MemOnly, touchMemory]

theorem MemOnly.trans {st1 st2 st3} (h12 : MemOnly st1 st2) (h23 : MemOnly st2 st3) :
    MemOnly st1 st3 := by
  rcases h12 with ⟨a, b, c, d, e, f, g, h, i, j, k⟩
  rcases h23 with ⟨a', b', c', d', e', f', g', h', i', j', k'⟩
  exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d, e'.trans e, f'.trans f,
    g'.trans g, h'.trans h, i'.trans i, j'.trans j, k'.trans k⟩

theorem R_touch_halted {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState}
    (h : R c Γ κ w st) (p n : Nat) (h' : Option (HaltKind × List UInt8)) :
    R c Γ κ w { touchMemory st p n with halted := h' } :=
  R_halted_update (R_memOnly h (memOnly_touch st p n)) h'


theorem R_sstore {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {st : EvmState} {f v : Nat}
    (hR : R c Γ κ w st) (_hctx : ctxRel ctx st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hok : fieldKindOK c f .scalar = true) (hv : v < wordBound) :
    R c Γ κ { w with self := Γ.st.scalarUpd f w.self v }
      { st with
        storage := upd st.storage (BitVec.ofNat 256 f) (BitVec.ofNat 256 v)
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address
            (BitVec.ofNat 256 f) (BitVec.ofNat 256 v) } } := by
  rcases hR with ⟨hs, hl, hk, hwf⟩
  refine ⟨?_, ?_, ?_, worldWF_store hwf hΓ hok hv⟩
  · exact storageRel_store hs hΓ hκ hlen hok hv
  · unfold logsRel at hl ⊢; exact hl
  · exact hk

end Lsc.Compiler
