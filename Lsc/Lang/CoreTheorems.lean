import Lsc.Lang.Core
import Lsc.Lang.CoreProof

/-!
Frame theorems for `Core.effects`: a successful run cannot change a storage
projection that is not in the write set. Per-entrypoint "this field is
immutable" facts are instances of these, not bespoke proofs.
-/

namespace Lsc

variable {S X E ε : Type}

/-- A successful primitive never writes `self`. Loads, arithmetic, and context
words are pure in storage; a CALL is allowed only under the hypothesis that
the callee model does not mutate our storage (`hCall`). This is the leaf of
the generic frame theorem: field-immutability proofs never reopen `Op.denote`. -/
theorem Op.effects_frame {Γ : ContractSchema S X E ε} (op : Op) (env : List Nat)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E}
    (h : Tx.run (Op.denote Γ env op) ctx w = .ok (v, w')) :
    w'.self = w.self :=
  Proof.Op.effects_frame op env hCall h

/-- If statement `s` does not list field index `f` among its writes, a successful
`Stmt.denote` leaves an arbitrary projection `P` of storage unchanged. Scalar
and mapping updaters are required to frame `P` when they target some other
index, and CALLs must not write `self`. Bound-address fields that no
entrypoint stores therefore stay fixed without a per-function lemma. -/
theorem Stmt.effects_frame_on {α} {Γ : ContractSchema S X E ε} (P : S → α)
    (s : Stmt) (env : List Nat) (f : Nat)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    P w'.self = P w.self :=
  Proof.Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hCall hf h

/-- Scalar specialisation of `Stmt.effects_frame_on`: a statement that does not
store to scalar slot `f` leaves that slot unchanged. Mapping stores are
required not to alias `f`, which generated `StorageSchema.Lawful` instances
discharge. -/
theorem Stmt.effects_frame {Γ : ContractSchema S X E ε} (s : Stmt) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Proof.Stmt.effects_frame s env f hΓ hMap1 hMap2 hCall hf h

/-- Generic Core frame: if field index `f` is absent from `Core.effects c`, a
successful `Core.denote` leaves projection `P` of `self` unchanged. This is
the theorem LANGUAGE_ARCHITECTURE uses in place of handwritten
`f_preserves_x` lemmas for every entrypoint. CALLs still require that the
external model not mutate our storage. -/
theorem effects_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    P w'.self = P w.self :=
  Proof.effects_frame_on c env f P hStore hStoreMap hStoreMap2 hCall hf h

/-- A successful Core run does not change scalar field `f` unless `f` is in the
write set. Used to freeze bound callee addresses that no runtime function
ever `sstore`s. -/
theorem effects_frame {Γ : ContractSchema S X E ε} {t} (c : Core t) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Proof.effects_frame c env f hΓ hMap1 hMap2 hCall hf h

/-- A successful Core run does not change mapping field `f` unless that mapping
is written. Token bytecode theorems use this so a call that never touches
`allowances` cannot change allowance slots in EVM storage. -/
theorem effects_frame_map1 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map1 f (Γ.st.scalarUpd i σ v) = Γ.st.map1 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map1Upd i σ m) = Γ.st.map1 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map2Upd i σ m) = Γ.st.map1 f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map1 f w'.self = Γ.st.map1 f w.self :=
  Proof.effects_frame_map1 c env f hΓ hMap1 hMap2 hCall hf h

/-- Same as `effects_frame_map1` for a nested mapping (two keccak layers). Needed
when a field such as Token `allowances[owner][spender]` is not in the write
set and must be shown identical in the post-state. -/
theorem effects_frame_map2 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map2 f (Γ.st.scalarUpd i σ v) = Γ.st.map2 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map1Upd i σ m) = Γ.st.map2 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map2Upd i σ m) = Γ.st.map2 f σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map2 f w'.self = Γ.st.map2 f w.self :=
  Proof.effects_frame_map2 c env f hΓ hMap1 hMap2 hCall hf h

/-- Revert or success: a Core run does not change projection `P` of `self` when
field `f` is not in the write set. Bind-address stability is this lemma plus
`coreAvoids`. -/
theorem worldAfter_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    (ctx : Ctx) (w : World S X E) :
    P (worldAfter (Core.denote Γ c env) ctx w).self = P w.self :=
  Proof.worldAfter_frame_on c env f P hStore hStoreMap hStoreMap2 hCall hf ctx w

end Lsc
