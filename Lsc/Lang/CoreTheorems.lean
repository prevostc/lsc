import Lsc.Lang.Core
import Lsc.Lang.CoreProof

/-!
Frame facts for the Core IR: a successful (or reverting) run cannot change
a storage field the function never writes.

Contract authors use these so a bound token address, an owner slot, or an
allowance mapping stays put without a per-entrypoint lemma. Shared
assumption: if the function CALLs out, the callee is assumed not to write
our storage — the IERC20 non-interference hypothesis.
-/

namespace Lsc

variable {S X E ε : Type}

/-- A successful primitive step — a load, an add, a context word, a CALL —
never changes our storage, provided a CALL's callee is assumed not to
write us. Field-immutability for whole functions is built on this leaf. -/
theorem Op.effects_frame {Γ : ContractSchema S X E ε} (op : Op) (env : List Nat)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E}
    (h : Tx.run (Op.denote Γ env op) ctx w = .ok (v, w')) :
    w'.self = w.self :=
  Proof.Op.effects_frame op env hCall h

/-- If a statement never stores to a given field, a successful run of that
statement leaves any observation of that field unchanged — a scalar, a
whole mapping, a bound address. Mapping stores to a different field must
not alias it, and CALLs must not write us. Bound-address slots that no
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

/-- If a statement never stores to a given scalar slot, a successful run
leaves that word unchanged. Mapping stores are required not to alias the
slot, which a lawful storage layout guarantees. CALLs must not write us. -/
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

/-- If a whole function body never stores to a given field, a successful
run leaves any observation of that field unchanged. This is the theorem
that replaces handwritten "this entrypoint does not touch X" lemmas.
CALLs must still be assumed not to write our storage. -/
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

/-- A successful function run does not change a scalar slot unless the
function stores to it. Used to freeze bound callee addresses that no
runtime function ever writes, so Vault's asset token cannot silently
become a different address. -/
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

/-- A successful function run does not change a one-key mapping unless the
function writes that mapping. Token uses this so a call that never
touches allowances cannot change allowance slots in EVM storage. -/
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

/-- Same as `effects_frame_map1` for a nested mapping (two hash layers).
Needed when a field such as Token allowances is not written and must be
shown identical after the call. -/
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

/-- Whether the function reverts or succeeds, a run does not change an
observation of a field it never stores to. Unlike `effects_frame_on`
this covers the revert path as well — a failed CALL still leaves the
bound token address untouched. -/
theorem worldAfter_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hCall : ∀ b m args ctx w v w',
      Tx.run (Γ.ext.call b m args) ctx w = .ok (v, w') → w'.self = w.self)
    (hf : f ∉ (Core.effects c).writes)
    (ctx : Ctx) (w : World S X E) :
    P (Lang.worldAfter (Core.denote Γ c env) ctx w).self = P w.self :=
  Proof.worldAfter_frame_on c env f P hStore hStoreMap hStoreMap2 hCall hf ctx w

end Lsc
