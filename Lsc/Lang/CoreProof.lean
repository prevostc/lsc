import Lsc.Lang.Core

/-!
Frame theorem for `Core.effects`. Extra hypotheses beyond the blueprint's `hΓ`:
mapping updates (`hMap1`/`hMap2`) and `ext.call` not mutating `self` (`hCall`).
Generated schemas satisfy the mapping facts via `StorageSchema.Lawful`.
-/

namespace Lsc

variable {S X E ε : Type}

/-- A successful run does not change scalar field `f` unless `f` is in `writes`. -/
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
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self := by
  sorry

end Lsc
