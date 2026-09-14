import Lsc.Lang.Amount
import Lsc.Lang.WordProof
import Lsc.Lang.TxProof

/-!
Proofs of the checked-amount theorems, `Tx.run` unfolding lemmas, and
certificate bind lemmas. Statements live in `AmountTheorems.lean`.
-/

namespace Lsc
namespace Amount.Proof

variable {S X E ε : Type} {a b : Asset}

theorem run_add (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if x.raw + y.raw < wordBound then .ok (⟨x.raw + y.raw⟩, w)
      else .error (.arith .overflow) := by
  simp [add, Tx.Proof.run_map, Tx.Proof.run_addChecked]
  by_cases h : x.raw + y.raw < wordBound <;> simp [h, ofWord]

theorem run_sub (x y : Amount a) (ctx : Ctx) (w : World S X E) :
    Tx.run (sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      if y.raw ≤ x.raw then .ok (⟨x.raw - y.raw⟩, w)
      else .error (.arith .underflow) := by
  simp [sub, Tx.Proof.run_map, Tx.Proof.run_subChecked]
  by_cases h : y.raw ≤ x.raw <;> simp [h, ofWord]

theorem run_mulScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if x.raw * k < wordBound then .ok (⟨x.raw * k⟩, w)
      else .error (.arith .overflow) := by
  simp [mulScalar, Tx.Proof.run_map, Tx.Proof.run_mulChecked]
  by_cases h : x.raw * k < wordBound <;> simp [h, ofWord]

theorem run_divScalar (x : Amount a) (k : Word) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (divScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      if k ≠ 0 then .ok (⟨x.raw / k⟩, w)
      else .error (.arith .divByZero) := by
  simp [divScalar, Tx.Proof.run_map, Tx.Proof.run_divChecked]
  by_cases h : k = 0 <;> simp [h, ofWord]

theorem run_mulDivDown (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw⟩, w)
      else .error (.arith .overflow) := by
  simp [mulDivDown, Tx.Proof.run_map, Tx.Proof.run_mulDivDown]
  by_cases hy : y.raw = 0
  · simp [hy]
  · by_cases hfit : num.raw * x.raw < wordBound <;> simp [hy, hfit, ofWord]

theorem run_mulDivUp (num : Amount b) (x y : Amount a) (ctx : Ctx)
    (w : World S X E) :
    Tx.run (mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y) ctx w =
      if y.raw = 0 then .error (.arith .divByZero)
      else if num.raw * x.raw < wordBound then
        .ok (⟨num.raw * x.raw / y.raw +
          (if num.raw * x.raw % y.raw = 0 then 0 else 1)⟩, w)
      else .error (.arith .overflow) := by
  simp [mulDivUp, Tx.Proof.run_map, Tx.Proof.run_mulDivUp]
  by_cases hy : y.raw = 0
  · simp [hy]
  · by_cases hfit : num.raw * x.raw < wordBound <;> simp [hy, hfit, ofWord]

theorem load_bind_ofWord {β : Type} (proj : S → Amount a)
    (k : Amount a → Tx S X E ε β) :
    Tx.load (X := X) (E := E) (ε := ε) proj >>= k =
      Tx.load (fun σ => (proj σ).raw) >>= fun n => k (ofWord n) := by
  funext ctx w
  simp [Tx.load, bind, ReaderT.bind, StateT.bind, Except.bind, ofWord, mk_raw]

theorem loadMap_bind_ofWord {K β : Type} (proj : S → K → Amount a) (key : K)
    (k : Amount a → Tx S X E ε β) :
    Tx.loadMap (X := X) (E := E) (ε := ε) proj key >>= k =
      Tx.loadMap (fun σ i => (proj σ i).raw) key >>= fun n => k (ofWord n) := by
  funext ctx w
  simp [Tx.loadMap, bind, ReaderT.bind, StateT.bind, Except.bind, ofWord, mk_raw]

theorem loadMap2_bind_ofWord {K₁ K₂ β : Type} (proj : S → K₁ → K₂ → Amount a)
    (k₁ : K₁) (k₂ : K₂) (k : Amount a → Tx S X E ε β) :
    Tx.loadMap2 (X := X) (E := E) (ε := ε) proj k₁ k₂ >>= k =
      Tx.loadMap2 (fun σ i j => (proj σ i j).raw) k₁ k₂ >>=
        fun n => k (ofWord n) := by
  funext ctx w
  simp [Tx.loadMap2, bind, ReaderT.bind, StateT.bind, Except.bind, ofWord, mk_raw]

theorem add_bind_ofWord {β : Type} (x y : Amount a)
    (k : Amount a → Tx S X E ε β) :
    add (S := S) (X := X) (E := E) (ε := ε) x y >>= k =
      Tx.addChecked x.raw y.raw >>= fun n => k (ofWord n) := by
  simp [add]

theorem sub_bind_ofWord {β : Type} (x y : Amount a)
    (k : Amount a → Tx S X E ε β) :
    sub (S := S) (X := X) (E := E) (ε := ε) x y >>= k =
      Tx.subChecked x.raw y.raw >>= fun n => k (ofWord n) := by
  simp [sub]

theorem mulDivDown_bind_ofWord {β : Type} (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx S X E ε β) :
    mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y >>= k =
      Tx.mulDivDown num.raw x.raw y.raw >>= fun n => k (ofWord n) := by
  simp [mulDivDown]

theorem mulDivUp_bind_ofWord {β : Type} (num : Amount b) (x y : Amount a)
    (k : Amount b → Tx S X E ε β) :
    mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y >>= k =
      Tx.mulDivUp num.raw x.raw y.raw >>= fun n => k (ofWord n) := by
  simp [mulDivUp]

theorem require_pos (x : Amount a) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (0 < x) err =
      Tx.require (0 < x.raw) err :=
  Tx.Proof.require_iff err (by simp [lt_iff])

theorem require_lt_ofWord (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (0 < ofWord (a := a) n) err =
      Tx.require (0 < n) err :=
  Tx.Proof.require_iff err (by simp [lt_iff, ofWord])

theorem require_le_ofWord (x : Amount a) (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (x ≤ ofWord n) err =
      Tx.require (x.raw ≤ n) err :=
  Tx.Proof.require_iff err (by simp [le_iff, ofWord])

theorem require_eq_zero_ofWord (n : Word) (err : ε) :
    Tx.require (S := S) (X := X) (E := E) (ofWord (a := a) n = 0) err =
      Tx.require (n = 0) err :=
  Tx.Proof.require_iff err (ofWord_eq_zero n)

theorem ite_eq_zero_ofWord {β : Type} (n : Word)
    (t e : Tx S X E ε β) :
    (if ofWord (a := a) n = 0 then t else e) = (if n = 0 then t else e) :=
  ite_congr (propext (ofWord_eq_zero n)) (fun _ => rfl) (fun _ => rfl)

theorem add_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.add (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw + y.raw ∧ x.raw + y.raw < wordBound ∧ w' = w := by
  simp [run_add] at h
  by_cases hfit : x.raw + y.raw < wordBound
  · simp [hfit] at h
    exact ⟨congrArg Amount.raw h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem sub_ok {x y : Amount a} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.sub (S := S) (X := X) (E := E) (ε := ε) x y) ctx w =
      .ok (q, w')) :
    q.raw = x.raw - y.raw ∧ y.raw ≤ x.raw ∧ w' = w := by
  simp [run_sub] at h
  by_cases hle : y.raw ≤ x.raw
  · simp [hle] at h
    exact ⟨congrArg Amount.raw h.1.symm, hle, h.2.symm⟩
  · simp [hle] at h

theorem mulScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.mulScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      .ok (q, w')) :
    q.raw = x.raw * k ∧ x.raw * k < wordBound ∧ w' = w := by
  simp [run_mulScalar] at h
  by_cases hfit : x.raw * k < wordBound
  · simp [hfit] at h
    exact ⟨congrArg Amount.raw h.1.symm, hfit, h.2.symm⟩
  · simp [hfit] at h

theorem divScalar_ok {x : Amount a} {k : Word} {ctx : Ctx} {w : World S X E}
    {q : Amount a} {w' : World S X E}
    (h : Tx.run (Amount.divScalar (S := S) (X := X) (E := E) (ε := ε) x k) ctx w =
      .ok (q, w')) :
    q.raw = x.raw / k ∧ k ≠ 0 ∧ w' = w := by
  simp [run_divScalar] at h
  by_cases hk : k = 0
  · simp [hk] at h
  · simp [hk] at h
    exact ⟨congrArg Amount.raw h.1.symm, hk, h.2.symm⟩

private theorem run_word_mulDivDown {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    Tx.run (Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num.raw x.raw y.raw)
      ctx w = .ok (q.raw, w') := by
  simp [run_mulDivDown] at h
  by_cases hy0 : y.raw = 0
  · simp [hy0] at h
  · by_cases hfit : num.raw * x.raw < wordBound
    · simp [hy0, hfit] at h
      simp [Tx.Proof.run_mulDivDown, hy0, hfit, congrArg Amount.raw h.1.symm, h.2.symm]
    · simp [hy0, hfit] at h

private theorem run_word_mulDivUp {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    Tx.run (Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num.raw x.raw y.raw)
      ctx w = .ok (q.raw, w') := by
  simp [run_mulDivUp] at h
  by_cases hy0 : y.raw = 0
  · simp [hy0] at h
  · by_cases hfit : num.raw * x.raw < wordBound
    · simp [hy0, hfit] at h
      simp [Tx.Proof.run_mulDivUp, hy0, hfit, congrArg Amount.raw h.1.symm, h.2.symm]
    · simp [hy0, hfit] at h

theorem mulDivDown_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivDown (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧ q.raw = num.raw * x.raw / y.raw ∧
      q.raw * y.raw ≤ num.raw * x.raw ∧
      num.raw * x.raw - q.raw * y.raw < y.raw ∧ w' = w :=
  Lsc.Proof.mulDivDown_ok (run_word_mulDivDown h)

theorem mulDivUp_ok {num : Amount b} {x y : Amount a} {ctx : Ctx}
    {w : World S X E} {q : Amount b} {w' : World S X E}
    (h : Tx.run (Amount.mulDivUp (S := S) (X := X) (E := E) (ε := ε) num x y)
      ctx w = .ok (q, w')) :
    y.raw ≠ 0 ∧ num.raw * x.raw < wordBound ∧
      q.raw = num.raw * x.raw / y.raw +
        (if num.raw * x.raw % y.raw = 0 then 0 else 1) ∧
      num.raw * x.raw ≤ q.raw * y.raw ∧ w' = w :=
  Lsc.Proof.mulDivUp_ok (run_word_mulDivUp h)

end Amount.Proof

namespace Lang.Proof

variable {S X E ε : Type}

theorem worldAfter_ofWord {a : Asset} (x : Tx S X E ε Nat)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (Amount.ofWord (a := a) <$> x) ctx w :=
  (worldAfter_map (Amount.ofWord (a := a)) x ctx w).symm

theorem worldAfter_amountProd {a b : Asset} (x : Tx S X E ε (Nat × Nat))
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w =
      worldAfter ((fun v =>
        (Amount.ofWord (a := a) v.1, Amount.ofWord (a := b) v.2)) <$> x) ctx w :=
  (worldAfter_map (fun v =>
    (Amount.ofWord (a := a) v.1, Amount.ofWord (a := b) v.2)) x ctx w).symm

end Lang.Proof
end Lsc
