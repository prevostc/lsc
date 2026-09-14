import Lsc.Lang.Core

/-!
# `Tx.run` peeling lemmas

The simp / `obtain` set for a `Tx` program. Success-as-hypothesis forms
take `Tx.run f ctx w = .ok (r, w')` (or a concrete `c` / oracle `none`)
and conclude about `w'` or rewrite the `run`.

Already in `Lsc.Lang.Tx` (`RunLemmas`):

* `run_pure` / `run_bind` / `run_map` / `run_ite` / `bind_apply` / `map_apply`
* `run_load` / `run_loadMap` / `run_loadMap2`
* `run_store` / `run_storeMap` / `run_storeMap2`
* `run_require` / `run_require_true` / `run_require_false` / `require_iff`
* `run_revert` / `run_emit`
* `run_sender` / `run_value` / `run_timestamp` / `run_blockNumber` / `run_selfAddress`
* `run_addChecked` / `run_subChecked` / `run_mulChecked` / `run_divChecked`
* `run_ok_error` — `.ok` and `.error` of the same run are incompatible
* `run_ok_toOption` / `run_toOption_ok` / `run_toOption_iff` / `run_toOption_some`
  — `Tx.run = .ok` iff `(Tx.run).toOption = some` (`I.Impl` Fn fields)

In `Lsc.Lang.Word`: `run_mulDivDown` / `run_mulDivUp` / `run_pow10`.

In `Lsc.Lang.Amount`: `run_add` / `run_sub` / `run_mulScalar` / `run_divScalar`
/ `run_mulDivDown` / `run_mulDivUp`.

In `Lsc.Lang.Interface`: `run_call` / `run_view` / `run_tryCall` / `run_tryView`,
plus `run_call_ok` / `run_call_none` / `run_view_ok` / `run_view_none`, and
`run_call_toOption` / `run_call_toOption_err` (`I.Impl.ofRef` uses `ε := Unit`).

Schema-level aliases below match `Core.denote` of `Op.load` / `Stmt.store`.
-/

namespace Lsc.Tx

variable {S X E ε α : Type}

/-- Schema scalar load: the word at slot `i`, world unchanged. -/
@[simp] theorem run_read (Γ : ContractSchema S X E ε) (i : Nat) (ctx : Ctx)
    (w : World S X E) :
    run (load (X := X) (E := E) (ε := ε) (Γ.st.scalar i)) ctx w =
      .ok (Γ.st.scalar i w.self, w) :=
  run_load (Γ.st.scalar i) ctx w

/-- Schema one-key mapping load. -/
@[simp] theorem run_readMap (Γ : ContractSchema S X E ε) (i k : Nat)
    (ctx : Ctx) (w : World S X E) :
    run (loadMap (X := X) (E := E) (ε := ε) (Γ.st.map1 i) k) ctx w =
      .ok (Γ.st.map1 i w.self k, w) :=
  run_loadMap (Γ.st.map1 i) k ctx w

/-- Schema scalar store: update slot `i`, rest of the world unchanged. -/
@[simp] theorem run_write (Γ : ContractSchema S X E ε) (i : Nat) (v : Nat)
    (ctx : Ctx) (w : World S X E) :
    run (store (X := X) (E := E) (ε := ε) (Γ.st.scalarUpd i) v) ctx w =
      .ok ((), { w with self := Γ.st.scalarUpd i w.self v }) :=
  run_store (Γ.st.scalarUpd i) v ctx w

/-- Schema one-key mapping store. -/
@[simp] theorem run_writeMap (Γ : ContractSchema S X E ε) (i k v : Nat)
    (ctx : Ctx) (w : World S X E) :
    run (storeMap (X := X) (E := E) (ε := ε) (Γ.st.map1 i) (Γ.st.map1Upd i) k v)
      ctx w =
      .ok ((), { w with self :=
        (Γ.st.map1Upd i) w.self (Function.update (Γ.st.map1 i w.self) k v) }) :=
  run_storeMap (Γ.st.map1 i) (Γ.st.map1Upd i) k v ctx w

end Lsc.Tx
