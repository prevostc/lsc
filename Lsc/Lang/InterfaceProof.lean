import Lsc.Lang.Interface
import Lsc.Lang.TxProof

/-!
Proofs of CALL / view run lemmas and Core-word certificate
equalities. Statements live in `InterfaceTheorems.lean`.
-/

namespace Lsc.Tx.Proof

section CallRun
variable {S X E ε α : Type} [AbiRetType α]

theorem run_call (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .error .callFailed
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .error .callFailed
        | some v => .ok (v, { w with ext := x' }) :=
  rfl

theorem call_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (call (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (call (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

theorem run_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .error .callFailed
      | some v => .ok (v, w) :=
  rfl

theorem view_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (view (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (view (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

/-- A successful CALL: the oracle returned a decodable payload and `ext`
was updated. -/
theorem run_call_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    ∃ rets x', w.oracle.call addr sel args w.ext = some (rets, x') ∧
      AbiRetType.decode (α := α) rets = some v ∧
      w' = { w with ext := x' } := by
  simp only [run_call] at h
  cases hcall : w.oracle.call addr sel args w.ext with
  | none =>
    simp [hcall] at h
  | some pair =>
    rcases pair with ⟨rets, x'⟩
    simp [hcall] at h
    cases hdec : AbiRetType.decode (α := α) rets with
    | none =>
      simp [hdec] at h
    | some v' =>
      simp [hdec] at h
      rcases h with ⟨hv, hw⟩
      subst hv
      exact ⟨rets, x', rfl, hdec, hw.symm⟩

/-- Oracle `none` is `.callFailed`. -/
theorem run_call_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : w.oracle.call addr sel args w.ext = none) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed := by
  simp [run_call, h]

/-- `toOption` of a CALL is the decoded oracle payload (or `none`). Independent
of the user-error type. -/
theorem run_call_toOption (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (run (call (ε := ε) (α := α) addr sel args) ctx w).toOption =
      match w.oracle.call addr sel args w.ext with
      | none => none
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => none
        | some v => some (v, { w with ext := x' }) := by
  simp only [run_call]
  split
  · rfl
  · split <;> rfl

/-- `toOption` of a CALL ignores the user-error type. A contract body uses the
contract's `Error`; `I.Impl.ofRef` reconstructs the same oracle CALL on a
`WorldView` without threading `ε`. -/
theorem run_call_toOption_err {ε' : Type} (addr : Address) (sel : Nat)
    (args : List Word) (ctx : Ctx) (w : World S X E) :
    (run (call (ε := ε) (α := α) addr sel args) ctx w).toOption =
      (run (call (ε := ε') (α := α) addr sel args) ctx w).toOption := by
  rw [run_call_toOption, run_call_toOption]

/-- `WorldView.callDecode` on `w.view` is `Tx.run (call …)` mapped onto the
view. -/
theorem callDecode_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    WorldView.callDecode (α := α) w.view addr sel args =
      (Tx.run (call (ε := ε) (α := α) addr sel args) ctx w).toOption.map
        (Prod.map id World.view) := by
  simp only [WorldView.callDecode, World.view_oracle, World.view_ext]
  rw [run_call_toOption]
  cases w.oracle.call addr sel args w.ext with
  | none => simp
  | some p =>
    cases p with
    | mk rets x' =>
      simp
      cases _hdec : AbiRetType.decode (α := α) rets with
      | none => simp
      | some _ret => simp [Prod.map, World.view]

/-- A successful view: the oracle payload decoded and the world is unchanged. -/
theorem run_view_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = some v ∧
      w' = w := by
  simp only [run_view] at h
  split at h
  · cases h
  · next hv =>
    cases h
    exact ⟨hv, rfl⟩

/-- Decode failure on a view is `.callFailed`; the world is unchanged. -/
theorem run_view_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = none) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed := by
  simp [run_view, h]

theorem run_tryCall (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .ok (.error .callFailed, w)
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .ok (.error .callFailed, w)
        | some v => .ok (.ok v, { w with ext := x' }) :=
  rfl

theorem tryCall_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (tryCall (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

theorem run_tryView (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryView (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, w) :=
  rfl

/-- A successful CALL leaves `self` unchanged (no reentrancy in this slice). -/
theorem call_self (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.self = w.self := by
  simp [run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

/-- A successful CALL leaves the oracle unchanged. -/
theorem call_oracle (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.oracle = w.oracle := by
  simp [run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

/-- A successful view returns the pre-world. -/
theorem view_world (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w' = w := by
  simp [run_view]
  split
  · intro h; cases h
  · intro h; cases h; rfl

end CallRun

section Wrappers
variable {S X E ε : Type}

theorem natToBool_boolBit (b : Bool) : natToBool (boolBit b) = b := by
  cases b <;> rfl

theorem natToBool_eq (n : Nat) : natToBool n = (n != 0) := rfl

theorem natToBool_eq_true (n : Nat) : natToBool n = true ↔ n ≠ 0 := by
  simp [natToBool]

theorem natToBool_zero : natToBool 0 = false := rfl
theorem natToBool_one : natToBool 1 = true := rfl

/-- `decide (n ≠ 0) = true` is `n ≠ 0`. Used when `require (ok = true)`
meets a `n != 0` decode. -/
theorem decide_ne_zero_eq_true (n : Nat) :
    decide (n ≠ 0) = true ↔ n ≠ 0 :=
  decide_eq_true_iff

theorem bne_zero_eq_true (n : Nat) : (n != 0) = true ↔ n ≠ 0 := by
  simp [bne]

theorem callAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  rfl

theorem viewAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  rfl

theorem boolBit_true : boolBit true = 1 := rfl
theorem boolBit_false : boolBit false = 0 := rfl

theorem boolBit_eq_one (b : Bool) : (boolBit b = 1) = (b = true) := by
  cases b <;> simp [boolBit]

theorem boolBit_beq_one (b : Bool) : (boolBit b == 1) = b := by
  cases b <;> rfl

/-- `require (ok = true)` is the Core bit-test `require (boolBit ok = 1)`. -/
theorem require_bool_eq_true_iff_bit (b : Bool) (err : ε) :
    require (S := S) (X := X) (E := E) (b = true) err =
      require (boolBit b = 1) err := by
  cases b <;> rfl

/-- Recover a `Bool` CALL from the Core-word wrapper. -/
theorem map_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  simp only [callAsNat]
  rw [map_eq_pure_bind, bind_map]
  simp only [natToBool_boolBit]
  exact bind_pure _

/-- `Tx.call` at `Bool` is `natToBool <$> callAsNat .boolOpt` (`n ≠ 0`). -/
theorem call_bool (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  (map_callAsNat_bool addr sel args).symm

/-- Recover a `Bool` view from the Core-word wrapper. -/
theorem map_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  simp only [viewAsNat]
  rw [map_eq_pure_bind, bind_map]
  simp only [natToBool_boolBit]
  exact bind_pure _

/-- `Tx.view` at `Bool` is `natToBool <$> viewAsNat .boolOpt`. -/
theorem view_bool (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  (map_viewAsNat_bool addr sel args).symm

/-- Bind form of `map_callAsNat_bool` (`simp` may rewrite `<$>` to `>>= pure`). -/
theorem bind_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_callAsNat_bool addr sel args

theorem bind_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_viewAsNat_bool addr sel args

theorem encode_address (a : Address) :
    AbiType.encode a = Address.toWord a :=
  rfl

theorem encode_amount {a : Asset} (x : Amount a) :
    AbiType.encode x = Amount.raw x :=
  rfl

theorem encode_word (w : Word) : AbiType.encode w = w :=
  rfl

theorem encode_bool (b : Bool) : AbiType.encode b = if b then 1 else 0 :=
  rfl

/-- `Address.toWord` is the identity; CALL targets from Core env atoms use it. -/
theorem callAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      callAsNat ret addr sel args :=
  rfl

theorem viewAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      viewAsNat ret addr sel args :=
  rfl

/-- Recover an `Amount` CALL from the Core-word wrapper. -/
theorem map_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (α := Amount a) addr sel args := by
  funext ctx w
  change Tx.run (Amount.ofWord (a := a) <$>
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args) ctx w =
    Tx.run (call (α := Amount a) addr sel args) ctx w
  simp only [callAsNat]
  rw [run_map, run_call (α := Nat), run_call (α := Amount a)]
  cases w.oracle.call addr sel args w.ext with
  | none => rfl
  | some p =>
    rcases p with ⟨rets, _x'⟩
    match rets with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- Recover an `Amount` view from the Core-word wrapper. -/
theorem map_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (α := Amount a) addr sel args := by
  funext ctx w
  change Tx.run (Amount.ofWord (a := a) <$>
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args) ctx w =
    Tx.run (view (α := Amount a) addr sel args) ctx w
  simp only [viewAsNat]
  rw [run_map, run_view (α := Nat), run_view (α := Amount a)]
  match w.oracle.view addr sel args w.ext with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- Certificate direction: surface `view` is Core `ofWord <$> viewAsNat`.
Lets `bind_map` + `raw_ofWord` turn an intermediate `ta.raw` into the Core
word (live `balanceOf` feeding `mulDiv`). -/
theorem view_eq_map_viewAsNat {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    view (α := Amount a) addr sel args =
      Amount.ofWord (a := a) <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args :=
  (map_viewAsNat_amount addr sel args).symm

/-- Bind form of `map_viewAsNat_amount`. -/
theorem bind_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      view (α := Amount a) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_viewAsNat_amount addr sel args

/-- Surface `view` then `k ta.raw` is Core `viewAsNat` then `k n`.
Simp-oriented: the surface mentions `Amount a`, so `a` is inferable. -/
theorem bind_viewAsNat_raw {a : Asset} {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (k : Nat → Tx S X E ε β) :
    view (α := Amount a) addr sel args >>= (fun ta => k ta.raw) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>= k := by
  rw [← map_viewAsNat_amount (a := a), bind_map]
  rfl

/-- Bind form of `map_callAsNat_amount`. -/
theorem bind_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      call (α := Amount a) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_callAsNat_amount addr sel args

/-- `f <$> (x >>= k)` with an Amount wrapper; named so certificate `simp` matches
after `Core.denote` of a `letOp` sequence. -/
theorem map_bind_ofWord {a : Asset} {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    Amount.ofWord (a := a) <$> (x >>= k) =
      x >>= fun b => Amount.ofWord (a := a) <$> k b :=
  map_bind (Amount.ofWord (a := a)) x k

/-- Pair-of-Amount wrap through `bind`. Certificate key for `Prod.map ofWord`. -/
theorem map_bind_ofWord_pair {a b : Asset} {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε (Nat × Nat)) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> (x >>= k) =
      x >>= fun v =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> k v :=
  map_bind (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) x k

/-- Discarded bind then pair-of-Amount wrap. -/
theorem map_discard_ofWord_pair {a b : Asset} {γ : Type} (x : Tx S X E ε γ)
    (y : Tx S X E ε (Nat × Nat)) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        (x >>= fun _ => y) =
      x >>= fun _ =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> y :=
  map_bind_ofWord_pair (a := a) (b := b) x (fun _ => y)

/-- `Prod.map ofWord` of a Core pair `pure`. -/
theorem map_pure_ofWord_pair {a b : Asset} (x y : Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        (pure (x, y) : Tx S X E ε (Nat × Nat)) =
      pure (Amount.ofWord (a := a) x, Amount.ofWord (a := b) y) :=
  map_pure (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))) (x, y)

/-- `natToBool <$> (x >>= k)` after `Core.denote` of a Bool-returning sequence. -/
theorem map_bind_natToBool {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    natToBool <$> (x >>= k) = x >>= fun b => natToBool <$> k b :=
  map_bind natToBool x k

/-- Push `ofWord` through `selfAddress >>= viewAsNat` (view after a storage load).
`addr` is `Nat` so `simp` matches Core `load (S → Nat)` binders; `Address := Nat`. -/
theorem map_bind_viewAsNat_amount {a : Asset} {β : Type}
    (x : Tx S X E ε β) (addr : Nat) (sel : Nat) (args : β → List Word) :
    Amount.ofWord (a := a) <$>
        (x >>= fun v => viewAsNat (S := S) (X := X) (E := E) (ε := ε)
          .word addr sel (args v)) =
      x >>= fun v => view (α := Amount a) addr sel (args v) := by
  rw [map_bind_ofWord]
  refine congrArg (fun k => x >>= k) ?_
  funext v
  exact map_viewAsNat_amount addr sel (args v)

/-- `Address.toWord` is the identity; Core env atoms of `selfAddress` omit it. -/
theorem view_toWord_arg {a : Asset} (addr : Address) (sel : Nat) (v : Address) :
    view (S := S) (X := X) (E := E) (ε := ε) (α := Amount a) addr sel [v.toWord] =
      view (α := Amount a) addr sel [v] :=
  rfl

/-- After `map_bind_ofWord`, ofWord sits on the inner `selfAddress >>= viewAsNat`. -/
theorem bind_load_inner_viewAsNat_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load proj >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  refine congrArg (fun k => load proj >>= k) ?_
  funext addr
  exact map_bind_viewAsNat_amount (a := a) (S := S) (X := X) (E := E) (ε := ε)
    selfAddress addr sel (fun me => [me])

/-- Same as `bind_load_inner_viewAsNat_amount` with an `Address` projection
(`Address := Nat`, but `simp` keys on the binder type). -/
theorem bind_load_inner_viewAsNat_amount_addr {a : Asset}
    (proj : S → Address) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load proj >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] :=
  bind_load_inner_viewAsNat_amount (fun σ => proj σ) sel

/-- Schema `getD` form of `bind_load_inner_viewAsNat_amount`. -/
theorem bind_load_getD_inner_viewAsNat_amount {a : Asset}
    (p : S → Nat) (rest : List (S → Nat)) (d : S → Nat) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) (List.getD (p :: rest) 0 d) >>=
        fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load p >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  have hproj : List.getD (p :: rest) 0 d = p := rfl
  rw [hproj]
  exact bind_load_inner_viewAsNat_amount p sel

/-- `getD [p, q]` with `Address` projections, as `lsc_schema` pretty-prints them. -/
theorem bind_load_getD_pair_addr_view_amount {a : Asset}
    (p q : S → Address) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε)
        (List.getD [p, q] 0 (fun _ => (0 : Address))) >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load p >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  have hproj : List.getD [p, q] 0 (fun _ => (0 : Address)) = p := rfl
  rw [hproj]
  exact bind_load_inner_viewAsNat_amount_addr p sel

/-- Load a callee address, then `selfAddress`, then an Amount view. -/
theorem load_selfAddress_view_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    Amount.ofWord (a := a) <$>
        (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
          selfAddress >>= fun me =>
            viewAsNat .word addr sel [me]) =
      load proj >>= fun addr =>
        selfAddress >>= fun me =>
          view (α := Amount a) addr sel [me.toWord] := by
  rw [map_bind_ofWord]
  trans (load proj >>= fun addr =>
    selfAddress >>= fun me =>
      view (S := S) (X := X) (E := E) (ε := ε) (α := Amount a) addr sel [me])
  · exact bind_load_inner_viewAsNat_amount (a := a) proj sel
  · refine congrArg (fun k => load proj >>= k) ?_
    funext addr
    refine congrArg (fun k => selfAddress >>= k) ?_
    funext me
    exact (view_toWord_arg (a := a) addr sel me).symm

/-- `require (ok = true)` after a Bool CALL is the Core `boolOpt` bit-test. -/
theorem callAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) := by
  have hreq :
      (fun ok : Bool => require (S := S) (X := X) (E := E) (ok = true) err) =
        fun ok => require (boolBit ok = 1) err := by
    funext ok
    exact require_bool_eq_true_iff_bit ok err
  rw [hreq]
  simp only [callAsNat]
  exact (bind_map boolBit (call (α := Bool) addr sel args)
    (fun n => require (n = 1) err)).symm

/-- `require (ok = true)` after a Bool view is the Core `boolOpt` bit-test. -/
theorem viewAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) := by
  have hreq :
      (fun ok : Bool => require (S := S) (X := X) (E := E) (ok = true) err) =
        fun ok => require (boolBit ok = 1) err := by
    funext ok
    exact require_bool_eq_true_iff_bit ok err
  rw [hreq]
  simp only [viewAsNat]
  exact (bind_map boolBit (view (α := Bool) addr sel args)
    (fun n => require (n = 1) err)).symm

/-- `require (ok = true)` then a continuation after a Bool CALL. -/
theorem callAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) := by
  have h := callAsNat_bool_bind_require (S := S) (X := X) (E := E)
    addr sel args err
  rw [← bind_assoc, h, bind_assoc]

/-- `require (ok = true)` then a continuation after a Bool view. -/
theorem viewAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) := by
  have h := viewAsNat_bool_bind_require (S := S) (X := X) (E := E)
    addr sel args err
  rw [← bind_assoc, h, bind_assoc]

/-- `require (ok = true)` after `sendRaw` matches Core `require (boolBit ok = 1)`. -/
theorem sendRaw_require_eq_true_iff_bit (to amount : Nat) (err : ε) :
    sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun ok => require (ok = true) err) =
      sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun a => require (boolBit a = 1) err) := by
  refine congrArg (fun k => sendRaw to amount >>= k) ?_
  funext ok
  exact require_bool_eq_true_iff_bit ok err

/-- Continuation form of `sendRaw_require_eq_true_iff_bit`. -/
theorem sendRaw_require_eq_true_iff_bit_bind {β : Type} (to amount : Nat)
    (err : ε) (k : Tx S X E ε β) :
    sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun a => require (boolBit a = 1) err >>= fun _ => k) := by
  refine congrArg (fun f => sendRaw to amount >>= f) ?_
  funext ok
  exact congrArg (fun r => r >>= fun _ => k)
    (require_bool_eq_true_iff_bit ok err)

/-- `require (ok = true)` after `sendRaw` is the Core `boolBit <$> sendRaw` bit-test. -/
theorem sendRaw_bool_bind_require (to amount : Nat) (err : ε) :
    sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun ok => require (ok = true) err) =
      (boolBit <$> sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount) >>=
        (fun n => require (n = 1) err) := by
  have hreq :
      (fun ok : Bool => require (S := S) (X := X) (E := E) (ok = true) err) =
        fun ok => require (boolBit ok = 1) err := by
    funext ok
    exact require_bool_eq_true_iff_bit ok err
  rw [hreq]
  exact (bind_map boolBit (sendRaw to amount)
    (fun n => require (n = 1) err)).symm

/-- `require (ok = true)` then a continuation after `sendRaw`. -/
theorem sendRaw_bool_bind_require_bind {β : Type} (to amount : Nat) (err : ε)
    (k : Tx S X E ε β) :
    sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      (boolBit <$> sendRaw (S := S) (X := X) (E := E) (ε := ε) to amount) >>=
        (fun n => require (n = 1) err >>= fun _ => k) := by
  have h := sendRaw_bool_bind_require (S := S) (X := X) (E := E) to amount err
  rw [← bind_assoc, h, bind_assoc]

/-- Discarded Bool CALL: Core `boolOpt` vs surface `Bool`. -/
theorem callAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) := by
  simp only [callAsNat]
  rw [bind_map]

/-- Discarded Bool view: Core `boolOpt` vs surface `Bool`. -/
theorem viewAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) := by
  simp only [viewAsNat]
  rw [bind_map]

/-- Discarded Amount view: Core `word` vs surface `Amount`. -/
theorem viewAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    view (α := Amount a) addr sel args >>= (fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) := by
  funext ctx w
  change Tx.run (view (α := Amount a) addr sel args >>= fun _ => k) ctx w =
    Tx.run (viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
      fun _ => k) ctx w
  simp only [viewAsNat]
  rw [run_bind, run_bind, run_view (α := Amount a), run_view (α := Nat)]
  match w.oracle.view addr sel args w.ext with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- Discarded Amount CALL: Core `word` vs surface `Amount`. -/
theorem callAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    call (α := Amount a) addr sel args >>= (fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) := by
  funext ctx w
  change Tx.run (call (α := Amount a) addr sel args >>= fun _ => k) ctx w =
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
      fun _ => k) ctx w
  simp only [callAsNat]
  rw [run_bind, run_bind, run_call (α := Amount a), run_call (α := Nat)]
  cases w.oracle.call addr sel args w.ext with
  | none => rfl
  | some p =>
    rcases p with ⟨rets, _x'⟩
    match rets with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- A successful `callAsNat` leaves `self` unchanged. -/
theorem callAsNat_self (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.self = w.self := by
  cases ret with
  | word => exact call_self (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_self (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_self (α := Unit) addr sel args hrun

/-- A successful `callAsNat` leaves the oracle unchanged. -/
theorem callAsNat_oracle (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.oracle = w.oracle := by
  cases ret with
  | word => exact call_oracle (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_oracle (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_oracle (α := Unit) addr sel args hrun

/-- A successful `viewAsNat` returns the pre-world. -/
theorem viewAsNat_world (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w' = w := by
  cases ret with
  | word => exact view_world (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [viewAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (view (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact view_world (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [viewAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (view (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact view_world (α := Unit) addr sel args hrun

end Wrappers

end Lsc.Tx.Proof
