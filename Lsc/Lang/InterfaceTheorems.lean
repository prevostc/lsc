import Lsc.Lang.InterfaceProof

/-!
# CALL / view run lemmas and Core-word certificates

`Tx.run (call/view/tryCall/tryView)` peeling lemmas, `self` / oracle
preservation, and the Amount / Bool certificate equalities `lsc_reify`
names (`map_callAsNat_*`, `bind_viewAsNat_*`, …).
-/

namespace Lsc.Tx

section CallRun
variable {S X E ε α : Type} [AbiRetType α]

/-- `Tx.run (call …)` is the oracle CALL, or `.callFailed` on `none` / decode failure. -/
@[simp] theorem run_call (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .error .callFailed
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .error .callFailed
        | some v => .ok (v, { w with ext := x' }) :=
  by apply Proof.run_call

/-- `(call …).run` is `Tx.run (call …)`. -/
@[simp] theorem call_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (call (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (call (ε := ε) (α := α) addr sel args) ctx w :=
  by apply Proof.call_run

/-- `Tx.run (view …)` is the oracle view, or `.callFailed` on decode failure. -/
@[simp] theorem run_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .error .callFailed
      | some v => .ok (v, w) :=
  by apply Proof.run_view

/-- `(view …).run` is `Tx.run (view …)`. -/
@[simp] theorem view_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (view (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (view (ε := ε) (α := α) addr sel args) ctx w :=
  by apply Proof.view_run

/-- A successful CALL: the oracle returned a decodable payload and `ext`
was updated. -/
theorem run_call_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    ∃ rets x', w.oracle.call addr sel args w.ext = some (rets, x') ∧
      AbiRetType.decode (α := α) rets = some v ∧
      w' = { w with ext := x' } :=
  Proof.run_call_ok h

/-- Oracle `none` is `.callFailed`. -/
theorem run_call_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : w.oracle.call addr sel args w.ext = none) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed :=
  Proof.run_call_none addr sel args ctx w h

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
        | some v => some (v, { w with ext := x' }) :=
  by apply Proof.run_call_toOption

/-- `toOption` of a CALL ignores the user-error type. A contract body uses the
contract's `Error`; `I.Impl.ofRef` reconstructs the same oracle CALL on a
`WorldView` without threading `ε`. -/
theorem run_call_toOption_err {ε' : Type} (addr : Address) (sel : Nat)
    (args : List Word) (ctx : Ctx) (w : World S X E) :
    (run (call (ε := ε) (α := α) addr sel args) ctx w).toOption =
      (run (call (ε := ε') (α := α) addr sel args) ctx w).toOption :=
  by apply Proof.run_call_toOption_err

/-- `WorldView.callDecode` on `w.view` is `Tx.run (call …)` mapped onto the
view. Independent of the user-error type. -/
theorem callDecode_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    WorldView.callDecode (α := α) w.view addr sel args =
      (Tx.run (call (ε := ε) (α := α) addr sel args) ctx w).toOption.map
        (Prod.map id World.view) :=
  Proof.callDecode_view addr sel args ctx w

/-- A successful view: the oracle payload decoded and the world is unchanged. -/
theorem run_view_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = some v ∧
      w' = w :=
  Proof.run_view_ok h

/-- Decode failure on a view is `.callFailed`; the world is unchanged. -/
theorem run_view_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = none) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed :=
  Proof.run_view_none addr sel args ctx w h

/-- `Tx.run (tryCall …)` is a non-reverting CALL: oracle `none` / decode failure is `.ok (.error …)`. -/
@[simp] theorem run_tryCall (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .ok (.error .callFailed, w)
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .ok (.error .callFailed, w)
        | some v => .ok (.ok v, { w with ext := x' }) :=
  by apply Proof.run_tryCall

/-- `(tryCall …).run` is `Tx.run (tryCall …)`. -/
@[simp] theorem tryCall_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (tryCall (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w :=
  by apply Proof.tryCall_run

/-- `Tx.run (tryView …)` is a non-reverting view. -/
@[simp] theorem run_tryView (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryView (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, w) :=
  by apply Proof.run_tryView

/-- A successful CALL leaves `self` unchanged (no reentrancy in this slice). -/
theorem call_self (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.self = w.self :=
  by apply Proof.call_self

/-- A successful CALL leaves the oracle unchanged. -/
theorem call_oracle (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.oracle = w.oracle :=
  by apply Proof.call_oracle

/-- A successful view returns the pre-world. -/
theorem view_world (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w' = w :=
  by apply Proof.view_world

end CallRun

section Wrappers
variable {S X E ε : Type}

/-- `natToBool (boolBit b)` is `b`. -/
@[simp] theorem natToBool_boolBit (b : Bool) : natToBool (boolBit b) = b :=
  by apply Proof.natToBool_boolBit

/-- `natToBool n` is `n != 0`. -/
@[simp] theorem natToBool_eq (n : Nat) : natToBool n = (n != 0) :=
  by apply Proof.natToBool_eq

/-- `natToBool n` is `true` exactly when `n ≠ 0`. -/
@[simp] theorem natToBool_eq_true (n : Nat) : natToBool n = true ↔ n ≠ 0 :=
  by apply Proof.natToBool_eq_true

/-- `natToBool 0` is `false`. -/
@[simp] theorem natToBool_zero : natToBool 0 = false :=
  by apply Proof.natToBool_zero

/-- `natToBool 1` is `true`. -/
@[simp] theorem natToBool_one : natToBool 1 = true :=
  by apply Proof.natToBool_one

/-- `decide (n ≠ 0) = true` is `n ≠ 0`. Used when `require (ok = true)`
meets a `n != 0` decode. -/
@[simp] theorem decide_ne_zero_eq_true (n : Nat) :
    decide (n ≠ 0) = true ↔ n ≠ 0 :=
  by apply Proof.decide_ne_zero_eq_true

/-- `(n != 0) = true` iff `n ≠ 0`. -/
@[simp] theorem bne_zero_eq_true (n : Nat) : (n != 0) = true ↔ n ≠ 0 :=
  by apply Proof.bne_zero_eq_true

/-- `Tx.call` with the result erased to a Core word. -/
@[simp] 
theorem callAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  by apply Proof.callAsNat_word

/-- `viewAsNat .word` is `view` at `Nat`. -/
@[simp] theorem viewAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  by apply Proof.viewAsNat_word

/-- `boolBit true` is `1`. -/
@[simp] theorem boolBit_true : boolBit true = 1 :=
  by apply Proof.boolBit_true

/-- `boolBit false` is `0`. -/
@[simp] theorem boolBit_false : boolBit false = 0 :=
  by apply Proof.boolBit_false

/-- `boolBit b = 1` is `b = true`. -/
@[simp] theorem boolBit_eq_one (b : Bool) : (boolBit b = 1) = (b = true) :=
  by apply Proof.boolBit_eq_one

/-- `boolBit b == 1` is `b`. -/
@[simp] theorem boolBit_beq_one (b : Bool) : (boolBit b == 1) = b :=
  by apply Proof.boolBit_beq_one

/-- `require (ok = true)` is the Core bit-test `require (boolBit ok = 1)`. -/
theorem require_bool_eq_true_iff_bit (b : Bool) (err : ε) :
    require (S := S) (X := X) (E := E) (b = true) err =
      require (boolBit b = 1) err :=
  by apply Proof.require_bool_eq_true_iff_bit

/-- Recover a `Bool` CALL from the Core-word wrapper. -/
theorem map_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args :=
  by apply Proof.map_callAsNat_bool

/-- `Tx.call` at `Bool` is `natToBool <$> callAsNat .boolOpt` (`n ≠ 0`). -/
theorem call_bool (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  by apply Proof.call_bool

/-- Recover a `Bool` view from the Core-word wrapper. -/
theorem map_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args :=
  by apply Proof.map_viewAsNat_bool

/-- `Tx.view` at `Bool` is `natToBool <$> viewAsNat .boolOpt`. -/
theorem view_bool (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  by apply Proof.view_bool

/-- Bind form of `map_callAsNat_bool` (`simp` may rewrite `<$>` to `>>= pure`). -/
theorem bind_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args :=
  by apply Proof.bind_callAsNat_bool

/-- Bind form of `map_viewAsNat_bool`. -/
theorem bind_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args :=
  by apply Proof.bind_viewAsNat_bool

/-- ABI-encoding an address is `Address.toWord`. -/
@[simp] theorem encode_address (a : Address) :
    AbiType.encode a = Address.toWord a :=
  by apply Proof.encode_address

/-- ABI-encoding an amount is its `.raw` word. -/
@[simp] theorem encode_amount {a : Asset} (x : Amount a) :
    AbiType.encode x = Amount.raw x :=
  by apply Proof.encode_amount

/-- ABI-encoding a word is the word. -/
@[simp] theorem encode_word (w : Word) : AbiType.encode w = w :=
  by apply Proof.encode_word

/-- ABI-encoding a bool is `1` / `0`. -/
@[simp] theorem encode_bool (b : Bool) : AbiType.encode b = if b then 1 else 0 :=
  by apply Proof.encode_bool

/-- `Address.toWord` is the identity; CALL targets from Core env atoms use it. -/
theorem callAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      callAsNat ret addr sel args :=
  by apply Proof.callAsNat_addr

/-- `Address.toWord` is the identity on a view target. -/
theorem viewAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      viewAsNat ret addr sel args :=
  by apply Proof.viewAsNat_addr

/-- Recover an `Amount` CALL from the Core-word wrapper. -/
theorem map_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (α := Amount a) addr sel args :=
  by apply Proof.map_callAsNat_amount

/-- Recover an `Amount` view from the Core-word wrapper. -/
theorem map_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (α := Amount a) addr sel args :=
  by apply Proof.map_viewAsNat_amount

/-- Certificate direction: surface `view` is Core `ofWord <$> viewAsNat`.
Lets `bind_map` + `raw_ofWord` turn an intermediate `ta.raw` into the Core
word (live `balanceOf` feeding `mulDiv`). -/
theorem view_eq_map_viewAsNat {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    view (α := Amount a) addr sel args =
      Amount.ofWord (a := a) <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args :=
  by apply Proof.view_eq_map_viewAsNat

/-- Bind form of `map_viewAsNat_amount`. -/
theorem bind_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      view (α := Amount a) addr sel args :=
  by apply Proof.bind_viewAsNat_amount

/-- Surface `view` then `k ta.raw` is Core `viewAsNat` then `k n`.
Simp-oriented: the surface mentions `Amount a`, so `a` is inferable. -/
theorem bind_viewAsNat_raw {a : Asset} {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (k : Nat → Tx S X E ε β) :
    view (α := Amount a) addr sel args >>= (fun ta => k ta.raw) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>= k :=
  by apply Proof.bind_viewAsNat_raw

/-- Bind form of `map_callAsNat_amount`. -/
theorem bind_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      call (α := Amount a) addr sel args :=
  by apply Proof.bind_callAsNat_amount

/-- `f <$> (x >>= k)` with an Amount wrapper; named so certificate `simp` matches
after `Core.denote` of a `letOp` sequence. -/
theorem map_bind_ofWord {a : Asset} {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    Amount.ofWord (a := a) <$> (x >>= k) =
      x >>= fun b => Amount.ofWord (a := a) <$> k b :=
  by apply Proof.map_bind_ofWord

/-- Pair-of-Amount wrap through `bind`. Certificate key for `Prod.map ofWord`. -/
theorem map_bind_ofWord_pair {a b : Asset} {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε (Nat × Nat)) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> (x >>= k) =
      x >>= fun v =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> k v :=
  by apply Proof.map_bind_ofWord_pair

/-- Discarded bind then pair-of-Amount wrap. -/
theorem map_discard_ofWord_pair {a b : Asset} {γ : Type} (x : Tx S X E ε γ)
    (y : Tx S X E ε (Nat × Nat)) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        (x >>= fun _ => y) =
      x >>= fun _ =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$> y :=
  by apply Proof.map_discard_ofWord_pair

/-- `Prod.map ofWord` of a Core pair `pure`. -/
theorem map_pure_ofWord_pair {a b : Asset} (x y : Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        (pure (x, y) : Tx S X E ε (Nat × Nat)) =
      pure (Amount.ofWord (a := a) x, Amount.ofWord (a := b) y) :=
  by apply Proof.map_pure_ofWord_pair

/-- `natToBool <$> (x >>= k)` after `Core.denote` of a Bool-returning sequence. -/
theorem map_bind_natToBool {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    natToBool <$> (x >>= k) = x >>= fun b => natToBool <$> k b :=
  by apply Proof.map_bind_natToBool

/-- Push `ofWord` through `selfAddress >>= viewAsNat` (view after a storage load).
`addr` is `Nat` so `simp` matches Core `load (S → Nat)` binders; `Address := Nat`. -/
theorem map_bind_viewAsNat_amount {a : Asset} {β : Type}
    (x : Tx S X E ε β) (addr : Nat) (sel : Nat) (args : β → List Word) :
    Amount.ofWord (a := a) <$>
        (x >>= fun v => viewAsNat (S := S) (X := X) (E := E) (ε := ε)
          .word addr sel (args v)) =
      x >>= fun v => view (α := Amount a) addr sel (args v) :=
  by apply Proof.map_bind_viewAsNat_amount

/-- `Address.toWord` is the identity; Core env atoms of `selfAddress` omit it. -/
theorem view_toWord_arg {a : Asset} (addr : Address) (sel : Nat) (v : Address) :
    view (S := S) (X := X) (E := E) (ε := ε) (α := Amount a) addr sel [v.toWord] =
      view (α := Amount a) addr sel [v] :=
  by apply Proof.view_toWord_arg

/-- After `map_bind_ofWord`, ofWord sits on the inner `selfAddress >>= viewAsNat`. -/
theorem bind_load_inner_viewAsNat_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load proj >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] :=
  by apply Proof.bind_load_inner_viewAsNat_amount

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
  by apply Proof.bind_load_inner_viewAsNat_amount_addr

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
        view (α := Amount a) addr sel [me] :=
  by apply Proof.bind_load_getD_inner_viewAsNat_amount

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
        view (α := Amount a) addr sel [me] :=
  by apply Proof.bind_load_getD_pair_addr_view_amount

/-- Load a callee address, then `selfAddress`, then an Amount view. -/
theorem load_selfAddress_view_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    Amount.ofWord (a := a) <$>
        (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
          selfAddress >>= fun me =>
            viewAsNat .word addr sel [me]) =
      load proj >>= fun addr =>
        selfAddress >>= fun me =>
          view (α := Amount a) addr sel [me.toWord] :=
  by apply Proof.load_selfAddress_view_amount

/-- `require (ok = true)` after a Bool CALL is the Core `boolOpt` bit-test. -/
theorem callAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) :=
  by apply Proof.callAsNat_bool_bind_require

/-- `require (ok = true)` after a Bool view is the Core `boolOpt` bit-test. -/
theorem viewAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) :=
  by apply Proof.viewAsNat_bool_bind_require

/-- `require (ok = true)` then a continuation after a Bool CALL. -/
theorem callAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) :=
  by apply Proof.callAsNat_bool_bind_require_bind

/-- `require (ok = true)` then a continuation after a Bool view. -/
theorem viewAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) :=
  by apply Proof.viewAsNat_bool_bind_require_bind

/-- Discarded Bool CALL: Core `boolOpt` vs surface `Bool`. -/
theorem callAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) :=
  by apply Proof.callAsNat_bool_bind_unit

/-- Discarded Bool view: Core `boolOpt` vs surface `Bool`. -/
theorem viewAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) :=
  by apply Proof.viewAsNat_bool_bind_unit

/-- Discarded Amount view: Core `word` vs surface `Amount`. -/
theorem viewAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    view (α := Amount a) addr sel args >>= (fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) :=
  by apply Proof.viewAsNat_word_bind_const

/-- Discarded Amount CALL: Core `word` vs surface `Amount`. -/
theorem callAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    call (α := Amount a) addr sel args >>= (fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) :=
  by apply Proof.callAsNat_word_bind_const

/-- A successful `callAsNat` leaves `self` unchanged. -/
theorem callAsNat_self (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.self = w.self :=
  by apply Proof.callAsNat_self

/-- A successful `callAsNat` leaves the oracle unchanged. -/
theorem callAsNat_oracle (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.oracle = w.oracle :=
  by apply Proof.callAsNat_oracle

/-- A successful `viewAsNat` returns the pre-world. -/
theorem viewAsNat_world (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w' = w :=
  by apply Proof.viewAsNat_world

end Wrappers

end Lsc.Tx
