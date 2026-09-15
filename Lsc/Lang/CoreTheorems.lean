import Lsc.Lang.Core
import Lsc.Lang.CoreProof

/-!
Frame facts for the Core IR, plus `map_denote_*` certificate lemmas that
push `f <$>` through Core constructors.

Frame: a successful (or reverting) run cannot change

Contract authors use these so a bound token address, an owner slot, or an
allowance mapping stays put without a per-entrypoint lemma. External CALLs
leave `self` unchanged (reentrancy is not modelled).
-/

namespace Lsc

variable {S X E ε : Type}

/-- A successful primitive step — a load, an add, a context word, a CALL —
never changes our storage. CALLs update `ext` only. -/
theorem Op.effects_frame {Γ : ContractSchema S X E ε} (op : Op) (env : List Nat)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E}
    (h : Tx.run (Op.denote Γ env op) ctx w = .ok (v, w')) :
    w'.self = w.self :=
  Proof.Op.effects_frame op env h

/-- If a statement never stores to a given field, a successful run of that
statement leaves any observation of that field unchanged — a scalar, a
whole mapping, a bound address. Mapping stores to a different field must
not alias it. Bound-address slots that no entrypoint stores therefore stay
fixed without a per-function lemma. -/
theorem Stmt.effects_frame_on {α} {Γ : ContractSchema S X E ε} (P : S → α)
    (s : Stmt) (env : List Nat) (f : Nat)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    P w'.self = P w.self :=
  Proof.Stmt.effects_frame_on P s env f hStore hStoreMap hStoreMap2 hf h

/-- If a statement never stores to a given scalar slot, a successful run
leaves that word unchanged. Mapping stores are required not to alias the
slot, which a lawful storage layout guarantees. -/
theorem Stmt.effects_frame {Γ : ContractSchema S X E ε} (s : Stmt) (env : List Nat)
    (f : Nat)
    (hΓ : ∀ f₁ f₂ σ v, f₁ ≠ f₂ →
      Γ.st.scalar f₁ (Γ.st.scalarUpd f₂ σ v) = Γ.st.scalar f₁ σ)
    (hMap1 : ∀ i σ m, Γ.st.scalar f (Γ.st.map1Upd i σ m) = Γ.st.scalar f σ)
    (hMap2 : ∀ i σ m, Γ.st.scalar f (Γ.st.map2Upd i σ m) = Γ.st.scalar f σ)
    (hf : f ∉ (Stmt.effects s).writes)
    {ctx : Ctx} {w : World S X E} {v : Unit} {w' : World S X E}
    (h : Tx.run (Stmt.denote Γ env s) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Proof.Stmt.effects_frame s env f hΓ hMap1 hMap2 hf h

/-- If a whole function body never stores to a given field, a successful
run leaves any observation of that field unchanged. This is the theorem
that replaces handwritten "this entrypoint does not touch X" lemmas. -/
theorem effects_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    P w'.self = P w.self :=
  Proof.effects_frame_on c env f P hStore hStoreMap hStoreMap2 hf h

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
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.scalar f w'.self = Γ.st.scalar f w.self :=
  Proof.effects_frame c env f hΓ hMap1 hMap2 hf h

/-- A successful function run does not change a one-key mapping unless the
function writes that mapping. Token uses this so a call that never
touches allowances cannot change allowance slots in EVM storage. -/
theorem effects_frame_map1 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map1 f (Γ.st.scalarUpd i σ v) = Γ.st.map1 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map1Upd i σ m) = Γ.st.map1 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map1 f (Γ.st.map2Upd i σ m) = Γ.st.map1 f σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map1 f w'.self = Γ.st.map1 f w.self :=
  Proof.effects_frame_map1 c env f hΓ hMap1 hMap2 hf h

/-- Same as `effects_frame_map1` for a nested mapping (two hash layers).
Needed when a field such as Token allowances is not written and must be
shown identical after the call. -/
theorem effects_frame_map2 {Γ : ContractSchema S X E ε} {t} (c : Core t)
    (env : List Nat) (f : Nat)
    (hΓ : ∀ i σ v, f ≠ i → Γ.st.map2 f (Γ.st.scalarUpd i σ v) = Γ.st.map2 f σ)
    (hMap1 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map1Upd i σ m) = Γ.st.map2 f σ)
    (hMap2 : ∀ i σ m, f ≠ i → Γ.st.map2 f (Γ.st.map2Upd i σ m) = Γ.st.map2 f σ)
    (hf : f ∉ (Core.effects c).writes)
    {ctx : Ctx} {w : World S X E} {v : t.denote} {w' : World S X E}
    (h : Tx.run (Core.denote Γ c env) ctx w = .ok (v, w')) :
    Γ.st.map2 f w'.self = Γ.st.map2 f w.self :=
  Proof.effects_frame_map2 c env f hΓ hMap1 hMap2 hf h

/-- Whether the function reverts or succeeds, a run does not change an
observation of a field it never stores to. Unlike `effects_frame_on`
this covers the revert path as well — a failed CALL still leaves the
bound token address untouched. -/
theorem worldAfter_frame_on {α} {Γ : ContractSchema S X E ε} {t : RetTy} (c : Core t)
    (env : List Nat) (f : Nat) (P : S → α)
    (hStore : ∀ i σ v, f ≠ i → P (Γ.st.scalarUpd i σ v) = P σ)
    (hStoreMap : ∀ i σ m, f ≠ i → P (Γ.st.map1Upd i σ m) = P σ)
    (hStoreMap2 : ∀ i σ m, f ≠ i → P (Γ.st.map2Upd i σ m) = P σ)
    (hf : f ∉ (Core.effects c).writes)
    (ctx : Ctx) (w : World S X E) :
    P (Lang.worldAfter (Core.denote Γ c env) ctx w).self = P w.self :=
  Proof.worldAfter_frame_on c env f P hStore hStoreMap hStoreMap2 hf ctx w


/-! ### `map_denote_*` certificate lemmas

Push `f <$>` through Core constructors so `lsc_reify` can wrap an Amount/Bool/pair body.
-/

/-- Push `f <$>` through `letOp`. Certificate wrap of an Amount/Bool body. -/
theorem map_denote_letOp {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v => f <$> Core.denote Γ k (v :: env) :=
  by apply Proof.map_denote_letOp

/-- Push `f <$>` through `seq`. -/
theorem map_denote_seq {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ => f <$> Core.denote Γ k env :=
  by apply Proof.map_denote_seq

/-- `f <$> ret` is `pure (f (eval r))`. -/
theorem map_denote_ret {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (r : RetExpr t) (env : List Nat) :
    f <$> Core.denote Γ (.ret r) env = pure (f (r.eval env)) :=
  by apply Proof.map_denote_ret

/-- Push `f <$>` through `ite`. -/
theorem map_denote_ite {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (c : Cond) (a b : Core t) (env : List Nat) :
    f <$> Core.denote Γ (.ite c a b) env =
      if c.denote env then f <$> Core.denote Γ a env
      else f <$> Core.denote Γ b env :=
  by apply Proof.map_denote_ite

/-- `seqIf` is bind of the chosen branch into `seqIfCont`. -/
theorem denote_seqIf {t u : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core u)
    (env : List Nat) :
    Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Core.seqIfCont Γ v k env :=
  by apply Proof.denote_seqIf

/-- Push `f <$>` through `seqIf`. -/
theorem map_denote_seqIf {t u : RetTy} {γ : Type} (f : u.denote → γ)
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core u)
    (env : List Nat) :
    f <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => f <$> Core.seqIfCont Γ v k env :=
  by apply Proof.map_denote_seqIf

/-- Amount wrap through `seqIf`. -/
theorem map_denote_seqIf_ofWord {a : Asset} {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core .word)
    (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Amount.ofWord (a := a) <$> Core.seqIfCont Γ v k env :=
  by apply Proof.map_denote_seqIf_ofWord

/-- Bool wrap through `seqIf`. -/
theorem map_denote_seqIf_natToBool {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t) (k : Core .flag)
    (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v => Tx.natToBool <$> Core.seqIfCont Γ v k env :=
  by apply Proof.map_denote_seqIf_natToBool

/-- Pair-of-Amount wrap through `seqIf`. -/
theorem map_denote_seqIf_ofWord_pair {a b : Asset} {t : RetTy}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core t)
    (k : Core (.pair .word .word)) (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.seqIf c th el k) env =
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        fun v =>
          Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
            Core.seqIfCont Γ v k env :=
  by apply Proof.map_denote_seqIf_ofWord_pair

/-- `seqIf` of unit branches is `ite` with `k` copied into both sides. -/
theorem seqIf_eq_ite {u : RetTy} (Γ : ContractSchema S X E ε)
    (c : Cond) (th el : Core .unit) (k : Core u) (env : List Nat) :
    Core.denote Γ (.seqIf c th el k) env =
      Core.denote Γ (.ite c (th.seqUnit k) (el.seqUnit k)) env :=
  by apply Proof.seqIf_eq_ite

/-- `letPure` is substitution; the wrap stays on the continuation. -/
theorem map_denote_letPure {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core t)
    (env : List Nat) :
    f <$> Core.denote Γ (.letPure p args k) env =
      f <$> Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  by apply Proof.map_denote_letPure

/-- Tail op: wrap stays on the primitive. -/
theorem map_denote_opTail {γ : Type} (f : Nat → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTail op) env = f <$> Op.denote Γ env op :=
  by apply Proof.map_denote_opTail

/-- Tail flag op: wrap stays on the primitive. -/
theorem map_denote_opTailFlag {γ : Type} (f : Nat → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTailFlag op) env = f <$> Op.denote Γ env op :=
  by apply Proof.map_denote_opTailFlag

/-- Tail address op: wrap stays on the primitive. -/
theorem map_denote_opTailAddr {γ : Type} (f : Address → γ)
    (Γ : ContractSchema S X E ε) (op : Op) (env : List Nat) :
    f <$> Core.denote Γ (.opTailAddr op) env =
      f <$> (Op.denote Γ env op : Tx S X E ε Nat) :=
  by apply Proof.map_denote_opTailAddr

/-- Tail statement: wrap stays on the statement. -/
theorem map_denote_stmtTail {γ : Type} (f : Unit → γ)
    (Γ : ContractSchema S X E ε) (s : Stmt) (env : List Nat) :
    f <$> Core.denote Γ (.stmtTail s) env = f <$> Stmt.denote Γ env s :=
  by apply Proof.map_denote_stmtTail

/-- Mapping a revert tail is still that revert. -/
theorem map_denote_revertTail {t : RetTy} {γ : Type} (f : t.denote → γ)
    (Γ : ContractSchema S X E ε) (err : Nat) (args : List Atom) (env : List Nat) :
    f <$> Core.denote Γ (.revertTail err args) env =
      Tx.revert (Γ.err.build err (args.map (·.eval env))) :=
  by apply Proof.map_denote_revertTail

/-- Amount wrap through `letOp`. First-order key for `lsc_reify`. -/
theorem map_denote_letOp_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Amount.ofWord (a := a) <$> Core.denote Γ k (v :: env) :=
  by apply Proof.map_denote_letOp_ofWord

/-- Amount wrap through `seq`. -/
theorem map_denote_seq_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Amount.ofWord (a := a) <$> Core.denote Γ k env :=
  by apply Proof.map_denote_seq_ofWord

/-- Amount wrap of a `ret`. -/
theorem map_denote_ret_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (r : RetExpr .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.ret r) env =
      pure (Amount.ofWord (a := a) (r.eval env)) :=
  by apply Proof.map_denote_ret_ofWord

/-- Amount wrap through `ite`. -/
theorem map_denote_ite_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core .word) (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.ite c th el) env =
      if c.denote env then Amount.ofWord (a := a) <$> Core.denote Γ th env
      else Amount.ofWord (a := a) <$> Core.denote Γ el env :=
  by apply Proof.map_denote_ite_ofWord

/-- Amount wrap through `letPure`. -/
theorem map_denote_letPure_ofWord {a : Asset}
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core .word)
    (env : List Nat) :
    Amount.ofWord (a := a) <$> Core.denote Γ (.letPure p args k) env =
      Amount.ofWord (a := a) <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  by apply Proof.map_denote_letPure_ofWord

/-- Bool wrap through `letOp`. `RetTy.flag` denotes to `Nat`. -/
theorem map_denote_letOp_natToBool
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Tx.natToBool <$> Core.denote Γ k (v :: env) :=
  by apply Proof.map_denote_letOp_natToBool

/-- Bool wrap through `seq`. -/
theorem map_denote_seq_natToBool
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Tx.natToBool <$> Core.denote Γ k env :=
  by apply Proof.map_denote_seq_natToBool

/-- Bool wrap of a `ret`. -/
theorem map_denote_ret_natToBool
    (Γ : ContractSchema S X E ε) (r : RetExpr .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.ret r) env =
      pure (Tx.natToBool (r.eval env)) :=
  by apply Proof.map_denote_ret_natToBool

/-- Bool wrap through `ite`. -/
theorem map_denote_ite_natToBool
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core .flag) (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.ite c th el) env =
      if c.denote env then Tx.natToBool <$> Core.denote Γ th env
      else Tx.natToBool <$> Core.denote Γ el env :=
  by apply Proof.map_denote_ite_natToBool

/-- Bool wrap through `letPure`. -/
theorem map_denote_letPure_natToBool
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom) (k : Core .flag)
    (env : List Nat) :
    Tx.natToBool <$> Core.denote Γ (.letPure p args k) env =
      Tx.natToBool <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  by apply Proof.map_denote_letPure_natToBool

/-- Pair-of-Amount wrap through `letOp`. Core `RetTy` is `.pair .word .word`. -/
theorem map_denote_letOp_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (op : Op) (k : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.letOp op k) env =
      Op.denote Γ env op >>= fun v =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ k (v :: env) :=
  by apply Proof.map_denote_letOp_ofWord_pair

/-- Pair-of-Amount wrap through `seq`. -/
theorem map_denote_seq_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (s : Stmt) (k : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.seq s k) env =
      Stmt.denote Γ env s >>= fun _ =>
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ k env :=
  by apply Proof.map_denote_seq_ofWord_pair

/-- Pair-of-Amount wrap of a `ret`. -/
theorem map_denote_ret_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (r : RetExpr (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.ret r) env =
      pure (Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b))
        (r.eval env)) :=
  by apply Proof.map_denote_ret_ofWord_pair

/-- Pair-of-Amount wrap through `ite`. -/
theorem map_denote_ite_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (c : Cond) (th el : Core (.pair .word .word))
    (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.ite c th el) env =
      if c.denote env then
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ th env
      else
        Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
          Core.denote Γ el env :=
  by apply Proof.map_denote_ite_ofWord_pair

/-- Pair-of-Amount wrap through `letPure`. -/
theorem map_denote_letPure_ofWord_pair {a b : Asset}
    (Γ : ContractSchema S X E ε) (p : Prim) (args : List Atom)
    (k : Core (.pair .word .word)) (env : List Nat) :
    Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ (.letPure p args k) env =
      Prod.map (Amount.ofWord (a := a)) (Amount.ofWord (a := b)) <$>
        Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env) :=
  by apply Proof.map_denote_letPure_ofWord_pair

end Lsc

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
