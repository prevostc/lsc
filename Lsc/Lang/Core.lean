import Lsc.Lang.Word
import Lsc.Lang.Amount
import Lsc.Lang.WordTheorems
import Lsc.Lang.AmountTheorems
import Lsc.Lang.TxTheorems
import Lsc.Lang.Interface

/-!
# the Core AST and its denotation

`Core` is a tiny first-order, loop-free, A-normal-form language that mirrors exactly the
shapes Lean's `do` elaborator produces for programs in the reifiable fragment:

* `bind op (fun x => k)`       ↦ `letOp op k` (word-valued primitive) / `seq s k` (unit statement)
* `let x := p a b; k`          ↦ `letPure p [a, b] k`
* `if c then a else b`         ↦ `ite c a b` (pure / expression-level)
* `bind (if c then a else b) k` with effects ↦ `seqIf c a b k` (`k` once)
* `pure v` in tail position    ↦ `ret v`
* tail primitives              ↦ `opTail` / `stmtTail` / `revertTail`

Join points (`have __do_jp := fun y => rest; …`) of an effectful `if` become the
shared `seqIf` continuation. Pure join points are still leaf-substituted.

Locals are de Bruijn indices into an environment of words (`var 0` is the most recently
bound value; function parameters are the initial environment, last parameter first).
Storage fields, events and errors are referenced by index through a `ContractSchema`,
which `lsc_schema` generates from the user's Lean `structure`/`inductive`s. Every case of
`denote` is *literally* the surface primitive applied to evaluated atoms, which is what
makes `Core.denote (reify f) = f` hold by `rfl` for word-typed programs whose `bind`
nesting already matches the ANF, and by the `Tx` monad laws when an `@[lsc_inline]`
helper sits mid-`do`. `Amount a` / `Fixed d` are one-field structures over `Word`;
Reify erases `.raw` / `ofWord` and certificates of Amount-returning functions are
`Amount.ofWord <$> Core.denote`. The `map_denote_*` lemmas push that wrapper through
Core constructors (so the certificate does not depend on `do`-notation matching
`map_bind`). Bool-returning functions wrap with `Tx.natToBool`. Pair-of-Amount
returns wrap with `Prod.map Amount.ofWord Amount.ofWord`.
-/

namespace Lsc

/-- Operands: a local (de Bruijn index) or a word literal. -/
inductive Atom
  | var (i : Nat)
  | lit (n : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

def Atom.eval (env : List Nat) : Atom → Nat
  | .var i => env.getD i 0
  | .lit n => n

@[simp] theorem Atom.eval_lit (env : List Nat) (n : Nat) :
    Atom.eval env (.lit n) = n :=
  rfl

@[simp] theorem Atom.eval_var_0 (x : Nat) (env : List Nat) :
    Atom.eval (x :: env) (.var 0) = x :=
  rfl

/-- `Address` is a `def` newtype, so simp's discrimination tree does not
reuse the `Nat` lemma on `Atom.eval (to :: env)`. -/
@[simp] theorem Atom.eval_var_0_addr (x : Address) (env : List Nat) :
    Atom.eval (x :: env) (.var 0) = x :=
  rfl

@[simp] theorem Atom.eval_var_1_addr (x y : Address) (env : List Nat) :
    Atom.eval (x :: y :: env) (.var 1) = y :=
  rfl

@[simp] theorem Atom.eval_var_2_addr (x y z : Address) (env : List Nat) :
    Atom.eval (x :: y :: z :: env) (.var 2) = z :=
  rfl

@[simp] theorem Atom.eval_var_3_addr (a b c d : Address) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: env) (.var 3) = d :=
  rfl

@[simp] theorem Atom.eval_var_succ_addr (x : Address) (env : List Nat) (i : Nat) :
    Atom.eval (x :: env) (.var (i + 1)) = Atom.eval env (.var i) :=
  rfl

@[simp] theorem Atom.eval_var_1 (x y : Nat) (env : List Nat) :
    Atom.eval (x :: y :: env) (.var 1) = y :=
  rfl

@[simp] theorem Atom.eval_var_2 (x y z : Nat) (env : List Nat) :
    Atom.eval (x :: y :: z :: env) (.var 2) = z :=
  rfl

@[simp] theorem Atom.eval_var_3 (a b c d : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: env) (.var 3) = d :=
  rfl

@[simp] theorem Atom.eval_var_4 (a b c d e : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: env) (.var 4) = e :=
  rfl

@[simp] theorem Atom.eval_var_5 (a b c d e f : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: env) (.var 5) = f :=
  rfl

@[simp] theorem Atom.eval_var_succ (x : Nat) (env : List Nat) (i : Nat) :
    Atom.eval (x :: env) (.var (i + 1)) = Atom.eval env (.var i) :=
  rfl

@[simp] theorem Atom.eval_var_6 (a b c d e f g : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: env) (.var 6) = g :=
  rfl

@[simp] theorem Atom.eval_var_7 (a b c d e f g h : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: env) (.var 7) = h :=
  rfl

@[simp] theorem Atom.eval_var_8 (a b c d e f g h i : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: i :: env) (.var 8) = i :=
  rfl

@[simp] theorem Atom.eval_var_9 (a b c d e f g h i j : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: env)
      (.var 9) = j :=
  rfl

@[simp] theorem Atom.eval_var_10 (a b c d e f g h i j k : Nat) (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: env)
      (.var 10) = k :=
  rfl

@[simp] theorem Atom.eval_var_11 (a b c d e f g h i j k l : Nat)
    (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: env)
      (.var 11) = l :=
  rfl

@[simp] theorem Atom.eval_var_12 (a b c d e f g h i j k l m : Nat)
    (env : List Nat) :
    Atom.eval (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m
        :: env) (.var 12) = m :=
  rfl

@[simp] theorem list_getD_cons_zero {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 0 d = x :=
  rfl

/-- `List.getD (x :: xs) (n+1)` steps into the tail (`OfNat` indices use the
explicit `1`/`2`/… lemmas below). -/
@[simp] theorem list_getD_cons_succ {α : Type _} (x : α) (xs : List α) (n : Nat)
    (d : α) :
    List.getD (x :: xs) (n + 1) d = List.getD xs n d :=
  rfl

@[simp] theorem list_getD_cons_one {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 1 d = List.getD xs 0 d :=
  rfl

@[simp] theorem list_getD_cons_two {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 2 d = List.getD xs 1 d :=
  rfl

@[simp] theorem list_getD_cons_three {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 3 d = List.getD xs 2 d :=
  rfl

@[simp] theorem list_getD_cons_four {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 4 d = List.getD xs 3 d :=
  rfl

@[simp] theorem list_getD_cons_five {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 5 d = List.getD xs 4 d :=
  rfl

@[simp] theorem list_getD_cons_six {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 6 d = List.getD xs 5 d :=
  rfl

@[simp] theorem list_getD_cons_seven {α : Type _} (x : α) (xs : List α) (d : α) :
    List.getD (x :: xs) 7 d = List.getD xs 6 d :=
  rfl

/-- `schema.err.build i args` is `List.getD [ctor] i default args`. -/
@[simp] theorem list_getD_cons_zero_app {α β : Type _} (f : α → β)
    (xs : List (α → β)) (d : α → β) (x : α) :
    List.getD (f :: xs) 0 d x = f x :=
  rfl

@[simp] theorem list_getD_pair_zero {α : Type _} (a b d : α) :
    List.getD [a, b] 0 d = a :=
  rfl

/-- Schema `st.scalar 0` is `List.getD [proj₀, …] 0 default`. `α` is `Nat` or
`Address` (`Address := Nat`) so `simp` matches either discrimination-tree key. -/
@[simp] theorem load_getD_cons {S X E ε α : Type}
    (a : S → α) (xs : List (S → α)) (d : S → α) :
    Tx.load (S := S) (X := X) (E := E) (ε := ε) (List.getD (a :: xs) 0 d) =
      Tx.load a := by
  rw [list_getD_cons_zero]

@[simp] theorem load_getD_cons_one {S X E ε α : Type}
    (a b : S → α) (xs : List (S → α)) (d : S → α) :
    Tx.load (S := S) (X := X) (E := E) (ε := ε) (List.getD (a :: b :: xs) 1 d) =
      Tx.load b := by
  rw [list_getD_cons_one, list_getD_cons_zero]

@[simp] theorem load_getD_cons_two {S X E ε α : Type}
    (a b c : S → α) (xs : List (S → α)) (d : S → α) :
    Tx.load (S := S) (X := X) (E := E) (ε := ε)
        (List.getD (a :: b :: c :: xs) 2 d) =
      Tx.load c := by
  rw [list_getD_cons_two, list_getD_cons_one, list_getD_cons_zero]

/-- `simp` lemma: `xs[1]?` is `OfNat` `1`, not `n.succ` / `i+1`. -/
@[simp] theorem list_getElem?_cons_one {α : Type _} (a : α) (l : List α) :
    (a :: l)[1]? = l[0]? :=
  rfl

@[simp] theorem list_getElem?_cons_two {α : Type _} (a : α) (l : List α) :
    (a :: l)[2]? = l[1]? :=
  rfl

@[simp] theorem list_getElem?_cons_three {α : Type _} (a : α) (l : List α) :
    (a :: l)[3]? = l[2]? :=
  rfl

@[simp] theorem list_getElem?_cons_four {α : Type _} (a : α) (l : List α) :
    (a :: l)[4]? = l[3]? :=
  rfl

@[simp] theorem list_getElem?_cons_five {α : Type _} (a : α) (l : List α) :
    (a :: l)[5]? = l[4]? :=
  rfl

/-- Decidable conditions. Denotes to a `Prop` whose `Decidable` instance is the one Lean's
elaborator picks for the same proposition, so `if` on both sides agree definitionally. -/
inductive Cond
  | lt (a b : Atom)
  | le (a b : Atom)
  | eq (a b : Atom)
  | ne (a b : Atom)
  | and (c d : Cond)
  | or (c d : Cond)
  | not (c : Cond)
  | tt
  | ff
  deriving DecidableEq, Repr, Lean.ToExpr

def Cond.denote (env : List Nat) : Cond → Prop
  | .lt a b => a.eval env < b.eval env
  | .le a b => a.eval env ≤ b.eval env
  | .eq a b => a.eval env = b.eval env
  | .ne a b => a.eval env ≠ b.eval env
  | .and c d => c.denote env ∧ d.denote env
  | .or c d => c.denote env ∨ d.denote env
  | .not c => ¬ c.denote env
  | .tt => True
  | .ff => False

@[simp] theorem Cond.denote_lt (env : List Nat) (a b : Atom) :
    Cond.denote env (.lt a b) = (a.eval env < b.eval env) := rfl
@[simp] theorem Cond.denote_le (env : List Nat) (a b : Atom) :
    Cond.denote env (.le a b) = (a.eval env ≤ b.eval env) := rfl
@[simp] theorem Cond.denote_eq (env : List Nat) (a b : Atom) :
    Cond.denote env (.eq a b) = (a.eval env = b.eval env) := rfl
@[simp] theorem Cond.denote_ne (env : List Nat) (a b : Atom) :
    Cond.denote env (.ne a b) = (a.eval env ≠ b.eval env) := rfl
@[simp] theorem Cond.denote_and (env : List Nat) (c d : Cond) :
    Cond.denote env (.and c d) = (c.denote env ∧ d.denote env) := rfl
@[simp] theorem Cond.denote_or (env : List Nat) (c d : Cond) :
    Cond.denote env (.or c d) = (c.denote env ∨ d.denote env) := rfl
@[simp] theorem Cond.denote_not (env : List Nat) (c : Cond) :
    Cond.denote env (.not c) = ¬ c.denote env := rfl
@[simp] theorem Cond.denote_tt (env : List Nat) : Cond.denote env .tt = True := rfl
@[simp] theorem Cond.denote_ff (env : List Nat) : Cond.denote env .ff = False := rfl

instance Cond.instDecidable (env : List Nat) : (c : Cond) → Decidable (c.denote env)
  | .lt a b => inferInstanceAs (Decidable (a.eval env < b.eval env))
  | .le a b => inferInstanceAs (Decidable (a.eval env ≤ b.eval env))
  | .eq a b => inferInstanceAs (Decidable (a.eval env = b.eval env))
  | .ne a b => inferInstanceAs (Decidable (a.eval env ≠ b.eval env))
  | .and c d => @instDecidableAnd _ _ (Cond.instDecidable env c) (Cond.instDecidable env d)
  | .or c d => @instDecidableOr _ _ (Cond.instDecidable env c) (Cond.instDecidable env d)
  | .not c => @instDecidableNot _ (Cond.instDecidable env c)
  | .tt => inferInstanceAs (Decidable True)
  | .ff => inferInstanceAs (Decidable False)

/-- Pure word operations (wrapping arithmetic, exactly the EVM). -/
inductive Prim
  | id
  | addWrap
  | subWrap
  | mulWrap
  deriving DecidableEq, Repr, Lean.ToExpr

def Prim.eval : Prim → List Nat → Nat
  | .id, [a] => a
  | .addWrap, [a, b] => Tx.addWrap a b
  | .subWrap, [a, b] => Tx.subWrap a b
  | .mulWrap, [a, b] => Tx.mulWrap a b
  | _, _ => 0

@[simp] theorem Prim.eval_id (a : Nat) : Prim.eval .id [a] = a := rfl

/-- Word-valued monadic primitives. -/
inductive Op
  | load (f : Nat)
  | loadMap (f : Nat) (k : Atom)
  | loadMap2 (f : Nat) (k₁ k₂ : Atom)
  | sender
  | value
  | timestamp
  | blockNumber
  | selfAddress
  | addChecked (a b : Atom)
  | subChecked (a b : Atom)
  | mulChecked (a b : Atom)
  | divChecked (a b : Atom)
  | mulDivDown (a b c : Atom)
  | mulDivUp (a b c : Atom)
  | pow10 (d : Atom)
  /-- CALL: target address, selector, ABI argument words, return kind.
  Arity is `args.length`; denotation is `Tx.callAsNat`. -/
  | call (target : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
  /-- STATICCALL: same payload as `call`; denotation is `Tx.viewAsNat`. -/
  | view (target : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
  /-- Value-carrying CALL, empty calldata. Denotation is `boolBit <$> Tx.sendRaw`. -/
  | send (target : Atom) (amount : Atom)
  /-- `selfbalance()` of the executing account. -/
  | selfBalance
  | pure (a : Atom)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Unit-valued monadic primitives (statements). -/
inductive Stmt
  | store (f : Nat) (v : Atom)
  | storeMap (f : Nat) (k v : Atom)
  | storeMap2 (f : Nat) (k₁ k₂ v : Atom)
  | require (c : Cond) (err : Nat) (args : List Atom)
  | emit (ev : Nat) (args : List Atom)
  | revert (err : Nat) (args : List Atom)
  /-- Discarded CALL (`let _ ← …`). -/
  | call (target : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
  /-- Discarded STATICCALL (`let _ ← …` of a view). -/
  | view (target : Atom) (sel : Nat) (args : List Atom) (ret : AbiRet)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Return types of contract functions. -/
inductive RetTy
  | unit
  | word
  | addr
  | flag
  | pair (a b : RetTy)
  deriving DecidableEq, Repr, Lean.ToExpr

@[reducible] def RetTy.denote : RetTy → Type
  | .unit => Unit
  | .word => Nat
  | .addr => Address
  | .flag => Nat
  | .pair a b => a.denote × b.denote

/-- Return expressions, typed by `RetTy`. -/
inductive RetExpr : RetTy → Type
  | unit : RetExpr .unit
  | word (a : Atom) : RetExpr .word
  | addr (a : Atom) : RetExpr .addr
  | flag (a : Atom) : RetExpr .flag
  | pair {s t : RetTy} (x : RetExpr s) (y : RetExpr t) : RetExpr (.pair s t)

def RetExpr.eval (env : List Nat) : {t : RetTy} → RetExpr t → t.denote
  | _, .unit => ()
  | _, .word a => a.eval env
  | _, .addr a => (a.eval env : Nat)
  | _, .flag a => (a.eval env : Nat)
  | _, .pair x y => (x.eval env, y.eval env)

@[simp] theorem RetExpr.eval_word (env : List Nat) (a : Atom) :
    RetExpr.eval env (.word a) = a.eval env :=
  rfl
@[simp] theorem RetExpr.eval_flag (env : List Nat) (a : Atom) :
    RetExpr.eval env (.flag a) = a.eval env :=
  rfl

/-- The Core language. Indexed by the function's return type. -/
inductive Core : RetTy → Type
  | ret {t : RetTy} (r : RetExpr t) : Core t
  | opTail (op : Op) : Core .word
  | opTailAddr (op : Op) : Core .addr
  | opTailFlag (op : Op) : Core .flag
  | stmtTail (s : Stmt) : Core .unit
  | revertTail {t : RetTy} (err : Nat) (args : List Atom) : Core t
  | letOp {t : RetTy} (op : Op) (k : Core t) : Core t
  | seq {t : RetTy} (s : Stmt) (k : Core t) : Core t
  | letPure {t : RetTy} (p : Prim) (args : List Atom) (k : Core t) : Core t
  | ite {t : RetTy} (c : Cond) (a b : Core t) : Core t
  /-- Run `th` or `el`, then `k` once. Unit branches keep `k`'s environment;
  word/addr/flag branches bind the result as `var 0` in `k`. -/
  | seqIf {t u : RetTy} (c : Cond) (th el : Core t) (k : Core u) : Core u

/-! ## Schemas: how field / event / error indices map to the user's Lean types -/

/-- Storage access by field index. Fields are classified by shape: scalar word,
single-key mapping, double-key mapping. Generated by `lsc_schema`. -/
structure StorageSchema (S : Type) where
  scalar : Nat → S → Nat
  scalarUpd : Nat → S → Nat → S
  map1 : Nat → S → Nat → Nat
  map1Upd : Nat → S → (Nat → Nat) → S
  map2 : Nat → S → Nat → Nat → Nat
  map2Upd : Nat → S → (Nat → Nat → Nat) → S
  /-- Point-update a 1-key map. For `Amount` fields this is `Function.update` on the
  Amount-valued map (with `ofNat`), which matches the surface `write f[k]`. The
  whole-map `map1Upd` is kept for `Lawful`. Default is the Nat encoding. -/
  map1Set : Nat → S → Nat → Nat → S := fun f σ k v =>
    map1Upd f σ (Function.update (map1 f σ) k v)
  map2Set : Nat → S → Nat → Nat → Nat → S := fun f σ k₁ k₂ v =>
    map2Upd f σ (Function.update (map2 f σ) k₁ (Function.update (map2 f σ k₁) k₂ v))

structure EvSchema (E : Type) where
  build : Nat → List Nat → E

structure ErrSchema (ε : Type) where
  build : Nat → List Nat → ε

/-- Storage / event / error index tables. External CALLs are self-contained
`Op.call` / `Op.view` (selector + target + arity + return kind); there is no
binding table on the schema. -/
structure ContractSchema (S X E ε : Type) where
  st : StorageSchema S
  ev : EvSchema E
  err : ErrSchema ε

/-! ## Denotation -/

variable {S X E ε : Type}

def Op.denote (Γ : ContractSchema S X E ε) (env : List Nat) : Op → Tx S X E ε Nat
  | .load f => Tx.load (Γ.st.scalar f)
  | .loadMap f k => Tx.loadMap (Γ.st.map1 f) (k.eval env)
  | .loadMap2 f k₁ k₂ => Tx.loadMap2 (Γ.st.map2 f) (k₁.eval env) (k₂.eval env)
  | .sender => Tx.sender
  | .value => Tx.valueRaw
  | .timestamp => Tx.timestamp
  | .blockNumber => Tx.blockNumber
  | .selfAddress => Tx.selfAddress
  | .selfBalance => Tx.selfBalanceRaw
  | .addChecked a b => Tx.addChecked (a.eval env) (b.eval env)
  | .subChecked a b => Tx.subChecked (a.eval env) (b.eval env)
  | .mulChecked a b => Tx.mulChecked (a.eval env) (b.eval env)
  | .divChecked a b => Tx.divChecked (a.eval env) (b.eval env)
  | .mulDivDown a b c => Tx.mulDivDown (a.eval env) (b.eval env) (c.eval env)
  | .mulDivUp a b c => Tx.mulDivUp (a.eval env) (b.eval env) (c.eval env)
  | .pow10 d => Tx.pow10 (d.eval env)
  | .call t sel args ret =>
    Tx.callAsNat ret (t.eval env) sel (args.map (·.eval env))
  | .view t sel args ret =>
    Tx.viewAsNat ret (t.eval env) sel (args.map (·.eval env))
  | .send t amt =>
    Tx.boolBit <$> Tx.sendRaw (t.eval env) (amt.eval env)
  | .pure a => Pure.pure (a.eval env)

def Stmt.denote (Γ : ContractSchema S X E ε) (env : List Nat) : Stmt → Tx S X E ε Unit
  | .store f v => Tx.store (Γ.st.scalarUpd f) (v.eval env)
  | .storeMap f k v => Tx.storeMap (Γ.st.map1 f) (Γ.st.map1Upd f) (k.eval env) (v.eval env)
  | .storeMap2 f k₁ k₂ v =>
    Tx.storeMap2 (Γ.st.map2 f) (Γ.st.map2Upd f) (k₁.eval env) (k₂.eval env) (v.eval env)
  | .require c err args => Tx.require (c.denote env) (Γ.err.build err (args.map (·.eval env)))
  | .emit ev args => Tx.emit (Γ.ev.build ev (args.map (·.eval env)))
  | .revert err args => Tx.revert (Γ.err.build err (args.map (·.eval env)))
  | .call t sel args ret =>
    Op.denote Γ env (.call t sel args ret) >>= fun _ => Pure.pure ()
  | .view t sel args ret =>
    Op.denote Γ env (.view t sel args ret) >>= fun _ => Pure.pure ()

def Core.denote (Γ : ContractSchema S X E ε) : {t : RetTy} → Core t → List Nat → Tx S X E ε t.denote
  | _, .ret r, env => pure (r.eval env)
  | _, .opTail op, env => Op.denote Γ env op
  | _, .opTailAddr op, env => (Op.denote Γ env op : Tx S X E ε Nat)
  | _, .opTailFlag op, env => (Op.denote Γ env op : Tx S X E ε Nat)
  | _, .stmtTail s, env => Stmt.denote Γ env s
  | _, .revertTail err args, env => Tx.revert (Γ.err.build err (args.map (·.eval env)))
  | _, .letOp op k, env => Op.denote Γ env op >>= fun v => Core.denote Γ k (v :: env)
  | _, .seq s k, env => Stmt.denote Γ env s >>= fun _ => Core.denote Γ k env
  | _, .letPure p args k, env => Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env)
  | _, .ite c a b, env => if c.denote env then Core.denote Γ a env else Core.denote Γ b env
  | _, .seqIf (t := t) c th el k, env =>
      (if c.denote env then Core.denote Γ th env else Core.denote Γ el env) >>=
        match t with
        | .unit => fun _ => Core.denote Γ k env
        | .word => fun v => Core.denote Γ k (v :: env)
        | .addr => fun v => Core.denote Γ k ((v : Nat) :: env)
        | .flag => fun v => Core.denote Γ k (v :: env)
        | .pair _ _ => fun _ => Core.denote Γ k env

/-- Continuation of `seqIf` (`k` after the chosen branch). -/
def Core.seqIfCont (Γ : ContractSchema S X E ε) :
    {t u : RetTy} → t.denote → Core u → List Nat → Tx S X E ε u.denote
  | .unit, _, _, k, env => Core.denote Γ k env
  | .word, _, v, k, env => Core.denote Γ k (v :: env)
  | .addr, _, v, k, env => Core.denote Γ k ((v : Nat) :: env)
  | .flag, _, v, k, env => Core.denote Γ k (v :: env)
  | .pair _ _, _, _, k, env => Core.denote Γ k env

/-! ## Renaming (used by the reifier to eliminate join points) -/

def Atom.rename (ρ : Nat → Atom) : Atom → Atom
  | .var i => ρ i
  | .lit n => .lit n

/-- Lift a renaming under one binder. -/
def liftRename (ρ : Nat → Atom) : Nat → Atom
  | 0 => .var 0
  | i + 1 =>
    match ρ i with
    | .var j => .var (j + 1)
    | .lit n => .lit n

/-- `seqIf` binds `k` under one extra local iff the branches are word-like. -/
def seqIfRename {t : RetTy} (ρ : Nat → Atom) : Nat → Atom :=
  match t with
  | .word | .addr | .flag => liftRename ρ
  | .unit | .pair _ _ => ρ

def Cond.rename (ρ : Nat → Atom) : Cond → Cond
  | .lt a b => .lt (a.rename ρ) (b.rename ρ)
  | .le a b => .le (a.rename ρ) (b.rename ρ)
  | .eq a b => .eq (a.rename ρ) (b.rename ρ)
  | .ne a b => .ne (a.rename ρ) (b.rename ρ)
  | .and c d => .and (c.rename ρ) (d.rename ρ)
  | .or c d => .or (c.rename ρ) (d.rename ρ)
  | .not c => .not (c.rename ρ)
  | .tt => .tt
  | .ff => .ff

def Op.rename (ρ : Nat → Atom) : Op → Op
  | .load f => .load f
  | .loadMap f k => .loadMap f (k.rename ρ)
  | .loadMap2 f k₁ k₂ => .loadMap2 f (k₁.rename ρ) (k₂.rename ρ)
  | .sender => .sender
  | .value => .value
  | .timestamp => .timestamp
  | .blockNumber => .blockNumber
  | .selfAddress => .selfAddress
  | .addChecked a b => .addChecked (a.rename ρ) (b.rename ρ)
  | .subChecked a b => .subChecked (a.rename ρ) (b.rename ρ)
  | .mulChecked a b => .mulChecked (a.rename ρ) (b.rename ρ)
  | .divChecked a b => .divChecked (a.rename ρ) (b.rename ρ)
  | .mulDivDown a b c => .mulDivDown (a.rename ρ) (b.rename ρ) (c.rename ρ)
  | .mulDivUp a b c => .mulDivUp (a.rename ρ) (b.rename ρ) (c.rename ρ)
  | .pow10 d => .pow10 (d.rename ρ)
  | .call t sel args ret => .call (t.rename ρ) sel (args.map (·.rename ρ)) ret
  | .view t sel args ret => .view (t.rename ρ) sel (args.map (·.rename ρ)) ret
  | .send t amt => .send (t.rename ρ) (amt.rename ρ)
  | .selfBalance => .selfBalance
  | .pure a => .pure (a.rename ρ)

def Stmt.rename (ρ : Nat → Atom) : Stmt → Stmt
  | .store f v => .store f (v.rename ρ)
  | .storeMap f k v => .storeMap f (k.rename ρ) (v.rename ρ)
  | .storeMap2 f k₁ k₂ v => .storeMap2 f (k₁.rename ρ) (k₂.rename ρ) (v.rename ρ)
  | .require c err args => .require (c.rename ρ) err (args.map (·.rename ρ))
  | .emit ev args => .emit ev (args.map (·.rename ρ))
  | .revert err args => .revert err (args.map (·.rename ρ))
  | .call t sel args ret => .call (t.rename ρ) sel (args.map (·.rename ρ)) ret
  | .view t sel args ret => .view (t.rename ρ) sel (args.map (·.rename ρ)) ret

def RetExpr.rename (ρ : Nat → Atom) : {t : RetTy} → RetExpr t → RetExpr t
  | _, .unit => .unit
  | _, .word a => .word (a.rename ρ)
  | _, .addr a => .addr (a.rename ρ)
  | _, .flag a => .flag (a.rename ρ)
  | _, .pair x y => .pair (x.rename ρ) (y.rename ρ)

def Core.rename (ρ : Nat → Atom) : {t : RetTy} → Core t → Core t
  | _, .ret r => .ret (r.rename ρ)
  | _, .opTail op => .opTail (op.rename ρ)
  | _, .opTailAddr op => .opTailAddr (op.rename ρ)
  | _, .opTailFlag op => .opTailFlag (op.rename ρ)
  | _, .stmtTail s => .stmtTail (s.rename ρ)
  | _, .revertTail err args => .revertTail err (args.map (·.rename ρ))
  | _, .letOp op k => .letOp (op.rename ρ) (k.rename (liftRename ρ))
  | _, .seq s k => .seq (s.rename ρ) (k.rename ρ)
  | _, .letPure p args k => .letPure p (args.map (·.rename ρ)) (k.rename (liftRename ρ))
  | _, .ite c a b => .ite (c.rename ρ) (a.rename ρ) (b.rename ρ)
  | _, .seqIf (t := t) c th el k =>
      .seqIf (c.rename ρ) (th.rename ρ) (el.rename ρ) (k.rename (seqIfRename (t := t) ρ))

/-- Sequence a unit core before `k`, duplicating `k` through `ite`. -/
def Core.seqUnit {u : RetTy} : Core .unit → Core u → Core u
  | .ret _, k => k
  | .stmtTail s, k => .seq s k
  | .seq s k', k => .seq s (seqUnit k' k)
  | .letOp op k', k => .letOp op (seqUnit k' (k.rename (fun i => .var (i + 1))))
  | .letPure p args k', k => .letPure p args (seqUnit k' (k.rename (fun i => .var (i + 1))))
  | .ite c a b, k => .ite c (seqUnit a k) (seqUnit b k)
  | .seqIf (t := t) c th el k', k =>
      .seqIf c th el (seqUnit k' (match t with
        | .word | .addr | .flag => k.rename (fun i => .var (i + 1))
        | .unit | .pair _ _ => k))
  | .revertTail e args, _ => .revertTail e args

/-- Bind a word core's result into `k` (`var 0`), duplicating `k` through `ite`. -/
def Core.bindWord {u : RetTy} : Core .word → Core u → Core u
  | .ret r, k =>
    match r with
    | .word a => .letPure .id [a] k
  | .opTail op, k => .letOp op k
  | .letOp op k', k => .letOp op (bindWord k' k)
  | .seq s k', k => .seq s (bindWord k' k)
  | .letPure p args k', k => .letPure p args (bindWord k' k)
  | .ite c a b, k => .ite c (bindWord a k) (bindWord b k)
  | .seqIf c th el k', k => .seqIf c th el (bindWord k' k)
  | .revertTail e args, _ => .revertTail e args

/-- Bind an address core's result into `k`. -/
def Core.bindAddr {u : RetTy} : Core .addr → Core u → Core u
  | .ret r, k =>
    match r with
    | .addr a => .letPure .id [a] k
  | .opTailAddr op, k => .letOp op k
  | .letOp op k', k => .letOp op (bindAddr k' k)
  | .seq s k', k => .seq s (bindAddr k' k)
  | .letPure p args k', k => .letPure p args (bindAddr k' k)
  | .ite c a b, k => .ite c (bindAddr a k) (bindAddr b k)
  | .seqIf c th el k', k => .seqIf c th el (bindAddr k' k)
  | .revertTail e args, _ => .revertTail e args

/-- Bind a flag core's result into `k`. -/
def Core.bindFlag {u : RetTy} : Core .flag → Core u → Core u
  | .ret r, k =>
    match r with
    | .flag a => .letPure .id [a] k
  | .opTailFlag op, k => .letOp op k
  | .letOp op k', k => .letOp op (bindFlag k' k)
  | .seq s k', k => .seq s (bindFlag k' k)
  | .letPure p args k', k => .letPure p args (bindFlag k' k)
  | .ite c a b, k => .ite c (bindFlag a k) (bindFlag b k)
  | .seqIf c th el k', k => .seqIf c th el (bindFlag k' k)
  | .revertTail e args, _ => .revertTail e args

/-! ## Quoting `Core` values into `Expr` (indexed families are not covered by `deriving ToExpr`) -/

open Lean in
def RetExpr.toExpr : {t : RetTy} → RetExpr t → Expr
  | _, .unit => mkConst ``RetExpr.unit
  | _, .word a => mkApp (mkConst ``RetExpr.word) (Lean.toExpr a)
  | _, .addr a => mkApp (mkConst ``RetExpr.addr) (Lean.toExpr a)
  | _, .flag a => mkApp (mkConst ``RetExpr.flag) (Lean.toExpr a)
  | .pair s t, .pair x y =>
    mkApp4 (mkConst ``RetExpr.pair) (Lean.toExpr s) (Lean.toExpr t) x.toExpr y.toExpr

open Lean in
def Core.toExpr : {t : RetTy} → Core t → Expr
  | t, .ret r => mkApp2 (mkConst ``Core.ret) (Lean.toExpr t) r.toExpr
  | _, .opTail op => mkApp (mkConst ``Core.opTail) (Lean.toExpr op)
  | _, .opTailAddr op => mkApp (mkConst ``Core.opTailAddr) (Lean.toExpr op)
  | _, .opTailFlag op => mkApp (mkConst ``Core.opTailFlag) (Lean.toExpr op)
  | _, .stmtTail s => mkApp (mkConst ``Core.stmtTail) (Lean.toExpr s)
  | t, .revertTail err args =>
    mkApp3 (mkConst ``Core.revertTail) (Lean.toExpr t) (Lean.toExpr err) (Lean.toExpr args)
  | t, .letOp op k => mkApp3 (mkConst ``Core.letOp) (Lean.toExpr t) (Lean.toExpr op) k.toExpr
  | t, .seq s k => mkApp3 (mkConst ``Core.seq) (Lean.toExpr t) (Lean.toExpr s) k.toExpr
  | t, .letPure p args k =>
    mkApp4 (mkConst ``Core.letPure) (Lean.toExpr t) (Lean.toExpr p) (Lean.toExpr args) k.toExpr
  | t, .ite c a b => mkApp4 (mkConst ``Core.ite) (Lean.toExpr t) (Lean.toExpr c) a.toExpr b.toExpr
  | u, .seqIf (t := t) c th el k =>
    mkAppN (mkConst ``Core.seqIf)
      #[Lean.toExpr t, Lean.toExpr u, Lean.toExpr c, th.toExpr, el.toExpr, k.toExpr]

/-! ## Pretty-printing of `Core` for `#eval`/logging -/

instance : Repr (RetExpr t) where
  reprPrec r _ :=
    let rec go : {t : RetTy} → RetExpr t → Std.Format
      | _, .unit => "()"
      | _, .word a => repr a
      | _, .addr a => repr a
      | _, .flag a => repr a
      | _, .pair x y => "(" ++ go x ++ ", " ++ go y ++ ")"
    go r

instance : Repr (Core t) where
  reprPrec c _ :=
    let rec go : {t : RetTy} → Core t → Std.Format
      | _, .ret r => "ret " ++ repr r
      | _, .opTail op => "tail " ++ repr op
      | _, .opTailAddr op => "tail " ++ repr op
      | _, .opTailFlag op => "tail " ++ repr op
      | _, .stmtTail s => "tail " ++ repr s
      | _, .revertTail e a => "revert " ++ repr e ++ " " ++ repr a
      | _, .letOp op k => "let ← " ++ repr op ++ ";" ++ Std.Format.line ++ go k
      | _, .seq s k => repr s ++ ";" ++ Std.Format.line ++ go k
      | _, .letPure p a k => "let := " ++ repr p ++ " " ++ repr a ++ ";" ++ Std.Format.line ++ go k
      | _, .ite c a b =>
        "if " ++ repr c ++ " then" ++ Std.Format.nest 2 (Std.Format.line ++ go a) ++
          Std.Format.line ++ "else" ++ Std.Format.nest 2 (Std.Format.line ++ go b)
      | _, .seqIf c th el k =>
        "seqIf " ++ repr c ++ " then" ++ Std.Format.nest 2 (Std.Format.line ++ go th) ++
          Std.Format.line ++ "else" ++ Std.Format.nest 2 (Std.Format.line ++ go el) ++
          Std.Format.line ++ "then" ++ Std.Format.nest 2 (Std.Format.line ++ go k)
    go c

/-! ## Effects and framing -/

/-- Reads, writes, emits, and external CALLs (selectors). Views are tracked
separately so a view-only function is still a pure read. -/
structure Effects where
  reads : List Nat := []
  writes : List Nat := []
  emits : List Nat := []
  /-- Selectors of `Op.call` / `Stmt.call` (state-changing CALL). -/
  calls : List Nat := []
  /-- Selectors of `Op.view` / `Stmt.view` (STATICCALL). -/
  views : List Nat := []

def Effects.append (a b : Effects) : Effects where
  reads := a.reads ++ b.reads
  writes := a.writes ++ b.writes
  emits := a.emits ++ b.emits
  calls := a.calls ++ b.calls
  views := a.views ++ b.views

def Op.effects : Op → Effects
  | .load f => { reads := [f] }
  | .loadMap f _ => { reads := [f] }
  | .loadMap2 f _ _ => { reads := [f] }
  | .call _ sel _ _ => { calls := [sel] }
  | .view _ sel _ _ => { views := [sel] }
  | .send _ _ => { calls := [0] }
  | _ => {}

def Stmt.effects : Stmt → Effects
  | .store f _ => { writes := [f] }
  | .storeMap f _ _ => { writes := [f] }
  | .storeMap2 f _ _ _ => { writes := [f] }
  | .emit ev _ => { emits := [ev] }
  | .call _ sel _ _ => { calls := [sel] }
  | .view _ sel _ _ => { views := [sel] }
  | .require .. | .revert .. => {}

def Core.effects : {t : RetTy} → Core t → Effects
  | _, .ret _ => {}
  | _, .opTail op => Op.effects op
  | _, .opTailAddr op => Op.effects op
  | _, .opTailFlag op => Op.effects op
  | _, .stmtTail s => Stmt.effects s
  | _, .revertTail .. => {}
  | _, .letOp op k => (Op.effects op).append (Core.effects k)
  | _, .seq s k => (Stmt.effects s).append (Core.effects k)
  | _, .letPure _ _ k => Core.effects k
  | _, .ite _ a b => (Core.effects a).append (Core.effects b)
  | _, .seqIf _ th el k =>
    ((Core.effects th).append (Core.effects el)).append (Core.effects k)

/-- No stores, emits, or state-changing CALLs — allowed as an `implements` View. -/
def Core.isPureRead {t : RetTy} (c : Core t) : Bool :=
  let e := Core.effects c
  e.writes.isEmpty && e.emits.isEmpty && e.calls.isEmpty

/-- The body contains `Op.call` / `Stmt.call` / `Op.view` / `Stmt.view`.
Not `¬ CallFree`: that also excludes emits. Used by the reentrancy lock. -/
def Core.hasExtCall {t : RetTy} (c : Core t) : Bool :=
  let e := Core.effects c
  !e.calls.isEmpty || !e.views.isEmpty

/-- `Op.call` / `Op.view` (CALL / STATICCALL). -/
def Op.isExtCall : Op → Bool
  | .call .. | .view .. | .send .. => true
  | _ => false

/-- `Stmt.call` / `Stmt.view` (discarded CALL / STATICCALL). -/
def Stmt.isExtCall : Stmt → Bool
  | .call .. | .view .. => true
  | _ => false

/-- A storage write (`store` / `storeMap` / `storeMap2`). -/
def Stmt.isStore : Stmt → Bool
  | .store .. | .storeMap .. | .storeMap2 .. => true
  | _ => false

/-- `seen` is whether some prefix already contained an external call.
Structural in the Core (same shape as `Core.effects`) so `lsc_contract`
can reduce it. -/
def Core.storeAfterCallSeen {t : RetTy} (seen : Bool) : Core t → Bool
  | .ret _ => false
  | .opTail _ | .opTailAddr _ | .opTailFlag _ => false
  | .stmtTail s => seen && Stmt.isStore s
  | .revertTail .. => false
  | .letOp op k => Core.storeAfterCallSeen (seen || Op.isExtCall op) k
  | .seq s k =>
    (seen && Stmt.isStore s) ||
      Core.storeAfterCallSeen (seen || Stmt.isExtCall s) k
  | .letPure _ _ k => Core.storeAfterCallSeen seen k
  | .ite _ a b =>
    Core.storeAfterCallSeen seen a || Core.storeAfterCallSeen seen b
  | .seqIf _ th el k =>
    Core.storeAfterCallSeen seen th || Core.storeAfterCallSeen seen el ||
      Core.storeAfterCallSeen seen k

/-- Number of `seqIf` nodes, for reifier tests. -/
def Core.countSeqIf : {t : RetTy} → Core t → Nat
  | _, .seqIf _ th el k =>
    1 + Core.countSeqIf th + Core.countSeqIf el + Core.countSeqIf k
  | _, .ite _ a b => Core.countSeqIf a + Core.countSeqIf b
  | _, .letOp _ k | _, .seq _ k | _, .letPure _ _ k => Core.countSeqIf k
  | _, _ => 0

/-- Syntactic checks-effects-interactions: some path has an `Op`/`Stmt`
store after an external CALL/STATICCALL in program order. Used to reject
`[Reentrant]` functions that write after a call, unless they also carry
`[Reentrant.Unsafe]`. Tail calls are not followed by a store. -/
def Core.storeAfterCall {t : RetTy} (c : Core t) : Bool :=
  Core.storeAfterCallSeen false c

theorem Op.effects_writes (op : Op) : (Op.effects op).writes = [] := by
  cases op <;> rfl

end Lsc
