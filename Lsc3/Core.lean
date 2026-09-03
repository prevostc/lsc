import Lsc3.Amount

/-!
# LSC v3 — the Core AST and its denotation

`Core` is a tiny first-order, loop-free, A-normal-form language that mirrors exactly the
shapes Lean's `do` elaborator produces for programs in the reifiable fragment:

* `bind op (fun x => k)`       ↦ `letOp op k` (word-valued primitive) / `seq s k` (unit statement)
* `let x := p a b; k`          ↦ `letPure p [a, b] k`
* `if c then a else b`         ↦ `ite c a b`
* `pure v` in tail position    ↦ `ret v`
* tail primitives              ↦ `opTail` / `stmtTail` / `revertTail`

Join points (`have __do_jp := fun y => rest; …`) are eliminated by the reifier through
leaf substitution, which is definitionally what Lean's ζ/β-reduction does to them, so
`Core.denote` never has to reason about them.

Locals are de Bruijn indices into an environment of words (`var 0` is the most recently
bound value; function parameters are the initial environment, last parameter first).
Storage fields, events and errors are referenced by index through a `ContractSchema`,
which `lsc_schema` generates from the user's Lean `structure`/`inductive`s. Every case of
`denote` is *literally* the surface primitive applied to evaluated atoms, which is what
makes `Core.denote (reify f) = f` hold by `rfl`.
-/

namespace Lsc3

/-- Operands: a local (de Bruijn index) or a word literal. -/
inductive Atom
  | var (i : Nat)
  | lit (n : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

def Atom.eval (env : List Nat) : Atom → Nat
  | .var i => env.getD i 0
  | .lit n => n

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
  | erc20TransferFrom (tok src to amt : Atom)
  | erc20Transfer (tok to amt : Atom)
  | erc20BalanceOf (tok owner : Atom)
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
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Return types of contract functions. -/
inductive RetTy
  | unit
  | word
  | addr
  | flag
  | pair (a b : RetTy)
  deriving DecidableEq, Repr, Lean.ToExpr

def RetTy.denote : RetTy → Type
  | .unit => Unit
  | .word => Nat
  | .addr => Address
  | .flag => Flag
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

structure EvSchema (E : Type) where
  build : Nat → List Nat → E

structure ErrSchema (ε : Type) where
  build : Nat → List Nat → ε

structure ContractSchema (S E ε : Type) where
  st : StorageSchema S
  ev : EvSchema E
  err : ErrSchema ε

/-! ## Denotation -/

variable {S E ε : Type}

def Op.denote (Γ : ContractSchema S E ε) (env : List Nat) : Op → Tx S E ε Nat
  | .load f => Tx.load (Γ.st.scalar f)
  | .loadMap f k => Tx.loadMap (Γ.st.map1 f) (k.eval env)
  | .loadMap2 f k₁ k₂ => Tx.loadMap2 (Γ.st.map2 f) (k₁.eval env) (k₂.eval env)
  | .sender => Tx.sender
  | .value => Tx.value
  | .timestamp => Tx.timestamp
  | .blockNumber => Tx.blockNumber
  | .selfAddress => Tx.selfAddress
  | .addChecked a b => Tx.addChecked (a.eval env) (b.eval env)
  | .subChecked a b => Tx.subChecked (a.eval env) (b.eval env)
  | .mulChecked a b => Tx.mulChecked (a.eval env) (b.eval env)
  | .divChecked a b => Tx.divChecked (a.eval env) (b.eval env)
  | .mulDivDown a b c => Tx.mulDivDown (a.eval env) (b.eval env) (c.eval env)
  | .mulDivUp a b c => Tx.mulDivUp (a.eval env) (b.eval env) (c.eval env)
  | .erc20TransferFrom tok src to amt =>
    Tx.erc20TransferFrom (tok.eval env) (src.eval env) (to.eval env) (amt.eval env)
  | .erc20Transfer tok to amt => Tx.erc20Transfer (tok.eval env) (to.eval env) (amt.eval env)
  | .erc20BalanceOf tok owner => Tx.erc20BalanceOf (tok.eval env) (owner.eval env)
  | .pure a => Pure.pure (a.eval env)

def Stmt.denote (Γ : ContractSchema S E ε) (env : List Nat) : Stmt → Tx S E ε Unit
  | .store f v => Tx.store (Γ.st.scalarUpd f) (v.eval env)
  | .storeMap f k v => Tx.storeMap (Γ.st.map1 f) (Γ.st.map1Upd f) (k.eval env) (v.eval env)
  | .storeMap2 f k₁ k₂ v =>
    Tx.storeMap2 (Γ.st.map2 f) (Γ.st.map2Upd f) (k₁.eval env) (k₂.eval env) (v.eval env)
  | .require c err args => Tx.require (c.denote env) (Γ.err.build err (args.map (·.eval env)))
  | .emit ev args => Tx.emit (Γ.ev.build ev (args.map (·.eval env)))
  | .revert err args => Tx.revert (Γ.err.build err (args.map (·.eval env)))

def Core.denote (Γ : ContractSchema S E ε) : {t : RetTy} → Core t → List Nat → Tx S E ε t.denote
  | _, .ret r, env => pure (r.eval env)
  | _, .opTail op, env => Op.denote Γ env op
  | _, .opTailAddr op, env => (Op.denote Γ env op : Tx S E ε Nat)
  | _, .opTailFlag op, env => (Op.denote Γ env op : Tx S E ε Nat)
  | _, .stmtTail s, env => Stmt.denote Γ env s
  | _, .revertTail err args, env => Tx.revert (Γ.err.build err (args.map (·.eval env)))
  | _, .letOp op k, env => Op.denote Γ env op >>= fun v => Core.denote Γ k (v :: env)
  | _, .seq s k, env => Stmt.denote Γ env s >>= fun _ => Core.denote Γ k env
  | _, .letPure p args k, env => Core.denote Γ k (Prim.eval p (args.map (·.eval env)) :: env)
  | _, .ite c a b, env => if c.denote env then Core.denote Γ a env else Core.denote Γ b env

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
  | .erc20TransferFrom tok src to amt =>
    .erc20TransferFrom (tok.rename ρ) (src.rename ρ) (to.rename ρ) (amt.rename ρ)
  | .erc20Transfer tok to amt => .erc20Transfer (tok.rename ρ) (to.rename ρ) (amt.rename ρ)
  | .erc20BalanceOf tok owner => .erc20BalanceOf (tok.rename ρ) (owner.rename ρ)
  | .pure a => .pure (a.rename ρ)

def Stmt.rename (ρ : Nat → Atom) : Stmt → Stmt
  | .store f v => .store f (v.rename ρ)
  | .storeMap f k v => .storeMap f (k.rename ρ) (v.rename ρ)
  | .storeMap2 f k₁ k₂ v => .storeMap2 f (k₁.rename ρ) (k₂.rename ρ) (v.rename ρ)
  | .require c err args => .require (c.rename ρ) err (args.map (·.rename ρ))
  | .emit ev args => .emit ev (args.map (·.rename ρ))
  | .revert err args => .revert err (args.map (·.rename ρ))

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
    go c

end Lsc3
