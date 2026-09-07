import Lsc.Compiler.Proof.Ops

/-!
Call-free (S1) fragment of Core: the hypothesis of `toYulFn_correct_callFree`.
-/

namespace Lsc.Compiler

open Lsc

/-- S1 cores: the ops/stmts in `M1Op`/`M1Stmt`, identity `letPure`, and
`word × word` returns. Excludes wrapping `letPure`, other emit arities, and
nested pairs. -/
def M1Frag : {t : RetTy} → Core t → Prop
  | .unit, .ret _ => True
  | .word, .ret _ => True
  | .addr, .ret _ => True
  | .flag, .ret _ => True
  | .pair .word .word, .ret _ => True
  | .word, .opTail op => M1Op op
  | .addr, .opTailAddr op => M1Op op
  | .flag, .opTailFlag op => M1Op op
  | _, .stmtTail s => M1Stmt s
  | _, .revertTail _ args => args.length = 0
  | _, .letOp op k => M1Op op ∧ M1Frag k
  | _, .seq s k => M1Stmt s ∧ M1Frag k
  | _, .letPure p args k => p = .id ∧ args.length = 1 ∧ M1Frag k
  | _, .ite c a b => M1Cond c ∧ M1Frag a ∧ M1Frag b
  | _, _ => False

def CallFreeOp : Lsc.Op → Prop := M1Op
def CallFreeStmt : Lsc.Stmt → Prop := M1Stmt

/-- Call-free = `M1Frag`. This is the S1 compiler fragment: Counter and Token
bodies, and the call-free constructors. `Op.call` / `Stmt.call` need S2. -/
def CallFree : {t : RetTy} → Core t → Prop := M1Frag

/-! ## Boolean reflection of `M1Op` / `M1Stmt` / `M1Frag`

These are the `decide`/`rfl` forms of the S1 fragment predicates. The `Prop`
names stay the vocabulary of exported theorems; instantiation uses the `Bool`. -/

def m1OpB : Lsc.Op → Bool
  | .load _ | .loadMap _ _ | .loadMap2 _ _ _ => true
  | .sender | .value | .timestamp | .blockNumber | .selfAddress => true
  | .addChecked _ _ | .subChecked _ _ | .mulChecked _ _ | .divChecked _ _ => true
  | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .pure _ => true
  | .call _ _ _ => false

def m1StmtB : Lsc.Stmt → Bool
  | .store _ _ | .storeMap _ _ _ | .storeMap2 _ _ _ _ => true
  | .emit _ args =>
      args.length == 0 || args.length == 1 || args.length == 3 || args.length == 4
  | .require _ _ args => args.length == 0
  | .revert _ args => args.length == 0
  | .call _ _ _ => false

def m1FragB : {t : RetTy} → Core t → Bool
  | .unit, .ret _ => true
  | .word, .ret _ => true
  | .addr, .ret _ => true
  | .flag, .ret _ => true
  | .pair .word .word, .ret _ => true
  | .word, .opTail op => m1OpB op
  | .addr, .opTailAddr op => m1OpB op
  | .flag, .opTailFlag op => m1OpB op
  | _, .stmtTail s => m1StmtB s
  | _, .revertTail _ args => args.length == 0
  | _, .letOp op k => m1OpB op && m1FragB k
  | _, .seq s k => m1StmtB s && m1FragB k
  | _, .letPure p args k => decide (p = .id) && args.length == 1 && m1FragB k
  | _, .ite _ a b => m1FragB a && m1FragB b
  | _, _ => false

def callFreeB {t : RetTy} (core : Core t) : Bool := m1FragB core

theorem m1OpB_eq (op : Lsc.Op) : m1OpB op = true ↔ M1Op op := by
  cases op <;> simp [m1OpB, M1Op]

theorem m1StmtB_eq (s : Lsc.Stmt) : m1StmtB s = true ↔ M1Stmt s := by
  cases s with
  | store _ _ | storeMap _ _ _ | storeMap2 _ _ _ _ => simp [m1StmtB, M1Stmt]
  | emit _ args => simp [m1StmtB, M1Stmt]; tauto
  | require c _ args => simp [m1StmtB, M1Stmt, M1Cond]
  | revert _ args => simp [m1StmtB, M1Stmt]
  | call _ _ _ => simp [m1StmtB, M1Stmt]

theorem m1FragB_eq {t} (core : Core t) : m1FragB core = true ↔ M1Frag core := by
  induction core with
  | ret r =>
    cases r with
    | unit | word _ | addr _ | flag _ => simp [m1FragB, M1Frag]
    | pair x y =>
      cases x with
      | word _ =>
        cases y with
        | word _ => simp [m1FragB, M1Frag]
        | unit | addr _ | flag _ | pair _ _ => simp [m1FragB, M1Frag]
      | unit | addr _ | flag _ | pair _ _ => simp [m1FragB, M1Frag]
  | opTail op => simp [m1FragB, M1Frag, m1OpB_eq]
  | opTailAddr op => simp [m1FragB, M1Frag, m1OpB_eq]
  | opTailFlag op => simp [m1FragB, M1Frag, m1OpB_eq]
  | stmtTail s => simp [m1FragB, M1Frag, m1StmtB_eq]
  | revertTail _ args => simp [m1FragB, M1Frag]
  | letOp op k ih =>
    simp [m1FragB, M1Frag, m1OpB_eq, ih]
  | seq s k ih =>
    simp [m1FragB, M1Frag, m1StmtB_eq, ih]
  | letPure p args k ih =>
    simp [m1FragB, M1Frag, ih, and_assoc]
  | ite _ a b iha ihb =>
    simp [m1FragB, M1Frag, M1Cond, iha, ihb]

theorem callFreeB_eq {t} (core : Core t) : callFreeB core = true ↔ CallFree core :=
  m1FragB_eq core

instance (op : Lsc.Op) : Decidable (M1Op op) :=
  decidable_of_iff (m1OpB op = true) (m1OpB_eq op)

instance (s : Lsc.Stmt) : Decidable (M1Stmt s) :=
  decidable_of_iff (m1StmtB s = true) (m1StmtB_eq s)

instance {t} (core : Core t) : Decidable (M1Frag core) :=
  decidable_of_iff (m1FragB core = true) (m1FragB_eq core)

instance {t} (core : Core t) : Decidable (CallFree core) :=
  inferInstanceAs (Decidable (M1Frag core))

/-- Every function of a concrete `ContractDef` is call-free when the Boolean
check reduces. Discharge the hypothesis with `decide` or `rfl`. -/
theorem callFree_of_all {c : ContractDef}
    (h : c.functions.all (fun f => callFreeB f.core) = true) :
    ∀ f ∈ c.functions, CallFree f.core :=
  fun f hf => (callFreeB_eq f.core).mp ((List.all_eq_true.mp h) f hf)

end Lsc.Compiler
