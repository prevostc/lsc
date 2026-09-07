import Lsc.Compiler.Proof.Erase
import Lsc.Compiler.Proof.Lift
import Lsc.Compiler.Proof.DispatchProof
import Lsc.Compiler.Proof.Descend
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Static memory-footprint of Core→Yul: every `mstore`/`mload`/`keccak`/`call`/
`return`/`log`/`revert` uses a literal range below `memoryGuardK`. A `Run`
of such a block in the ordinary dialect is a `GuardedRun`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect

/-- Pointer/size arguments of a memory-touching op are literals in `[0, base)`. -/
def litNat? : YExpr → Option Nat
  | .lit (.number n) => some n
  | _ => none

def rangeBelow (base p n : Nat) : Bool :=
  decide (p + n ≤ base)

def staticSafeOp (base : Nat) : YOp → List YExpr → Bool
  | .keccak256, [p, n] | .log0, [p, n] | .ret, [p, n] | .revert, [p, n] =>
      match litNat? p, litNat? n with
      | some p, some n => rangeBelow base p n
      | _, _ => false
  | .mload, [p] =>
      match litNat? p with
      | some p => rangeBelow base p 32
      | none => false
  | .mstore, [p, _] =>
      match litNat? p with
      | some p => rangeBelow base p 32
      | none => false
  | .mstore8, [p, _] =>
      match litNat? p with
      | some p => rangeBelow base p 1
      | none => false
  | .log1, [p, n, _] =>
      match litNat? p, litNat? n with
      | some p, some n => rangeBelow base p n
      | _, _ => false
  | .log2, [p, n, _, _] | .log3, [p, n, _, _, _] | .log4, [p, n, _, _, _, _] =>
      match litNat? p, litNat? n with
      | some p, some n => rangeBelow base p n
      | _, _ => false
  | .call, [_, _, _, inp, insz, outp, outsz]
  | .callcode, [_, _, _, inp, insz, outp, outsz] =>
      match litNat? inp, litNat? insz, litNat? outp, litNat? outsz with
      | some ip, some isz, some op, some osz =>
          rangeBelow base ip isz && rangeBelow base op osz
      | _, _, _, _ => false
  | .delegatecall, [_, _, inp, insz, outp, outsz]
  | .staticcall, [_, _, inp, insz, outp, outsz] =>
      match litNat? inp, litNat? insz, litNat? outp, litNat? outsz with
      | some ip, some isz, some op, some osz =>
          rangeBelow base ip isz && rangeBelow base op osz
      | _, _, _, _ => false
  | .calldatacopy, [dst, _, n] | .codecopy, [dst, _, n]
  | .returndatacopy, [dst, _, n] | .datacopy, [dst, _, n] =>
      match litNat? dst, litNat? n with
      | some dst, some n => rangeBelow base dst n
      | _, _ => false
  | .mcopy, [dst, src, n] =>
      match litNat? dst, litNat? src, litNat? n with
      | some dst, some src, some n =>
          rangeBelow base dst n && rangeBelow base src n
      | _, _, _ => false
  | .extcodecopy, [_, dst, _, n] =>
      match litNat? dst, litNat? n with
      | some dst, some n => rangeBelow base dst n
      | _, _ => false
  | .create, [_, p, n] | .create2, [_, p, n, _] =>
      match litNat? p, litNat? n with
      | some p, some n => rangeBelow base p n
      | _, _ => false
  | .msize, _ => false
  | _, _ => true

mutual
def staticSafeExpr (base : Nat) : YExpr → Bool
  | .lit _ | .var _ => true
  | .builtin op args => staticSafeOp base op args && staticSafeExprs base args
  | .call _ args => staticSafeExprs base args

def staticSafeExprs (base : Nat) : List YExpr → Bool
  | [] => true
  | e :: es => staticSafeExpr base e && staticSafeExprs base es

def staticSafeStmt (base : Nat) : YStmt → Bool
  | .block b | .funDef _ _ _ b => staticSafeStmts base b
  | .letDecl _ none => true
  | .letDecl _ (some e) => staticSafeExpr base e
  | .assign _ e | .exprStmt e => staticSafeExpr base e
  | .cond c b => staticSafeExpr base c && staticSafeStmts base b
  | .switch c cases dflt =>
      staticSafeExpr base c && staticSafeCases base cases &&
        match dflt with
        | none => true
        | some b => staticSafeStmts base b
  | .forLoop init c post body =>
      staticSafeStmts base init && staticSafeExpr base c &&
        staticSafeStmts base post && staticSafeStmts base body
  | .break | .continue | .leave => true

def staticSafeStmts (base : Nat) : YBlock → Bool
  | [] => true
  | s :: rest => staticSafeStmt base s && staticSafeStmts base rest

def staticSafeCases (base : Nat) : List (Literal × YBlock) → Bool
  | [] => true
  | (_, b) :: rest => staticSafeStmts base b && staticSafeCases base rest
end

/-! ## Resolve vs erase on a `noYulCall` tail -/

mutual
theorem resolveMemoryGuardExpr_id (base reserved : Nat) (e : YExpr)
    (h : noYulCallExpr e = true) :
    resolveMemoryGuardExpr base reserved e = e := by
  cases e with
  | lit _ | var _ => simp [resolveMemoryGuardExpr]
  | builtin op args =>
    simp only [noYulCallExpr] at h
    simp [resolveMemoryGuardExpr, resolveMemoryGuardArgs_id base reserved args h]
  | call _ _ =>
    simp [noYulCallExpr] at h
termination_by sizeOf e

theorem resolveMemoryGuardArgs_id (base reserved : Nat) (args : List YExpr)
    (h : noYulCallExprs args = true) :
    args.map (resolveMemoryGuardExpr base reserved) = args := by
  cases args with
  | nil => rfl
  | cons e es =>
    simp only [noYulCallExprs, Bool.and_eq_true] at h
    simp [resolveMemoryGuardExpr_id base reserved e h.1,
      resolveMemoryGuardArgs_id base reserved es h.2]
termination_by sizeOf args
end

mutual
theorem resolveMemoryGuardStmt_id (base reserved : Nat) (s : YStmt)
    (h : noYulCallStmt s = true) :
    resolveMemoryGuardStmt base reserved s = s := by
  cases s with
  | block b =>
    simp [resolveMemoryGuardStmt, resolveMemoryGuardStmts_id base reserved b h]
  | funDef n ps rs b =>
    simp [resolveMemoryGuardStmt, resolveMemoryGuardStmts_id base reserved b h]
  | letDecl xs val =>
    cases val with
    | none => simp [resolveMemoryGuardStmt]
    | some e =>
      simp only [noYulCallStmt] at h
      simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved e h]
  | assign xs e =>
    simp only [noYulCallStmt] at h
    simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved e h]
  | cond c b =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved c h.1,
      resolveMemoryGuardStmts_id base reserved b h.2]
  | «switch» c cases dflt =>
    cases dflt with
    | none =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved c h.1.1,
        resolveMemoryGuardCases_id base reserved cases h.1.2]
    | some b =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved c h.1.1,
        resolveMemoryGuardCases_id base reserved cases h.1.2,
        resolveMemoryGuardStmts_id base reserved b h.2]
  | «forLoop» init c post body =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [resolveMemoryGuardStmt, resolveMemoryGuardStmts_id base reserved init h.1.1.1,
      resolveMemoryGuardExpr_id base reserved c h.1.1.2,
      resolveMemoryGuardStmts_id base reserved post h.1.2,
      resolveMemoryGuardStmts_id base reserved body h.2]
  | «break» => simp [resolveMemoryGuardStmt]
  | «continue» => simp [resolveMemoryGuardStmt]
  | «leave» => simp [resolveMemoryGuardStmt]
  | exprStmt e =>
    simp only [noYulCallStmt] at h
    simp [resolveMemoryGuardStmt, resolveMemoryGuardExpr_id base reserved e h]
termination_by sizeOf s

theorem resolveMemoryGuardStmts_id (base reserved : Nat) (b : YBlock)
    (h : noYulCallStmts b = true) :
    resolveMemoryGuardStmts base reserved b = b := by
  cases b with
  | nil => simp [resolveMemoryGuardStmts]
  | cons s rest =>
    simp only [noYulCallStmts, Bool.and_eq_true] at h
    simp [resolveMemoryGuardStmts, resolveMemoryGuardStmt_id base reserved s h.1,
      resolveMemoryGuardStmts_id base reserved rest h.2]
termination_by sizeOf b

theorem resolveMemoryGuardCases_id (base reserved : Nat)
    (cases : List (Literal × YBlock)) (h : noYulCallCases cases = true) :
    resolveMemoryGuardCases base reserved cases = cases := by
  cases cases with
  | nil => simp [resolveMemoryGuardCases]
  | cons p rest =>
    cases p with
    | mk l b =>
      simp only [noYulCallCases, Bool.and_eq_true] at h
      simp [resolveMemoryGuardCases, resolveMemoryGuardStmts_id base reserved b h.1,
        resolveMemoryGuardCases_id base reserved rest h.2]
termination_by sizeOf cases
end

theorem resolveMemoryGuardStmt_memoryGuard (reserved : Nat) :
    resolveMemoryGuardStmt memoryGuardK reserved memoryGuardStmt =
      .cond (lit reserved) [] := by
  simp [memoryGuardStmt, resolveMemoryGuardStmt, resolveMemoryGuardExpr, lit,
    resolveMemoryGuardStmts]

theorem resolve_runtimeBlock {c yul} (h : runtimeBlock c = some yul)
    (reserved : Nat) :
    ∃ cs, c.functions.mapM (entryCase c) = some cs ∧
      resolveMemoryGuardStmts memoryGuardK reserved yul =
        .cond (lit reserved) [] ::
          [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
            YulSemantics.Stmt.switch
              (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
              cs (some [revert00])] := by
  obtain ⟨_, cs, hmap, hy⟩ := runtimeBlock_inv h
  subst yul
  refine ⟨cs, hmap, ?_⟩
  have htail := noYulCall_dispatchTail (emitGuardLt {} 4).stmts _ cs
    (noYulCall_guardLt 4) noYulCall_selector (mapM_entryCase_noYulCall hmap)
  rw [resolveMemoryGuardStmts, resolveMemoryGuardStmt_memoryGuard,
    resolveMemoryGuardStmts_id _ _ _ htail]

/-! ## Both discarded guards are state-identity `if ≠ 0 {}` -/

theorem reserved_ne_zero {n : Nat} (hn : n ≠ 0) (hlt : n < wordBound) :
    evm.litValue (.number n) ≠ Dialect.zero evm := by
  intro heq
  have h1 : (BitVec.ofNat 256 n).toNat = n := toNat_ofNat_of_lt hlt
  have h0 : (BitVec.ofNat 256 0).toNat = 0 := by simp
  have : n = 0 := by
    simp [Dialect.zero, litValue] at heq
    exact h1.symm.trans ((congrArg BitVec.toNat heq).trans h0)
  exact hn this

theorem exec_cond_lit_empty {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {n : Nat}
    (hne : D.litValue (.number n) ≠ D.zero) :
    ExecStmt D funs V st (.cond (.lit (.number n)) []) V st .normal := by
  have hbody : ExecStmt D funs V st (.block []) V st .normal := by
    have hb : ExecStmt D funs V st (.block []) (restore V V) st .normal :=
      Step.block (D := D) (by
        change ExecStmts D (hoist D [] :: funs) V st [] V st .normal
        exact Step.seqNil)
    simpa [restore] using hb
  exact Step.ifTrue (D := D) (Step.lit (D := D)) hne hbody

theorem exec_memoryGuardResolved {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {n : Nat} (hn : n ≠ 0) (hlt : n < wordBound) :
    ExecStmt evm funs V st (.cond (lit n) []) V st .normal := by
  simpa [lit] using
    exec_cond_lit_empty (D := evm) (reserved_ne_zero hn hlt)

/-- Remaining lift into `guardedEvm`: a `Run` of `resolve … rt` in the ordinary
dialect is a `GuardedRun` once every executed builtin satisfies `OpMemorySafe`
(`staticSafeStmts memoryGuardK`). Not discharged here for general `emitCore`. -/
def GuardedRunOfErased (rt : YBlock) (r : Result) (yst0 yst' : EvmState)
    (o : Outcome) : Prop :=
  Run (evmWithExternal ExternalCalls.none ExternalCreates.none ExternalGas.any)
      (eraseMemoryGuardStmts rt) yst0 [] yst' o →
    GuardedRun ExternalCalls.none ExternalCreates.none rt r.base r.reserved
      yst0 [] yst' o

end Lsc.Compiler
