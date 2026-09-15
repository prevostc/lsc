import Lsc.Compiler.LockDefs
import Lsc.Compiler.Bytecode
import Lsc.Compiler.Proof.Erase
import Lsc.Compiler.Proof.SpillPath
import Lsc.Compiler.Proof.MemFootprint
import Lsc.Compiler.Proof.MemFootprintLift
import YulEvmCompiler.Compile
import YulEvmCompiler.AsmPeephole
import YulEvmCompiler.Decode
import YulEvmCompiler.Value
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound

set_option linter.unusedSimpArgs false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option autoImplicit false

/-!
Compile-equation unfolding of the runtime prologue (slice 8C-1).
Inversions follow `YulEvmCompiler.SimAsm`'s `simp only [compileStmt]`
pattern; we do not compile the prefix alone (`wfCheck` is whole-program).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect

namespace Proof

/-! ### Compile-equation inversions (pinned `Compile.lean`) -/

theorem compileExpr_lit (Φ : FMap) (Γ : List Ident) (off n : Nat)
    (l : Literal) :
    compileExpr Φ Γ off n (.lit l) = some ([.push (litValue l)], n) := by
  simp only [compileExpr]

theorem compileArgs_nil (Φ : FMap) (Γ : List Ident) (off n : Nat) :
    compileArgs Φ Γ off n [] = some ([], n) := by
  simp only [compileArgs]

theorem compileArgs_one_lit (Φ : FMap) (Γ : List Ident) (off n : Nat)
    (l : Literal) :
    compileArgs Φ Γ off n [.lit l] = some ([.push (litValue l)], n) := by
  simp only [compileArgs, compileExpr]
  rfl

theorem compileArgs_two_lit (Φ : FMap) (Γ : List Ident) (off n : Nat)
    (l₁ l₂ : Literal) :
    compileArgs Φ Γ off n [.lit l₁, .lit l₂] =
      some ([.push (litValue l₂), .push (litValue l₁)], n) := by
  simp only [compileArgs, compileExpr]
  rfl

theorem compileExpr_tload (Φ : FMap) (Γ : List Ident) (off n : Nat)
    (l : Literal) :
    compileExpr Φ Γ off n (.builtin .tload [.lit l]) =
      some ([.push (litValue l), .op .tload], n) := by
  simp only [compileExpr, compileArgs]
  rfl

theorem litValue_number_zero : litValue (.number 0) = 0 := rfl

theorem compileExpr_revert00 (Φ : FMap) (Γ : List Ident) (off n : Nat) :
    compileExpr Φ Γ off n
        (.builtin .revert [.lit (.number 0), .lit (.number 0)]) =
      some ([.push 0, .push 0, .op .revert], n) := by
  simp only [compileExpr, compileArgs, litValue_number_zero]
  rfl

theorem compileStmts_nil (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (n : Nat) :
    compileStmts Φ Γ F L n [] = some ([], Γ, n) := by
  simp only [compileStmts]

theorem hoistInfos_nil (n : Nat) : hoistInfos n [] = ([], n) := rfl

theorem hoistInfos_cond (n : Nat) (c : YExpr) (b rest : YBlock) :
    hoistInfos n (.cond c b :: rest) = hoistInfos n rest := rfl

theorem hoistInfos_exprStmt (n : Nat) (e : YExpr) (rest : YBlock) :
    hoistInfos n (.exprStmt e :: rest) = hoistInfos n rest := rfl

theorem hoistInfos_block (n : Nat) (b rest : YBlock) :
    hoistInfos n (.block b :: rest) = hoistInfos n rest := rfl

theorem hoistInfos_switch (n : Nat) (c : YExpr)
    (cs : List (Literal × YBlock)) (d : Option YBlock) (rest : YBlock) :
    hoistInfos n (.switch c cs d :: rest) = hoistInfos n rest := rfl

theorem yulCompileBlock_nil (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (n : Nat) :
    YulEvmCompiler.compileBlock Φ Γ F L n [] = some ([], n) := by
  rw [YulEvmCompiler.compileBlock, hoistInfos_nil]
  simp [compileStmts]

theorem compileStmt_cond_empty (Φ : FMap) (Γ : List Ident)
    (F : Option FunCtx) (L : Option LoopCtx) (n : Nat) (l : Literal) :
    compileStmt Φ Γ F L n (.cond (.lit l) []) =
      some ([.push (litValue l), .op .iszero, .jumpi n, .label n], Γ, n + 1) := by
  simp only [compileStmt, Option.bind_eq_bind, compileExpr_lit, yulCompileBlock_nil]
  simp

theorem compileStmts_cons_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {s : YStmt}
    {rest : YBlock} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmts Φ Γ F L n (s :: rest) = some (asm, Γ', n')) :
    ∃ (is1 : List Asm) (Γ1 : List Ident) (n1 : Nat) (is2 : List Asm),
      compileStmt Φ Γ F L n s = some (is1, Γ1, n1)
      ∧ compileStmts Φ Γ1 F L n1 rest = some (is2, Γ', n')
      ∧ asm = is1 ++ is2 := by
  simp only [compileStmts, Option.bind_eq_bind] at h
  obtain ⟨⟨is1, Γ1, n1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨is2, Γ2, n2⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  exact ⟨is1, Γ1, n1, is2, h1, h4.2.1 ▸ h4.2.2 ▸ h3, h4.1.symm⟩

theorem yulCompileBlock_revert00 (Φ : FMap) (Γ : List Ident)
    (F : Option FunCtx) (L : Option LoopCtx) (n : Nat) :
    YulEvmCompiler.compileBlock Φ Γ F L n
        [.exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)])] =
      some ([.push 0, .push 0, .op .revert], n) := by
  rw [YulEvmCompiler.compileBlock, hoistInfos_exprStmt, hoistInfos_nil]
  simp [compileStmts, compileStmt, compileExpr_revert00]

theorem compileStmt_lockCheck (Φ : FMap) (Γ : List Ident)
    (F : Option FunCtx) (L : Option LoopCtx) (n : Nat) :
    compileStmt Φ Γ F L n lockCheckStmt =
      some ([.push 0, .op .tload, .op .iszero, .jumpi n,
        .push 0, .push 0, .op .revert, .label n], Γ, n + 1) := by
  unfold lockCheckStmt revert00 bop lit reentrancyLockSlot
  simp only [compileStmt, Option.bind_eq_bind, compileExpr_tload,
    yulCompileBlock_revert00]
  simp [litValue]

theorem compileStmt_cond_lit (Φ : FMap) (Γ : List Ident)
    (F : Option FunCtx) (L : Option LoopCtx) (n k : Nat) :
    compileStmt Φ Γ F L n (.cond (lit k) []) =
      some ([.push (BitVec.ofNat 256 k), .op .iszero, .jumpi n, .label n],
        Γ, n + 1) := by
  simp [lit, compileStmt_cond_empty, litValue]

theorem compileStmts_lockPrefix (Φ : FMap) (Γ : List Ident)
    (F : Option FunCtx) (L : Option LoopCtx) (k : Nat) (rest : YBlock)
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmts Φ Γ F L 0
        (.cond (lit k) [] :: lockCheckStmt :: rest) = some (asm, Γ', n')) :
    ∃ restAsm, compileStmts Φ Γ F L 2 rest = some (restAsm, Γ', n') ∧
      asm = lockPrefixAsmRaw k ++ restAsm := by
  obtain ⟨is1, Γ1, n1, is2, h1, h2, rfl⟩ := compileStmts_cons_inv h
  simp only [compileStmt_cond_lit, Option.some.injEq, Prod.mk.injEq] at h1
  rcases h1 with ⟨rfl, rfl, hn1⟩
  subst hn1
  obtain ⟨isL, Γ2, n2, restAsm, hL, hrest, rfl⟩ := compileStmts_cons_inv h2
  simp only [compileStmt_lockCheck, Option.some.injEq, Prod.mk.injEq] at hL
  rcases hL with ⟨rfl, rfl, hn2⟩
  subst hn2
  have hn : (0 + 1 + 1 : Nat) = 2 := rfl
  rw [hn] at hrest
  exact ⟨restAsm, hrest, by simp [lockPrefixAsmRaw]⟩

theorem compileProgram_inv {prog : YBlock} {asm : List Asm}
    (h : compileProgram prog = some asm) :
    ∃ (scope : FScopeInfo) (n0 : Nat) (asm' : List Asm) (Γ : List Ident)
      (n' : Nat),
      hoistInfos 0 prog = (scope, n0) ∧
      (scope.map Prod.fst).Nodup ∧
      compileStmts [scope] [] none none n0 prog = some (asm', Γ, n') ∧
      wfCheck asm' = true ∧ asm = asm' := by
  rw [compileProgram] at h
  rcases hh : hoistInfos 0 prog with ⟨scope, n0⟩
  rw [hh] at h
  dsimp only at h
  by_cases hnd : (scope.map Prod.fst).Nodup
  · rw [decide_eq_true hnd] at h
    simp at h
    obtain ⟨⟨asm', Γ, n'⟩, hs, hw⟩ := Option.bind_eq_some_iff.mp h
    split at hw
    · next hwf =>
      simp only [Option.some.injEq] at hw
      exact ⟨scope, n0, asm', Γ, n', rfl, hnd, hs, hwf, hw.symm⟩
    · cases hw
  · rw [decide_eq_false hnd] at h
    simp at h

theorem yulCompile_inv {prog : YBlock} {is : List Instr}
    (h : YulEvmCompiler.compile prog = some is) :
    ∃ asm, compileProgram prog = some asm ∧
      stackOK2 (optimizeAsm asm) = true ∧
      lowerProg unpatchedImmutables (optimizeAsm asm) = some is := by
  simp only [YulEvmCompiler.compile, Option.bind_eq_bind] at h
  obtain ⟨asm, hp, h2⟩ := Option.bind_eq_some_iff.mp h
  split at h2
  · next hok => exact ⟨asm, hp, hok, h2⟩
  · exact absurd h2 (by simp)

/-! ### Runtime Yul shape (erase and spill) -/

theorem hoistInfos_erased_runtime {c : ContractDef} {yul : YBlock}
    (h : runtimeBlock c = some yul) :
    hoistInfos 0 (eraseMemoryGuardStmts yul) = ([], 0) := by
  obtain ⟨cases, _, hE⟩ := erase_runtimeBlock h
  rw [hE]
  simp [memoryGuardErased, lockCheckStmt, hoistInfos]

theorem rewriteExpr_lit (slots : SlotMap) (owner : Owner) (l : Literal) :
    rewriteExpr slots owner (.lit l) = .lit l := rfl

theorem rewriteArgs_nil (slots : SlotMap) (owner : Owner) :
    rewriteArgs slots owner [] = [] := rfl

theorem rewriteArgs_one_lit (slots : SlotMap) (owner : Owner) (l : Literal) :
    rewriteArgs slots owner [.lit l] = [.lit l] := by
  simp [rewriteArgs, rewriteExpr_lit]

theorem rewriteArgs_two_lit (slots : SlotMap) (owner : Owner)
    (l₁ l₂ : Literal) :
    rewriteArgs slots owner [.lit l₁, .lit l₂] = [.lit l₁, .lit l₂] := by
  simp [rewriteArgs, rewriteExpr_lit]

theorem rewriteExpr_tload_lit (slots : SlotMap) (owner : Owner) (l : Literal) :
    rewriteExpr slots owner (.builtin .tload [.lit l]) =
      .builtin .tload [.lit l] := by
  simp [rewriteExpr, rewriteArgs_one_lit]

theorem rewriteExpr_revert00 (slots : SlotMap) (owner : Owner) :
    rewriteExpr slots owner
        (.builtin .revert [.lit (.number 0), .lit (.number 0)]) =
      .builtin .revert [.lit (.number 0), .lit (.number 0)] := by
  simp [rewriteExpr, rewriteArgs_two_lit]

theorem rewriteStmt_cond_empty_lit (slots : SlotMap) (owner : Owner)
    (exitCopies : YBlock) (k : Nat) :
    rewriteStmt slots owner exitCopies (.cond (lit k) []) =
      [.cond (lit k) []] := by
  simp [rewriteStmt, rewriteExpr_lit, rewriteStmts, lit]

theorem rewriteStmt_lockCheck (slots : SlotMap) (owner : Owner)
    (exitCopies : YBlock) :
    rewriteStmt slots owner exitCopies lockCheckStmt = [lockCheckStmt] := by
  unfold lockCheckStmt revert00 bop lit reentrancyLockSlot
  simp [rewriteStmt, rewriteExpr_tload_lit, rewriteStmts,
    rewriteExpr_revert00]

theorem rewriteStmts_cons (slots : SlotMap) (owner : Owner)
    (exitCopies : YBlock) (s : YStmt) (rest : YBlock) :
    rewriteStmts slots owner exitCopies (s :: rest) =
      rewriteStmt slots owner exitCopies s ++
        rewriteStmts slots owner exitCopies rest := by
  simp [rewriteStmts]

theorem spilled_runtime_prefix_block {c : ContractDef} {rt : YBlock}
    {r : Result} (hrt : runtimeBlock c = some rt)
    (hsp : spillRuntime? rt = some r) :
    ∃ rest, r.block = .cond (lit r.reserved) [] :: lockCheckStmt :: rest ∧
      r.base = memoryGuardK := by
  have hbase : r.base = memoryGuardK := spillRuntime_base hrt hsp
  obtain ⟨_, hf⟩ := spillBlock_facts (by simpa [spillRuntime?] using hsp)
  obtain ⟨cs, _, hR⟩ := resolve_runtimeBlock hrt r.reserved
  rw [← hbase] at hR
  refine ⟨rewriteStmts r.layout.slots none []
      [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
        YulSemantics.Stmt.switch
          (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
          cs (some [revert00])], ?_, hbase⟩
  rw [hf.block_eq, hR, rewriteStmts_cons, rewriteStmt_cond_empty_lit,
    rewriteStmts_cons, rewriteStmt_lockCheck]
  simp [rewriteStmts]

/-! ### Label-counter monotonicity -/

def Φentries : FMap → List Label
  | [] => []
  | scope :: rest => scope.map (fun p => p.2.entry) ++ Φentries rest

def allowedLabel (n : Nat) (Φ : FMap) (F : Option FunCtx)
    (L : Option LoopCtx) (l : Label) : Prop :=
  n ≤ l ∨ l ∈ Φentries Φ ∨
    (∃ fc, F = some fc ∧ l = fc.exit) ∨
    (∃ lc, L = some lc ∧ (l = lc.brk ∨ l = lc.cont))

theorem Φentries_nil : Φentries [] = [] := rfl

theorem Φentries_empty_scope : Φentries [[]] = [] := rfl

theorem allowedLabel_ge {n Φ F L l} (h : allowedLabel n Φ F L l)
    (hΦ : Φentries Φ = []) (hF : F = none) (hL : L = none) : n ≤ l := by
  rcases h with h | h | h | h
  · exact h
  · simp [hΦ] at h
  · obtain ⟨fc, hF', _⟩ := h; cases hF.symm.trans hF'
  · obtain ⟨lc, hL', _⟩ := h; cases hL.symm.trans hL'

theorem lookupF_entry {Φ : FMap} {f : Ident} {info : FunInfo} {Φv : FMap}
    (h : lookupF Φ f = some (info, Φv)) : info.entry ∈ Φentries Φ := by
  induction Φ with
  | nil => simp [lookupF] at h
  | cons scope rest ih =>
    unfold lookupF at h
    cases hfind : scope.find? (fun p => p.1 = f) with
    | none =>
      simp only [hfind] at h
      exact List.mem_append.mpr (Or.inr (ih h))
    | some p =>
      simp only [hfind] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      have hp : p ∈ scope := List.mem_of_find?_eq_some hfind
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩))

theorem hoistInfos_entries (n : Nat) (body : YBlock) :
    n ≤ (hoistInfos n body).2 ∧
      ∀ q ∈ (hoistInfos n body).1,
        n ≤ q.2.entry ∧ q.2.entry < (hoistInfos n body).2 := by
  induction body generalizing n with
  | nil => simp [hoistInfos]
  | cons s rest ih =>
    cases s with
    | funDef f ps rs b =>
      simp only [hoistInfos]
      have ⟨hle, hent⟩ := ih (n + 1)
      refine ⟨Nat.le_trans (Nat.le_succ n) hle, ?_⟩
      intro q hq
      simp at hq
      rcases hq with hq | hq
      · subst q
        exact ⟨Nat.le_refl _, Nat.lt_of_succ_le hle⟩
      · have ⟨hle', hlt⟩ := hent q hq
        exact ⟨Nat.le_trans (Nat.le_succ n) hle', hlt⟩
    | _ => simpa [hoistInfos] using ih n

theorem allowedLabel_mono {n n' Φ F L l} (hle : n ≤ n')
    (h : allowedLabel n' Φ F L l) : allowedLabel n Φ F L l := by
  rcases h with h | h | h | h
  · exact Or.inl (le_trans hle h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem allowedLabel_cons_scope {n Φ F L l} {scope : FScopeInfo}
    (h : allowedLabel n (scope :: Φ) F L l)
    (hent : ∀ q ∈ scope, n ≤ q.2.entry) :
    allowedLabel n Φ F L l := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · unfold Φentries at h
    rw [List.mem_append] at h
    rcases h with h | h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact Or.inl (hent q hq)
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### Compile-time label lower bounds -/

theorem yulCompileBlock_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {body : YBlock} {asm : List Asm} {n' : Nat}
    (h : YulEvmCompiler.compileBlock Φ Γ F L n body = some (asm, n')) :
    ∃ (scope : FScopeInfo) (n1 : Nat) (stmtsAsm : List Asm) (Γb : List Ident)
      (n2 : Nat),
      hoistInfos n body = (scope, n1) ∧
      (scope.map Prod.fst).Nodup ∧
      compileStmts (scope :: Φ) Γ F L n1 body = some (stmtsAsm, Γb, n2) ∧
      asm = stmtsAsm ++ List.replicate (Γb.length - Γ.length) .pop ∧
      n' = n2 := by
  rw [YulEvmCompiler.compileBlock] at h
  rcases hh : hoistInfos n body with ⟨scope, n1⟩
  rw [hh] at h
  dsimp only at h
  by_cases hnd : (scope.map Prod.fst).Nodup
  · rw [if_pos hnd, Option.bind_eq_bind] at h
    obtain ⟨⟨stmtsAsm, Γb, n2⟩, hs, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨scope, n1, stmtsAsm, Γb, n2, rfl, hnd, hs, h2.1.symm, h2.2.symm⟩
  · rw [if_neg hnd] at h
    exact absurd h (by simp)

theorem labelRefs_pop_replicate (k : Nat) :
    labelRefs (List.replicate k Asm.pop) = [] := by
  induction k with
  | zero => simp [labelRefs]
  | succ k ih => simp [labelRefs, Asm.references, ih]

theorem labelRefs_of_pops {p q : List Asm} (h : q = List.replicate q.length Asm.pop) :
    labelRefs (p ++ q) = labelRefs p := by
  rw [h, labelRefs_append, labelRefs_pop_replicate, List.append_nil]

theorem labelRefs_push_replicate (k : Nat) :
    labelRefs (List.replicate k (Asm.push (0 : BitVec 256))) = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, labelRefs_cons, Asm.references,
      Option.toList_none, List.nil_append]
    exact ih

theorem labelRefs_cons_none {i : Asm} {p : List Asm}
    (h : i.references = none) : labelRefs (i :: p) = labelRefs p := by
  rw [labelRefs_cons, h]; rfl

theorem labelRefs_cons_some {i : Asm} {p : List Asm} {l : Label}
    (h : i.references = some l) : labelRefs (i :: p) = l :: labelRefs p := by
  rw [labelRefs_cons, h]; rfl

theorem labelRefs_iszero_jumpi (l : Label) :
    labelRefs [Asm.op .iszero, Asm.jumpi l] = [l] := by
  rw [labelRefs_cons_none (by rfl), labelRefs_cons_some (by rfl), labelRefs_nil]

theorem labelRefs_label_one (l : Label) :
    labelRefs [Asm.label l] = [] := by
  rw [labelRefs_cons_none (by rfl), labelRefs_nil]

theorem labelRefs_jump_one (l : Label) :
    labelRefs [Asm.jump l] = [l] := by
  rw [labelRefs_cons_some (by rfl), labelRefs_nil]

theorem labelRefs_jump_label (e l : Label) :
    labelRefs [Asm.jump e, Asm.label l] = [e] := by
  rw [labelRefs_cons_some (by rfl), labelRefs_label_one]

mutual

def compileExpr_labels {Φ : FMap} {Γ : List Ident} {off n : Nat}
    (e : YExpr) {asm : List Asm} {n' : Nat}
    (h : compileExpr Φ Γ off n e = some (asm, n')) :
    n ≤ n' ∧ ∀ l ∈ labelRefs asm, n ≤ l ∨ l ∈ Φentries Φ := by
  cases e with
  | lit l =>
    simp only [compileExpr, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [labelRefs, Asm.references]
  | var x =>
    simp only [compileExpr, Option.bind_eq_bind] at h
    obtain ⟨idx, hidx, h2⟩ := Option.bind_eq_some_iff.mp h
    by_cases h16 : off + idx < 16
    · rw [dif_pos h16] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl, rfl⟩
      simp [labelRefs, Asm.references]
    · rw [dif_neg h16] at h2
      cases h2
  | builtin op args =>
    simp only [compileExpr] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [labelRefs, Asm.references]
    · simp only [Option.bind_eq_bind] at h
      obtain ⟨⟨argCode, n1⟩, hargs, h2⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl, rfl⟩
      have ⟨hle, href⟩ := compileArgs_labels args hargs
      refine ⟨hle, ?_⟩
      intro l hl
      rw [labelRefs_append] at hl
      have hop : labelRefs [Asm.op op] = [] := by
        rw [labelRefs_cons_none (by rfl), labelRefs_nil]
      rw [hop, List.append_nil] at hl
      exact href l hl
  | call f args =>
    simp only [compileExpr, Option.bind_eq_bind] at h
    obtain ⟨⟨info, Φv⟩, hlk, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨argCode, n1⟩, hargs, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    rcases h3 with ⟨rfl, rfl⟩
    have ⟨hle, href⟩ := compileArgs_labels args hargs
    refine ⟨Nat.le_trans (Nat.le_succ n) hle, ?_⟩
    intro l hl
    rw [labelRefs_cons_some (by rfl)] at hl
    rcases List.mem_cons.mp hl with hln | hl
    · exact Or.inl (Nat.le_of_eq hln.symm)
    · rw [labelRefs_append, labelRefs_append, labelRefs_push_replicate,
        List.nil_append, labelRefs_jump_label] at hl
      rcases List.mem_append.mp hl with hl | hle
      · rcases href l hl with h | h
        · exact Or.inl (Nat.le_trans (Nat.le_succ n) h)
        · exact Or.inr h
      · rw [List.mem_singleton] at hle
        exact hle ▸ Or.inr (lookupF_entry hlk)
  termination_by structural e

def compileArgs_labels {Φ : FMap} {Γ : List Ident} {off n : Nat}
    (args : List YExpr) {asm : List Asm} {n' : Nat}
    (h : compileArgs Φ Γ off n args = some (asm, n')) :
    n ≤ n' ∧ ∀ l ∈ labelRefs asm, n ≤ l ∨ l ∈ Φentries Φ := by
  cases args with
  | nil =>
    simp only [compileArgs, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [labelRefs]
  | cons e rest =>
    simp only [compileArgs, Option.bind_eq_bind] at h
    obtain ⟨⟨restCode, n1⟩, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨eCode, n2⟩, he, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    rcases h3 with ⟨rfl, rfl⟩
    have ⟨hle1, href1⟩ := compileArgs_labels rest hr
    have ⟨hle2, href2⟩ := compileExpr_labels e he
    refine ⟨le_trans hle1 hle2, ?_⟩
    intro l hl
    rw [labelRefs_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact href1 l hl
    · rcases href2 l hl with h | h
      · exact Or.inl (le_trans hle1 h)
      · exact Or.inr h
  termination_by structural args

end

/-! ### Statement inversions (pinned `compileStmt`) -/

theorem compileAssigns_labelRefs {Γ : List Ident} {xs : List Ident}
    {asm : List Asm} (h : compileAssigns Γ xs = some asm) :
    labelRefs asm = [] := by
  induction xs generalizing asm with
  | nil =>
    simp only [compileAssigns, Option.some.injEq] at h
    subst h
    simp [labelRefs]
  | cons x xs ih =>
    simp only [compileAssigns, Option.bind_eq_bind] at h
    obtain ⟨idx, hidx, h2⟩ := Option.bind_eq_some_iff.mp h
    by_cases h16 : idx + xs.length < 16
    · rw [dif_pos h16] at h2
      obtain ⟨rest, hr, h3⟩ := Option.bind_eq_some_iff.mp h2
      simp only [Option.some.injEq] at h3
      subst h3
      simp [labelRefs_cons, Asm.references, ih hr]
    · rw [dif_neg h16] at h2
      cases h2

theorem labelRefs_retRot (k : Nat) : labelRefs (retRot k) = [] := by
  induction k with
  | zero => simp [retRot, labelRefs]
  | succ k ih => simp [retRot, labelRefs_append, labelRefs_cons, Asm.references, ih]

theorem labelRefs_funDefEmit (n entry nps nrs : Nat) (body : List Asm) :
    labelRefs (Asm.jump (n + 1) :: Asm.label entry :: body ++ [Asm.label n] ++
      List.replicate nps Asm.pop ++ retRot nrs ++
      [Asm.dynJump, Asm.label (n + 1)]) =
      (n + 1) :: labelRefs body := by
  simp [labelRefs_cons, Asm.references, labelRefs_append,
    labelRefs_pop_replicate, labelRefs_retRot]

theorem stmt_exprStmt_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {e : YExpr} {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.exprStmt e) = some (asm, Γ', n')) :
    compileExpr Φ Γ 0 n e = some (asm, n') ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨is, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1 ▸ h2.2.2 ▸ he, h2.2.1.symm⟩

theorem stmt_letNone_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {xs : List Ident} {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.letDecl xs none) = some (asm, Γ', n')) :
    asm = List.replicate xs.length (.push 0) ∧ Γ' = xs ++ Γ ∧ n' = n := by
  simp only [compileStmt, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem stmt_letSome_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {xs : List Ident} {e : YExpr}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.letDecl xs (some e)) = some (asm, Γ', n')) :
    compileExpr Φ Γ 0 n e = some (asm, n') ∧ Γ' = xs ++ Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨is, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1 ▸ h2.2.2 ▸ he, h2.2.1.symm⟩

theorem stmt_assign_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {xs : List Ident} {e : YExpr}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.assign xs e) = some (asm, Γ', n')) :
    ∃ eCode acode,
      compileExpr Φ Γ 0 n e = some (eCode, n') ∧
      compileAssigns Γ xs = some acode ∧
      asm = eCode ++ acode ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨eCode, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨acode, ha, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨eCode, acode, h3.2.2 ▸ he, ha, h3.1.symm, h3.2.1.symm⟩

theorem stmt_block_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {body : YBlock} {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.block body) = some (asm, Γ', n')) :
    YulEvmCompiler.compileBlock Φ Γ F L n body = some (asm, n') ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨is, n1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1 ▸ h2.2.2 ▸ hb, h2.2.1.symm⟩

theorem stmt_cond_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {ce : YExpr} {body : YBlock}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.cond ce body) = some (asm, Γ', n')) :
    ∃ (cCode : List Asm) (n1 : Nat) (bodyCode : List Asm),
      compileExpr Φ Γ 0 (n + 1) ce = some (cCode, n1) ∧
      YulEvmCompiler.compileBlock Φ Γ F L n1 body = some (bodyCode, n') ∧
      asm = cCode ++ [.op .iszero, .jumpi n] ++ bodyCode ++ [.label n] ∧
      Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨cCode, n1⟩, hce, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨bodyCode, n2⟩, hb, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨cCode, n1, bodyCode, hce, h3.2.2 ▸ hb, h3.1.symm, h3.2.1.symm⟩

theorem stmt_break_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {asm : List Asm} {Γ' : List Ident}
    {n' : Nat}
    (h : compileStmt Φ Γ F L n .break = some (asm, Γ', n')) :
    ∃ lc, L = some lc ∧
      asm = List.replicate (Γ.length - lc.depth) .pop ++ [.jump lc.brk] ∧
      Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨lc, hlc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨lc, hlc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

theorem stmt_continue_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {asm : List Asm} {Γ' : List Ident}
    {n' : Nat}
    (h : compileStmt Φ Γ F L n .continue = some (asm, Γ', n')) :
    ∃ lc, L = some lc ∧
      asm = List.replicate (Γ.length - lc.depth) .pop ++ [.jump lc.cont] ∧
      Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨lc, hlc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨lc, hlc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

theorem stmt_leave_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {asm : List Asm} {Γ' : List Ident}
    {n' : Nat}
    (h : compileStmt Φ Γ F L n .leave = some (asm, Γ', n')) :
    ∃ fc, F = some fc ∧
      asm = List.replicate (Γ.length - fc.depth) .pop ++ [.jump fc.exit] ∧
      Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨fc, hfc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨fc, hfc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

theorem stmt_funDef_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {f : Ident} {ps rs : List Ident}
    {body : YBlock} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.funDef f ps rs body) = some (asm, Γ', n')) :
    ∃ (info : FunInfo) (Φv : FMap) (bodyCode : List Asm),
      lookupF Φ f = some (info, Φv) ∧
      rs.length ≤ 16 ∧ (ps ++ rs).Nodup ∧
      YulEvmCompiler.compileBlock Φ (ps ++ rs)
          (some ⟨n, (ps ++ rs).length⟩) none (n + 2) body =
        some (bodyCode, n') ∧
      asm = .jump (n + 1) :: .label info.entry :: bodyCode
        ++ [.label n]
        ++ List.replicate ps.length .pop
        ++ retRot rs.length
        ++ [.dynJump, .label (n + 1)] ∧
      Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨info, Φv⟩, hlk, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases hg : rs.length ≤ 16 ∧ (ps ++ rs).Nodup
  · rw [if_pos hg] at h2
    obtain ⟨⟨bodyCode, n1⟩, hb, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    refine ⟨info, Φv, bodyCode, hlk, hg.1, hg.2, h3.2.2 ▸ hb,
      by rw [← h3.1], h3.2.1.symm⟩
  · rw [if_neg hg] at h2
    exact absurd h2 (by simp)

theorem stmt_switch_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {c : YExpr}
    {cases : List (Literal × YBlock)} {dflt : Option YBlock}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.switch c cases dflt) = some (asm, Γ', n')) :
    ∃ (cCode : List Asm) (n1 : Nat) (cmpAsm bodyAsm : List Asm) (n2 : Nat)
      (defAsm : List Asm),
      compileExpr Φ Γ 0 (n + 1) c = some (cCode, n1) ∧
      compileSwitchCases Φ Γ F L n n1 cases = some (cmpAsm, bodyAsm, n2) ∧
      YulEvmCompiler.compileBlock Φ Γ F L n2 (dflt.getD []) =
        some (defAsm, n') ∧
      asm = cCode ++ cmpAsm ++ .pop :: defAsm ++ [.jump n] ++ bodyAsm
        ++ [.label n] ∧
      Γ' = Γ := by
  rw [compileStmt.eq_def] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨cCode, n1⟩, hce, h2⟩ := h
  obtain ⟨⟨cmpAsm, bodyAsm, n2⟩, hcs, h3⟩ := h2
  obtain ⟨⟨defAsm, n3⟩, hdef, h4⟩ := h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  refine ⟨cCode, n1, cmpAsm, bodyAsm, n2, defAsm, hce, hcs, ?_, h4.1.symm,
    h4.2.1.symm⟩
  rw [← h4.2.2]
  cases dflt <;> exact hdef

theorem stmt_forLoop_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {init : YBlock} {ce : YExpr}
    {post body : YBlock} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.forLoop init ce post body)
      = some (asm, Γ', n')) :
    ∃ (scope : FScopeInfo) (n0 : Nat) (initCode : List Asm) (Γi : List Ident)
      (n1 : Nat) (cCode : List Asm) (n2 : Nat) (bodyCode : List Asm)
      (n3 : Nat) (postCode : List Asm),
      hoistInfos n init = (scope, n0) ∧
      (scope.map Prod.fst).Nodup ∧
      compileStmts (scope :: Φ) Γ F L (n0 + 3) init =
        some (initCode, Γi, n1) ∧
      compileExpr (scope :: Φ) Γi 0 n1 ce = some (cCode, n2) ∧
      YulEvmCompiler.compileBlock (scope :: Φ) Γi F
          (some ⟨n0 + 2, n0 + 1, Γi.length⟩) n2 body = some (bodyCode, n3) ∧
      YulEvmCompiler.compileBlock (scope :: Φ) Γi F none n3 post =
        some (postCode, n') ∧
      asm = initCode
        ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
        ++ bodyCode ++ .label (n0 + 1) :: postCode ++ [.jump n0]
        ++ [.label (n0 + 2)]
        ++ List.replicate (Γi.length - Γ.length) .pop ∧
      Γ' = Γ := by
  simp only [compileStmt] at h
  rcases hh : hoistInfos n init with ⟨scope, n0⟩
  rw [hh] at h
  dsimp only at h
  by_cases hnd : (scope.map Prod.fst).Nodup
  · rw [if_neg (by simp [hnd]), Option.bind_eq_bind] at h
    obtain ⟨⟨initCode, Γi, n1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨cCode, n2⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨⟨bodyCode, n3⟩, h5, h6⟩ := Option.bind_eq_some_iff.mp h4
    obtain ⟨⟨postCode, n4⟩, h7, h8⟩ := Option.bind_eq_some_iff.mp h6
    simp only [Option.some.injEq, Prod.mk.injEq] at h8
    refine ⟨scope, n0, initCode, Γi, n1, cCode, n2, bodyCode, n3, postCode,
      rfl, hnd, h1, h3, h5, h8.2.2 ▸ h7, ?_, h8.2.1.symm⟩
    rw [← h8.1]
    simp
  · rw [if_pos (by simp [hnd])] at h
    exact absurd h (by simp)

theorem allowedLabel_le {n Φ F L l} (h : n ≤ l) :
    allowedLabel n Φ F L l := Or.inl h

theorem allowedLabel_of_block {n n1 Φ scope F L l}
    (hle : n ≤ n1)
    (hent : ∀ q ∈ scope, n ≤ q.2.entry)
    (h : allowedLabel n1 (scope :: Φ) F L l) :
    allowedLabel n Φ F L l :=
  allowedLabel_cons_scope (allowedLabel_mono hle h) hent

mutual
def stmtRank : YStmt → Nat
  | .block body => stmtsRank body + 1
  | .funDef _ _ _ body => stmtsRank body + 1
  | .letDecl _ _ => 0
  | .assign _ _ => 0
  | .cond _ body => stmtsRank body + 1
  | .switch _ cases dflt =>
    casesRank cases + (match dflt with | none => 0 | some b => stmtsRank b) + 1
  | .forLoop init _ post body =>
    stmtsRank init + stmtsRank post + stmtsRank body + 1
  | .exprStmt _ => 0
  | .«break» => 0
  | .«continue» => 0
  | .leave => 0

def stmtsRank : YBlock → Nat
  | [] => 0
  | s :: rest => stmtRank s + stmtsRank rest + 1

def casesRank : List (Literal × YBlock) → Nat
  | [] => 0
  | (_, b) :: rest => stmtsRank b + casesRank rest + 1
end

@[simp] theorem stmtsRank_nil : stmtsRank ([] : YBlock) = 0 := rfl
@[simp] theorem stmtsRank_cons (s : YStmt) (rest : YBlock) :
    stmtsRank (s :: rest) = stmtRank s + stmtsRank rest + 1 := rfl
@[simp] theorem stmtRank_block (body : YBlock) :
    stmtRank (.block body) = stmtsRank body + 1 := rfl
@[simp] theorem stmtRank_funDef (f : Ident) (ps rs : List Ident) (body : YBlock) :
    stmtRank (.funDef f ps rs body) = stmtsRank body + 1 := rfl
@[simp] theorem stmtRank_cond (c : YExpr) (body : YBlock) :
    stmtRank (.cond c body) = stmtsRank body + 1 := rfl
@[simp] theorem stmtRank_forLoop (init : YBlock) (c : YExpr) (post body : YBlock) :
    stmtRank (.forLoop init c post body) =
      stmtsRank init + stmtsRank post + stmtsRank body + 1 := rfl
@[simp] theorem casesRank_nil : casesRank ([] : List (Literal × YBlock)) = 0 := rfl
@[simp] theorem casesRank_cons (v : Literal) (b : YBlock)
    (rest : List (Literal × YBlock)) :
    casesRank ((v, b) :: rest) = stmtsRank b + casesRank rest + 1 := rfl
@[simp] theorem stmtRank_switch (c : YExpr) (cases : List (Literal × YBlock))
    (dflt : Option YBlock) :
    stmtRank (.switch c cases dflt) =
      casesRank cases + stmtsRank (dflt.getD []) + 1 := by
  cases dflt <;> simp [stmtRank, Option.getD]

theorem stmtsRank_getD (dflt : Option YBlock) :
    stmtsRank (dflt.getD []) =
      match dflt with | none => 0 | some b => stmtsRank b := by
  cases dflt with
  | none => simp [Option.getD]
  | some _ => rfl

/-! ### Label lower bounds for statements -/

mutual

def compileStmt_labels {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} (s : YStmt) {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n s = some (asm, Γ', n')) :
    n ≤ n' ∧ ∀ l ∈ labelRefs asm, allowedLabel n Φ F L l := by
  cases s with
  | exprStmt e =>
    obtain ⟨he, rfl⟩ := stmt_exprStmt_inv h
    have ⟨hle, href⟩ := compileExpr_labels e he
    exact ⟨hle, fun l hl => (href l hl).elim allowedLabel_le
      (fun hΦ => Or.inr (Or.inl hΦ))⟩
  | letDecl xs v =>
    cases v with
    | none =>
      obtain ⟨hasm, rfl, hn⟩ := stmt_letNone_inv h
      subst hasm
      refine ⟨Nat.le_of_eq hn.symm, ?_⟩
      intro l hl
      rw [labelRefs_push_replicate] at hl
      cases hl
    | some e =>
      obtain ⟨he, rfl⟩ := stmt_letSome_inv h
      have ⟨hle, href⟩ := compileExpr_labels e he
      exact ⟨hle, fun l hl => (href l hl).elim allowedLabel_le
        (fun hΦ => Or.inr (Or.inl hΦ))⟩
  | assign xs e =>
    obtain ⟨eCode, acode, he, ha, rfl, rfl⟩ := stmt_assign_inv h
    have ⟨hle, href⟩ := compileExpr_labels e he
    refine ⟨hle, ?_⟩
    intro l hl
    rw [labelRefs_append, compileAssigns_labelRefs ha, List.append_nil] at hl
    exact (href l hl).elim allowedLabel_le (fun hΦ => Or.inr (Or.inl hΦ))
  | block body =>
    obtain ⟨hb, rfl⟩ := stmt_block_inv h
    exact compileBlock_labels body hb
  | cond c body =>
    obtain ⟨cCode, n1, bodyCode, hce, hb, rfl, rfl⟩ := stmt_cond_inv h
    have ⟨hle1, href⟩ := compileExpr_labels c hce
    have ⟨hle2, hbody⟩ := compileBlock_labels body hb
    refine ⟨le_trans (Nat.le_succ n) (le_trans hle1 hle2), ?_⟩
    intro l hl
    have hrefs :
        labelRefs (cCode ++ [.op .iszero, .jumpi n] ++ bodyCode ++ [.label n]) =
          labelRefs cCode ++ [n] ++ labelRefs bodyCode := by
      rw [labelRefs_append, labelRefs_append, labelRefs_append,
        labelRefs_iszero_jumpi, labelRefs_label_one, List.append_nil]
    rw [hrefs] at hl
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with (hl | hn) | hl
    · exact (href l hl).elim
        (fun h => allowedLabel_le (le_trans (Nat.le_succ n) h))
        (fun hΦ => Or.inr (Or.inl hΦ))
    · exact allowedLabel_le (Nat.le_of_eq hn.symm)
    · exact allowedLabel_mono (le_trans (Nat.le_succ n) hle1) (hbody l hl)
  | forLoop init c post body =>
    obtain ⟨scope, n0, initCode, Γi, n1, cCode, n2, bodyCode, n3, postCode,
      hh, hnd, hinit, hce, hb, hp, rfl, rfl⟩ := stmt_forLoop_inv h
    have ⟨hle0, hent0⟩ := hoistInfos_entries n init
    rw [hh] at hle0 hent0
    have ⟨hli, hrefi⟩ := compileStmts_labels init hinit
    have ⟨hlec, hrefc⟩ := compileExpr_labels c hce
    have ⟨hleb, hrefb⟩ := compileBlock_labels body hb
    have ⟨hlep, hrefp⟩ := compileBlock_labels post hp
    have hn1 : n0 + 3 ≤ n1 := hli
    have hn2 : n1 ≤ n2 := hlec
    have hn3 : n2 ≤ n3 := hleb
    have hn4 : n3 ≤ n' := hlep
    refine ⟨by omega, ?_⟩
    intro l hl
    have hge : n ≤ n0 := hle0
    have hscope : ∀ q ∈ scope, n ≤ q.2.entry := fun q hq => (hent0 q hq).1
    have hrefs :
        labelRefs (initCode ++ .label n0 :: cCode ++
          [.op .iszero, .jumpi (n0 + 2)] ++ bodyCode ++
          .label (n0 + 1) :: postCode ++ [.jump n0] ++
          [.label (n0 + 2)] ++
          List.replicate (Γi.length - Γ'.length) .pop) =
          labelRefs initCode ++ labelRefs cCode ++ [n0 + 2] ++
            labelRefs bodyCode ++ labelRefs postCode ++ [n0] := by
      simp [labelRefs_append, labelRefs_cons, Asm.references,
        labelRefs_pop_replicate]
    rw [hrefs] at hl
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with ((((hl | hl) | hn2) | hl) | hl) | hn0
    · exact allowedLabel_of_block (by omega) hscope (hrefi l hl)
    · exact (hrefc l hl).elim
        (fun h => allowedLabel_le (by omega))
        (fun hΦ => allowedLabel_cons_scope (Or.inr (Or.inl hΦ)) hscope)
    · exact allowedLabel_le (Nat.le_trans hge
        (Nat.le_trans (Nat.le_add_right n0 2) (Nat.le_of_eq hn2.symm)))
    · rcases hrefb l hl with h | h | h | h
      · exact allowedLabel_le (by omega)
      · exact allowedLabel_cons_scope (Or.inr (Or.inl h)) hscope
      · obtain ⟨fc, hF, rfl⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨fc, hF, rfl⟩))
      · obtain ⟨lc, hL, hlc⟩ := h
        simp only [Option.some.injEq] at hL
        subst lc
        rcases hlc with hbrk | hcont
        · exact allowedLabel_le (Nat.le_trans hge
            (Nat.le_trans (Nat.le_add_right n0 2) (Nat.le_of_eq hbrk.symm)))
        · exact allowedLabel_le (Nat.le_trans hge
            (Nat.le_trans (Nat.le_add_right n0 1) (Nat.le_of_eq hcont.symm)))
    · rcases hrefp l hl with h | h | h | h
      · exact allowedLabel_le (by omega)
      · exact allowedLabel_cons_scope (Or.inr (Or.inl h)) hscope
      · obtain ⟨fc, hF, rfl⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨fc, hF, rfl⟩))
      · obtain ⟨lc, hnone, _⟩ := h; cases hnone
    · exact allowedLabel_le (Nat.le_trans hge (Nat.le_of_eq hn0.symm))
  | funDef f ps rs body =>
    obtain ⟨info, Φv, bodyCode, hlk, _, _, hb, rfl, rfl⟩ := stmt_funDef_inv h
    have ⟨hleb, hrefb⟩ := compileBlock_labels body hb
    refine ⟨Nat.le_trans (Nat.le_add_right n 2) hleb, ?_⟩
    intro l hl
    rw [labelRefs_funDefEmit] at hl
    rcases List.mem_cons.mp hl with hln | hl
    · exact allowedLabel_le (Nat.le_trans (Nat.le_succ n) (Nat.le_of_eq hln.symm))
    · rcases hrefb l hl with h | h | h | h
      · exact allowedLabel_le (le_trans (Nat.le_add_right n 2) h)
      · exact Or.inr (Or.inl h)
      · obtain ⟨fc, hF, heq⟩ := h
        simp only [Option.some.injEq] at hF
        subst fc
        exact allowedLabel_le (Nat.le_of_eq heq.symm)
      · obtain ⟨lc, hnone, _⟩ := h; cases hnone
  | «break» =>
    obtain ⟨lc, hL, hasm, rfl, hn⟩ := stmt_break_inv h
    subst hL; subst hasm
    refine ⟨Nat.le_of_eq hn.symm, ?_⟩
    intro l hl
    rw [labelRefs_append, labelRefs_pop_replicate, List.nil_append] at hl
    simp [labelRefs, Asm.references] at hl
    exact Or.inr (Or.inr (Or.inr ⟨lc, rfl, Or.inl hl⟩))
  | «continue» =>
    obtain ⟨lc, hL, hasm, rfl, hn⟩ := stmt_continue_inv h
    subst hL; subst hasm
    refine ⟨Nat.le_of_eq hn.symm, ?_⟩
    intro l hl
    rw [labelRefs_append, labelRefs_pop_replicate, List.nil_append] at hl
    simp [labelRefs, Asm.references] at hl
    exact Or.inr (Or.inr (Or.inr ⟨lc, rfl, Or.inr hl⟩))
  | «leave» =>
    obtain ⟨fc, hF, hasm, rfl, hn⟩ := stmt_leave_inv h
    subst hF; subst hasm
    refine ⟨Nat.le_of_eq hn.symm, ?_⟩
    intro l hl
    rw [labelRefs_append, labelRefs_pop_replicate, List.nil_append] at hl
    simp [labelRefs, Asm.references] at hl
    exact Or.inr (Or.inr (Or.inl ⟨fc, rfl, hl⟩))
  | «switch» c cases dflt =>
    obtain ⟨cCode, n1, cmpAsm, bodyAsm, n2, defAsm, hce, hcs, hdef, rfl, rfl⟩ :=
      stmt_switch_inv h
    have ⟨hle1, href⟩ := compileExpr_labels c hce
    have ⟨hle2, hcmp⟩ := compileSwitchCases_labels cases hcs
    have ⟨hle3, hdef'⟩ := compileBlock_labels (dflt.getD []) hdef
    refine ⟨le_trans (Nat.le_succ n) (le_trans hle1 (le_trans hle2 hle3)), ?_⟩
    intro l hl
    have hrefs :
        labelRefs (cCode ++ cmpAsm ++ .pop :: defAsm ++ [.jump n] ++ bodyAsm
          ++ [.label n]) =
          labelRefs cCode ++ labelRefs cmpAsm ++ labelRefs defAsm ++
            n :: labelRefs bodyAsm := by
      simp [labelRefs_append, labelRefs_cons, Asm.references,
        labelRefs_jump_one, labelRefs_label_one]
    rw [hrefs] at hl
    simp only [List.mem_append, List.mem_cons] at hl
    rcases hl with ((hl | hl) | hl) | (hn | hl)
    · exact (href l hl).elim
        (fun h => allowedLabel_le (le_trans (Nat.le_succ n) h))
        (fun hΦ => Or.inr (Or.inl hΦ))
    · rcases hcmp l (List.mem_append.mpr (Or.inl hl)) with h | h
      · exact allowedLabel_mono (le_trans (Nat.le_succ n) hle1) h
      · exact allowedLabel_le (Nat.le_of_eq h.symm)
    · exact allowedLabel_mono (le_trans (Nat.le_succ n) (le_trans hle1 hle2))
        (hdef' l hl)
    · exact allowedLabel_le (Nat.le_of_eq hn.symm)
    · rcases hcmp l (List.mem_append.mpr (Or.inr hl)) with h | h
      · exact allowedLabel_mono (le_trans (Nat.le_succ n) hle1) h
      · exact allowedLabel_le (Nat.le_of_eq h.symm)
  termination_by (stmtRank s, (1 : Nat))

def compileStmts_labels {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} (ss : YBlock) {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmts Φ Γ F L n ss = some (asm, Γ', n')) :
    n ≤ n' ∧ ∀ l ∈ labelRefs asm, allowedLabel n Φ F L l := by
  cases ss with
  | nil =>
    simp only [compileStmts, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [labelRefs]
  | cons s rest =>
    obtain ⟨is1, Γ1, n1, is2, h1, h2, rfl⟩ := compileStmts_cons_inv h
    have ⟨hle1, href1⟩ := compileStmt_labels s h1
    have ⟨hle2, href2⟩ := compileStmts_labels rest h2
    refine ⟨le_trans hle1 hle2, ?_⟩
    intro l hl
    rw [labelRefs_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact href1 l hl
    · exact allowedLabel_mono hle1 (href2 l hl)
  termination_by (stmtsRank ss, (0 : Nat))

def compileBlock_labels {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} (body : YBlock) {asm : List Asm}
    {n' : Nat}
    (h : YulEvmCompiler.compileBlock Φ Γ F L n body = some (asm, n')) :
    n ≤ n' ∧ ∀ l ∈ labelRefs asm, allowedLabel n Φ F L l := by
  obtain ⟨scope, n1, stmtsAsm, Γb, n2, hh, _, hs, rfl, rfl⟩ :=
    yulCompileBlock_inv h
  have ⟨hle0, hent⟩ := hoistInfos_entries n body
  rw [hh] at hle0 hent
  have ⟨hle1, href⟩ := compileStmts_labels body hs
  refine ⟨le_trans hle0 hle1, ?_⟩
  intro l hl
  rw [labelRefs_append, labelRefs_pop_replicate, List.append_nil] at hl
  exact allowedLabel_of_block hle0 (fun q hq => (hent q hq).1) (href l hl)
  termination_by (stmtsRank body, (1 : Nat))

def compileSwitchCases_labels {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {lend n : Nat}
    (cases : List (Literal × YBlock)) {cmpAsm bodyAsm : List Asm}
    {n' : Nat}
    (h : compileSwitchCases Φ Γ F L lend n cases =
      some (cmpAsm, bodyAsm, n')) :
    n ≤ n' ∧
      ∀ l ∈ labelRefs cmpAsm ++ labelRefs bodyAsm,
        allowedLabel n Φ F L l ∨ l = lend := by
  match cases with
  | [] =>
    simp only [compileSwitchCases, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [labelRefs]
  | (v, b) :: rest =>
    simp only [compileSwitchCases, Option.bind_eq_bind] at h
    obtain ⟨⟨bAsm, n1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨cmpRest, bodyRest, n2⟩, hr, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    rcases h3 with ⟨rfl, rfl, rfl⟩
    have ⟨hleb, hrefb⟩ := compileBlock_labels b hb
    have ⟨hler, hrefr⟩ := compileSwitchCases_labels rest hr
    refine ⟨le_trans (Nat.le_succ n) (le_trans hleb hler), ?_⟩
    intro l hl
    have hcmp :
        labelRefs ([.dup 0, .push (litValue v), .op .eq, .jumpi n] ++ cmpRest) =
          n :: labelRefs cmpRest := by
      rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append]
      rw [labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
        labelRefs_cons_none (by rfl), labelRefs_cons_some (by rfl)]
    have hbody :
        labelRefs ([.label n, .pop] ++ bAsm ++ [.jump lend] ++ bodyRest) =
          labelRefs bAsm ++ [lend] ++ labelRefs bodyRest := by
      rw [labelRefs_append, labelRefs_append, labelRefs_append,
        labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
        labelRefs_jump_one, labelRefs_nil, List.nil_append]
    rw [hcmp, hbody] at hl
    simp only [List.mem_append, List.mem_cons, List.mem_singleton,
      List.mem_nil_iff, or_false] at hl
    rcases hl with (hln | hl) | ((hl | hlend) | hl)
    · exact Or.inl (allowedLabel_le (Nat.le_of_eq hln.symm))
    · rcases hrefr l (List.mem_append.mpr (Or.inl hl)) with h | h
      · exact Or.inl (allowedLabel_mono (le_trans (Nat.le_succ n) hleb) h)
      · exact Or.inr h
    · exact Or.inl (allowedLabel_mono (Nat.le_succ n) (hrefb l hl))
    · exact Or.inr hlend
    · rcases hrefr l (List.mem_append.mpr (Or.inr hl)) with h | h
      · exact Or.inl (allowedLabel_mono (le_trans (Nat.le_succ n) hleb) h)
      · exact Or.inr h
  termination_by (casesRank cases, (0 : Nat))
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [stmtRank_block, stmtRank_cond, stmtRank_funDef, stmtRank_forLoop,
        stmtRank_switch, stmtsRank_cons, stmtsRank_nil, casesRank_cons,
        casesRank_nil, Option.getD, stmtsRank_getD]
      omega

end

theorem compileStmts_rest_ge {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {rest : YBlock} {asm : List Asm} {Γ' : List Ident}
    {n' : Nat}
    (hΦ : Φentries Φ = []) (hF : F = none) (hL : L = none)
    (h : compileStmts Φ Γ F L 2 rest = some (asm, Γ', n')) :
    ∀ l ∈ labelRefs asm, 2 ≤ l := by
  have ⟨_, href⟩ := compileStmts_labels rest h
  intro l hl
  exact allowedLabel_ge (href l hl) hΦ hF hL

theorem labelRefs_lockPrefixAsmRaw (k : Nat) :
    labelRefs (lockPrefixAsmRaw k) = [0, 1] := by
  unfold lockPrefixAsmRaw
  rw [labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_some (l := 0) (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_some (l := 1) (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl)]
  rw [labelRefs_nil]

theorem labelRefs_lockPrefixAsmOpt (k : Nat) :
    labelRefs (lockPrefixAsmOpt k) = [1] := by
  unfold lockPrefixAsmOpt
  rw [labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_some (l := 1) (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl)]
  rw [labelRefs_nil]

theorem labelRefs_lockPrefixAsmRaw_append (k : Nat) (rest : List Asm) :
    labelRefs (lockPrefixAsmRaw k ++ rest) = [0, 1] ++ labelRefs rest := by
  rw [labelRefs_append, labelRefs_lockPrefixAsmRaw]

theorem two_le_not_zero {l : Nat} (h : 2 ≤ l) : l ≠ 0 :=
  Nat.ne_of_gt (Nat.lt_of_succ_le (Nat.le_trans (by decide : 1 ≤ 2) h))
theorem two_le_not_one {l : Nat} (h : 2 ≤ l) : l ≠ 1 :=
  Nat.ne_of_gt (Nat.lt_of_succ_le h)

theorem rest_refs_ge_not_mem_zero {rest : List Asm}
    (h : ∀ l ∈ labelRefs rest, 2 ≤ l) : 0 ∉ labelRefs rest :=
  fun hl => (two_le_not_zero (h 0 hl)).elim rfl

theorem rest_refs_ge_not_mem_one {rest : List Asm}
    (h : ∀ l ∈ labelRefs rest, 2 ≤ l) : 1 ∉ labelRefs rest :=
  fun hl => (two_le_not_one (h 1 hl)).elim rfl

theorem peepRun_labelRefs_subset (R : List Label) (p : List Asm) :
    ∀ l ∈ labelRefs (peepRun R p), l ∈ labelRefs p :=
  Peephole.codeRel_labelRefs_subset (Peephole.codeRel_peepRun R p)

/-! ### Peephole of the lock prefix -/

theorem peepRun_push_iszero (R : List Label) (v : BitVec 256) (rest : List Asm) :
    peepRun R (.push v :: .op .iszero :: rest) =
      .push v :: peepRun R (.op .iszero :: rest) := by
  simp [peepRun]

theorem peepRun_iszero_pop (R : List Label) (rest : List Asm) :
    peepRun R (.op .iszero :: .pop :: rest) =
      .op .iszero :: peepRun R (.pop :: rest) := by
  simp [peepRun]

theorem peepRun_pop_push (R : List Label) (v : BitVec 256) (rest : List Asm) :
    peepRun R (.pop :: .push v :: rest) =
      .pop :: peepRun R (.push v :: rest) := by
  simp [peepRun]

theorem peepRun_pop_label (R : List Label) (l : Label) (rest : List Asm) :
    peepRun R (.pop :: .label l :: rest) =
      .pop :: peepRun R (.label l :: rest) := by
  simp [peepRun]

theorem peepRun_push_tload (R : List Label) (v : BitVec 256) (rest : List Asm) :
    peepRun R (.push v :: .op .tload :: rest) =
      .push v :: peepRun R (.op .tload :: rest) := by
  simp [peepRun]

theorem peepRun_tload_iszero (R : List Label) (rest : List Asm) :
    peepRun R (.op .tload :: .op .iszero :: rest) =
      .op .tload :: peepRun R (.op .iszero :: rest) := by
  simp [peepRun]

theorem peepRun_iszero_jumpi (R : List Label) (l : Label) (rest : List Asm) :
    peepRun R (.op .iszero :: .jumpi l :: rest) =
      .op .iszero :: peepRun R (.jumpi l :: rest) := by
  simp [peepRun]

theorem peepRun_jumpi_label_eq (R : List Label) (l : Label) (rest : List Asm) :
    peepRun R (.jumpi l :: .label l :: rest) =
      .pop :: .label l :: peepRun R rest := by
  simp [peepRun]

theorem peepRun_jumpi_push (R : List Label) (l : Label) (v : BitVec 256)
    (rest : List Asm) :
    peepRun R (.jumpi l :: .push v :: rest) =
      .jumpi l :: peepRun R (.push v :: rest) := by
  simp [peepRun]

theorem peepRun_push_push (R : List Label) (v w : BitVec 256) (rest : List Asm) :
    peepRun R (.push v :: .push w :: rest) =
      .push v :: peepRun R (.push w :: rest) := by
  simp [peepRun]

theorem peepRun_push_revert (R : List Label) (v : BitVec 256) (rest : List Asm) :
    peepRun R (.push v :: .op .revert :: rest) =
      .push v :: peepRun R (.op .revert :: rest) := by
  simp [peepRun]

theorem peepRun_revert_label (R : List Label) (l : Label) (rest : List Asm) :
    peepRun R (.op .revert :: .label l :: rest) =
      .op .revert :: peepRun R (.label l :: rest) := by
  simp [peepRun]

theorem peepRun_label_mem (R : List Label) (l : Label) (rest : List Asm)
    (h : l ∈ R) :
    peepRun R (.label l :: rest) = .label l :: peepRun R rest := by
  simp [peepRun, h]

theorem peepRun_label_not_mem (R : List Label) (l : Label) (rest : List Asm)
    (h : l ∉ R) :
    peepRun R (.label l :: rest) = peepRun R rest := by
  simp [peepRun, h]

theorem mem_zero_lockPrefixRaw (k : Nat) (rest : List Asm) :
    0 ∈ labelRefs (lockPrefixAsmRaw k ++ rest) := by
  simp [labelRefs_lockPrefixAsmRaw_append]

theorem mem_one_lockPrefixRaw (k : Nat) (rest : List Asm) :
    1 ∈ labelRefs (lockPrefixAsmRaw k ++ rest) := by
  simp [labelRefs_lockPrefixAsmRaw_append]

theorem peepRun_lockPrefixRaw (R : List Label) (k : Nat) (rest : List Asm)
    (h0 : 0 ∈ R) (h1 : 1 ∈ R) :
    peepRun R (lockPrefixAsmRaw k ++ rest) =
      lockPrefixAsmMid k ++ peepRun R rest := by
  unfold lockPrefixAsmRaw lockPrefixAsmMid
  simp only [List.cons_append, List.nil_append]
  rw [peepRun_push_iszero, peepRun_iszero_jumpi, peepRun_jumpi_label_eq]
  rw [peepRun_push_tload, peepRun_tload_iszero, peepRun_iszero_jumpi]
  rw [peepRun_jumpi_push, peepRun_push_push, peepRun_push_revert,
    peepRun_revert_label]
  rw [peepRun_label_mem R 1 _ h1]

theorem labelRefs_lockPrefixAsmMid (k : Nat) :
    labelRefs (lockPrefixAsmMid k) = [1] := by
  unfold lockPrefixAsmMid
  rw [labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_some (l := 1) (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl),
    labelRefs_cons_none (by rfl), labelRefs_cons_none (by rfl)]
  rw [labelRefs_nil]

theorem peepRun_lockPrefixMid (R : List Label) (k : Nat) (rest : List Asm)
    (h0 : 0 ∉ R) (h1 : 1 ∈ R) :
    peepRun R (lockPrefixAsmMid k ++ rest) =
      lockPrefixAsmOpt k ++ peepRun R rest := by
  unfold lockPrefixAsmMid lockPrefixAsmOpt
  simp only [List.cons_append, List.nil_append]
  rw [peepRun_push_iszero, peepRun_iszero_pop, peepRun_pop_label]
  rw [peepRun_label_not_mem R 0 _ h0]
  rw [peepRun_push_tload, peepRun_tload_iszero, peepRun_iszero_jumpi]
  rw [peepRun_jumpi_push, peepRun_push_push, peepRun_push_revert,
    peepRun_revert_label]
  rw [peepRun_label_mem R 1 _ h1]

theorem peepRun_lockPrefixOpt (R : List Label) (k : Nat) (rest : List Asm)
    (h1 : 1 ∈ R) :
    peepRun R (lockPrefixAsmOpt k ++ rest) =
      lockPrefixAsmOpt k ++ peepRun R rest := by
  unfold lockPrefixAsmOpt
  simp only [List.cons_append, List.nil_append]
  rw [peepRun_push_iszero, peepRun_iszero_pop, peepRun_pop_push]
  rw [peepRun_push_tload, peepRun_tload_iszero, peepRun_iszero_jumpi]
  rw [peepRun_jumpi_push, peepRun_push_push, peepRun_push_revert,
    peepRun_revert_label]
  rw [peepRun_label_mem R 1 _ h1]

theorem optimizeAsmRound_lockPrefixRaw (k : Nat) (rest : List Asm) :
    optimizeAsmRound (lockPrefixAsmRaw k ++ rest) =
      lockPrefixAsmMid k ++
        peepRun (labelRefs (lockPrefixAsmRaw k ++ rest)) rest := by
  unfold optimizeAsmRound
  exact peepRun_lockPrefixRaw _ k rest
    (mem_zero_lockPrefixRaw k rest) (mem_one_lockPrefixRaw k rest)

theorem not_mem_zero_of_peep (R : List Label) {rest : List Asm}
    (h : 0 ∉ labelRefs rest) : 0 ∉ labelRefs (peepRun R rest) :=
  fun hl => h (peepRun_labelRefs_subset R rest 0 hl)

theorem optimizeAsmRound_lockPrefixMid (k : Nat) (rest : List Asm)
    (h0 : 0 ∉ labelRefs rest) :
    optimizeAsmRound (lockPrefixAsmMid k ++ rest) =
      lockPrefixAsmOpt k ++
        peepRun (labelRefs (lockPrefixAsmMid k ++ rest)) rest := by
  unfold optimizeAsmRound
  have hR0 : 0 ∉ labelRefs (lockPrefixAsmMid k ++ rest) := by
    simp [labelRefs_append, labelRefs_lockPrefixAsmMid, h0]
  have hR1 : 1 ∈ labelRefs (lockPrefixAsmMid k ++ rest) := by
    simp [labelRefs_append, labelRefs_lockPrefixAsmMid]
  exact peepRun_lockPrefixMid _ k rest hR0 hR1

theorem raw_ne_mid (k : Nat) (rest r1 : List Asm) :
    lockPrefixAsmRaw k ++ rest ≠ lockPrefixAsmMid k ++ r1 := by
  intro h
  have hraw : (lockPrefixAsmRaw k ++ rest)[2]? = some (.jumpi 0) := by
    simp [lockPrefixAsmRaw]
  have hmid : (lockPrefixAsmMid k ++ r1)[2]? = some .pop := by
    simp [lockPrefixAsmMid]
  rw [h] at hraw
  cases hraw.symm.trans hmid

theorem mid_ne_opt (k : Nat) (r1 r2 : List Asm) :
    lockPrefixAsmMid k ++ r1 ≠ lockPrefixAsmOpt k ++ r2 := by
  intro h
  have hmid : (lockPrefixAsmMid k ++ r1)[3]? = some (.label 0) := by
    simp [lockPrefixAsmMid]
  have hopt : (lockPrefixAsmOpt k ++ r2)[3]? = some (.push 0) := by
    simp [lockPrefixAsmOpt]
  rw [h] at hmid
  cases hmid.symm.trans hopt

theorem optimizeAsmN_opt_prefix (n k : Nat) (rest : List Asm) :
    ∃ rest', optimizeAsmN n (lockPrefixAsmOpt k ++ rest) =
      lockPrefixAsmOpt k ++ rest' := by
  induction n generalizing rest with
  | zero => exact ⟨rest, rfl⟩
  | succ n ih =>
    have h1 : 1 ∈ labelRefs (lockPrefixAsmOpt k ++ rest) := by
      simp [labelRefs_append, labelRefs_lockPrefixAsmOpt]
    have hq : optimizeAsmRound (lockPrefixAsmOpt k ++ rest) =
        lockPrefixAsmOpt k ++
          peepRun (labelRefs (lockPrefixAsmOpt k ++ rest)) rest := by
      unfold optimizeAsmRound
      exact peepRun_lockPrefixOpt _ k rest h1
    rw [optimizeAsmN]
    split
    · exact ⟨rest, rfl⟩
    · rw [hq]
      exact ih _

theorem optimizeAsm_lockPrefix (k : Nat) (rest : List Asm)
    (hrest : ∀ l ∈ labelRefs rest, 2 ≤ l) :
    ∃ rest', optimizeAsm (lockPrefixAsmRaw k ++ rest) =
      lockPrefixAsmOpt k ++ rest' := by
  unfold optimizeAsm
  have h0rest : 0 ∉ labelRefs rest := rest_refs_ge_not_mem_zero hrest
  have hr0 := optimizeAsmRound_lockPrefixRaw k rest
  set r1 := peepRun (labelRefs (lockPrefixAsmRaw k ++ rest)) rest
  have h0r1 : 0 ∉ labelRefs r1 := not_mem_zero_of_peep _ h0rest
  have hr1 := optimizeAsmRound_lockPrefixMid k r1 h0r1
  set r2 := peepRun (labelRefs (lockPrefixAsmMid k ++ r1)) r1
  have hne01 : optimizeAsmRound (lockPrefixAsmRaw k ++ rest) ≠
      lockPrefixAsmRaw k ++ rest := by
    rw [hr0]
    exact (raw_ne_mid k rest r1).symm
  have hne12 : optimizeAsmRound (lockPrefixAsmMid k ++ r1) ≠
      lockPrefixAsmMid k ++ r1 := by
    rw [hr1]
    exact (mid_ne_opt k r1 r2).symm
  rw [optimizeAsmN, if_neg hne01, hr0]
  rw [optimizeAsmN, if_neg hne12, hr1]
  exact optimizeAsmN_opt_prefix 2 k r2

/-! ### `compileProgram` of a runtime with the two-statement prologue -/

theorem hoistInfos_spilled_runtime {c : ContractDef} {rt : YBlock}
    {r : Result} (hrt : runtimeBlock c = some rt)
    (hsp : spillRuntime? rt = some r) :
    hoistInfos 0 r.block = ([], 0) := by
  have hbase : r.base = memoryGuardK := spillRuntime_base hrt hsp
  obtain ⟨_, hf⟩ := spillBlock_facts (by simpa [spillRuntime?] using hsp)
  obtain ⟨cs, _, hR⟩ := resolve_runtimeBlock hrt r.reserved
  rw [← hbase] at hR
  rw [hf.block_eq, hR, rewriteStmts_cons, rewriteStmt_cond_empty_lit,
    rewriteStmts_cons, rewriteStmt_lockCheck]
  simp [rewriteStmts, rewriteStmt, hoistInfos, lockCheckStmt]

theorem compileProgram_lockPrefix {prog : YBlock} {k : Nat} {tail : YBlock}
    {asm : List Asm}
    (hshape : prog = .cond (lit k) [] :: lockCheckStmt :: tail)
    (hhoist : hoistInfos 0 prog = ([], 0))
    (h : compileProgram prog = some asm) :
    ∃ restAsm, asm = lockPrefixAsmRaw k ++ restAsm ∧
      ∀ l ∈ labelRefs restAsm, 2 ≤ l := by
  obtain ⟨scope, n0, asm', Γ, n', hh, _, hs, _, rfl⟩ := compileProgram_inv h
  rw [hhoist] at hh
  simp only [Prod.mk.injEq] at hh
  rcases hh with ⟨rfl, rfl⟩
  rw [hshape] at hs
  obtain ⟨restAsm, hrest, rfl⟩ :=
    compileStmts_lockPrefix [[]] [] none none k tail hs
  exact ⟨restAsm, rfl, compileStmts_rest_ge Φentries_empty_scope rfl rfl hrest⟩

theorem compileProgram_erased_lockPrefix {c : ContractDef} {rt : YBlock}
    {asm : List Asm} (hrt : runtimeBlock c = some rt)
    (h : compileProgram (eraseMemoryGuardStmts rt) = some asm) :
    ∃ restAsm, asm = lockPrefixAsmRaw memoryGuardK ++ restAsm ∧
      ∀ l ∈ labelRefs restAsm, 2 ≤ l := by
  obtain ⟨cs, _, hE⟩ := erase_runtimeBlock hrt
  exact compileProgram_lockPrefix
    (tail := [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
      YulSemantics.Stmt.switch
        (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
        cs (some [revert00])])
    (by rw [hE]; simp [memoryGuardErased])
    (hoistInfos_erased_runtime hrt) h

theorem compileProgram_spilled_lockPrefix {c : ContractDef} {rt : YBlock}
    {r : Result} {asm : List Asm} (hrt : runtimeBlock c = some rt)
    (hsp : spillRuntime? rt = some r)
    (h : compileProgram r.block = some asm) :
    ∃ restAsm, asm = lockPrefixAsmRaw r.reserved ++ restAsm ∧
      ∀ l ∈ labelRefs restAsm, 2 ≤ l := by
  obtain ⟨tail, hblk, _⟩ := spilled_runtime_prefix_block hrt hsp
  exact compileProgram_lockPrefix hblk (hoistInfos_spilled_runtime hrt hsp) h

/-! ### Lowering the optimized prefix -/

theorem lockPrefixAsmOpt_eq_pre (k : Nat) :
    lockPrefixAsmOpt k = lockPrefixAsmOptPre k ++ [.label 1] := rfl

theorem labelDefs_lockPrefixAsmOptPre (k : Nat) :
    labelDefs (lockPrefixAsmOptPre k) = [] := by
  simp [lockPrefixAsmOptPre, labelDefs, Asm.defines]

theorem not_mem_labelDefs_optPre (k : Nat) (l : Label) :
    l ∉ labelDefs (lockPrefixAsmOptPre k) := by
  simp [labelDefs_lockPrefixAsmOptPre]

theorem conv_ofNat_of_lt {k : Nat} (h : k < 2 ^ 256) :
    conv (BitVec.ofNat 256 k) = EvmSemantics.UInt256.ofNat k := by
  rw [conv_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem byteWidth_zero : Instr.byteWidth 0 = 0 := by
  simp [Instr.byteWidth]

theorem codeSize_lockPrefixAsmOptPre (k : Nat) :
    codeSize (lockPrefixAsmOptPre k) =
      13 + Instr.byteWidth (conv (BitVec.ofNat 256 k)).toNat := by
  simp [lockPrefixAsmOptPre, codeSize, Asm.size, labelWidth, byteWidth_zero]
  omega

theorem resolve_lockPrefix_L1 (k : Nat) (rest : List Asm) :
    resolve 1 (lockPrefixAsmOpt k ++ rest) =
      some (codeSize (lockPrefixAsmOptPre k)) := by
  rw [lockPrefixAsmOpt_eq_pre, List.append_assoc]
  change resolve 1 (lockPrefixAsmOptPre k ++ .label 1 :: rest) = _
  exact resolve_of_not_mem (not_mem_labelDefs_optPre k 1) rest

theorem lowerInstr_push (imm : String → U256) (prog : List Asm)
    (v : BitVec 256) :
    lowerInstr imm prog (.push v) = some [Instr.pushMin (conv v)] := rfl

theorem lowerInstr_pop (imm : String → U256) (prog : List Asm) :
    lowerInstr imm prog .pop = some [.op .POP] := rfl

theorem lowerInstr_label (imm : String → U256) (prog : List Asm) (l : Label) :
    lowerInstr imm prog (.label l) = some [.op .JUMPDEST] := rfl

theorem lowerInstr_iszero (imm : String → U256) (prog : List Asm) :
    lowerInstr imm prog (.op .iszero) = some [.op .ISZERO] := by
  simp [lowerInstr, opTable]

theorem lowerInstr_tload (imm : String → U256) (prog : List Asm) :
    lowerInstr imm prog (.op .tload) = some [.op .TLOAD] := by
  simp [lowerInstr, opTable]

theorem lowerInstr_revert (imm : String → U256) (prog : List Asm) :
    lowerInstr imm prog (.op .revert) = some [.op .REVERT] := by
  simp [lowerInstr, opTable]

theorem lowerInstr_jumpi (imm : String → U256) (prog : List Asm) (l dest : Nat)
    (h : resolve l prog = some dest) :
    lowerInstr imm prog (.jumpi l) =
      some [Instr.push labelWidthFin (EvmSemantics.UInt256.ofNat dest),
        .op .JUMPI] := by
  simp [lowerInstr, h]

theorem lowerFrag_lockPrefixAsm (imm : String → U256) (k : Nat)
    (rest : List Asm) (hk : k < 2 ^ 256) :
    lowerFrag imm (lockPrefixAsmOpt k ++ rest) (lockPrefixAsmOpt k) =
      some (lockPrefixInstrs k (codeSize (lockPrefixAsmOptPre k))) := by
  have hres := resolve_lockPrefix_L1 k rest
  have hk' := conv_ofNat_of_lt hk
  have h0 : conv (0 : BitVec 256) = ⟨0⟩ := conv_zero
  set prog := lockPrefixAsmOpt k ++ rest
  have h :=
    lowerFrag_cons' (lowerInstr_push imm prog (BitVec.ofNat 256 k)) <|
    lowerFrag_cons' (lowerInstr_iszero imm prog) <|
    lowerFrag_cons' (lowerInstr_pop imm prog) <|
    lowerFrag_cons' (lowerInstr_push imm prog (0 : BitVec 256)) <|
    lowerFrag_cons' (lowerInstr_tload imm prog) <|
    lowerFrag_cons' (lowerInstr_iszero imm prog) <|
    lowerFrag_cons' (lowerInstr_jumpi imm prog 1 _ hres) <|
    lowerFrag_cons' (lowerInstr_push imm prog (0 : BitVec 256)) <|
    lowerFrag_cons' (lowerInstr_push imm prog (0 : BitVec 256)) <|
    lowerFrag_cons' (lowerInstr_revert imm prog) <|
    lowerFrag_cons' (lowerInstr_label imm prog 1)
      (rfl : lowerFrag imm prog [] = some [])
  simp only [lockPrefixInstrs]
  rw [← hk', ← h0]
  exact h

theorem lowerFrag_lockPrefixOpt (imm : String → U256) (k : Nat)
    (rest : List Asm) {restIs : List Instr}
    (hk : k < 2 ^ 256)
    (hrest : lowerFrag imm (lockPrefixAsmOpt k ++ rest) rest = some restIs) :
    lowerFrag imm (lockPrefixAsmOpt k ++ rest) (lockPrefixAsmOpt k ++ rest) =
      some (lockPrefixInstrs k (codeSize (lockPrefixAsmOptPre k)) ++ restIs) :=
  lowerFrag_append' (lowerFrag_lockPrefixAsm imm k rest hk) hrest

theorem conv_toNat_ofNat_of_lt {k : Nat} (hk : k < 2 ^ 256) :
    (conv (BitVec.ofNat 256 k)).toNat = k := by
  rw [conv_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem codeSize_lockPrefixAsmOptPre_byteWidth (k : Nat) (hk : k < 2 ^ 256) :
    codeSize (lockPrefixAsmOptPre k) = 13 + Instr.byteWidth k := by
  rw [codeSize_lockPrefixAsmOptPre, conv_toNat_ofNat_of_lt hk]

theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 :=
  have h8 : (256 : Nat) = 2 ^ 8 := rfl
  h8 ▸ (Nat.pow_mul 2 8 32).symm

theorem byteWidth_le_32_of_lt {k : Nat} (hk : k < 2 ^ 256) :
    Instr.byteWidth k ≤ 32 :=
  Instr.byteWidth_le_of_lt_pow k 32 (pow_256_32 ▸ hk)

theorem dest_lockPrefix_lt_256 (k : Nat) (hk : k < 2 ^ 256) :
    13 + Instr.byteWidth k < 256 := by
  have := byteWidth_le_32_of_lt hk
  omega

theorem natToBE_two_of_lt_256 {n : Nat} (h : n < 256) :
    natToBE n 2 = [0, UInt8.ofNat n] := by
  have hdiv : n / 256 = 0 := Nat.div_eq_of_lt h
  have hmod : n % 256 = n := Nat.mod_eq_of_lt h
  simp [natToBE, hdiv, hmod]

theorem ofBytes2_natToBE_two {n : Nat} (h : n < 256) :
    ofBytes2 0 (UInt8.ofNat n) = n := by
  simp [ofBytes2, UInt8.toNat, UInt8.ofNat, Nat.mod_eq_of_lt h]

theorem assembleBytes_lockPrefixInstrs (k dest : Nat) :
    assembleBytes (lockPrefixInstrs k dest) =
      lockPrefixP1 k ++
        natToBE (EvmSemantics.UInt256.ofNat dest).toNat labelWidth ++
        lockPrefixP2 := by
  simp [lockPrefixInstrs, lockPrefixP1, lockPrefixP2, assembleBytes,
    Instr.bytes, labelWidthFin_val, List.append_assoc]

theorem assembleBytes_lockPrefix_bytes (k : Nat) (hk : k < 2 ^ 256) :
    assembleBytes (lockPrefixInstrs k (13 + Instr.byteWidth k)) =
      lockPrefixP1 k ++ [0, UInt8.ofNat (13 + Instr.byteWidth k)] ++
        lockPrefixP2 := by
  have hdest := dest_lockPrefix_lt_256 k hk
  have hlt : 13 + Instr.byteWidth k < 2 ^ 256 := by omega
  rw [assembleBytes_lockPrefixInstrs, toNat_u256_ofNat, Nat.mod_eq_of_lt hlt]
  change _ ++ natToBE _ 2 ++ _ = _
  rw [natToBE_two_of_lt_256 hdest]

theorem memoryGuardK_lt : memoryGuardK < 2 ^ 256 := by
  simp [memoryGuardK]

theorem runtime_prefix_of_compile {k : Nat} {asm restAsm rest' : List Asm}
    {is : List Instr}
    (hk : k < 2 ^ 256)
    (hasm : asm = lockPrefixAsmRaw k ++ restAsm)
    (hge : ∀ l ∈ labelRefs restAsm, 2 ≤ l)
    (hopt : optimizeAsm asm = lockPrefixAsmOpt k ++ rest')
    (hlow : lowerProg unpatchedImmutables (optimizeAsm asm) = some is) :
    ∃ w hi lo restBytes,
      w = Instr.byteWidth k ∧
      assembleBytes is =
        lockPrefixP1 k ++ [hi, lo] ++ lockPrefixP2 ++ restBytes ∧
      ofBytes2 hi lo = 13 + w := by
  rw [hopt] at hlow
  obtain ⟨is1, is2, h1, h2, rfl⟩ :=
    lowerFrag_append (p := lockPrefixAsmOpt k) (q := rest') hlow
  have hpre := lowerFrag_lockPrefixAsm unpatchedImmutables k rest' hk
  have his1 : is1 = lockPrefixInstrs k (codeSize (lockPrefixAsmOptPre k)) :=
    Option.some.inj (h1.symm.trans hpre)
  subst his1
  have hcs := codeSize_lockPrefixAsmOptPre_byteWidth k hk
  rw [hcs]
  refine ⟨Instr.byteWidth k, 0, UInt8.ofNat (13 + Instr.byteWidth k),
    assembleBytes is2, rfl, ?_, ?_⟩
  · rw [assembleBytes_append, assembleBytes_lockPrefix_bytes k hk]
  · exact ofBytes2_natToBE_two (dest_lockPrefix_lt_256 k hk)

theorem runtime_prefix {c : ContractDef} {rt : YBlock} {is : List Instr}
    (hrt : runtimeBlock c = some rt) (h : compileBlock rt = some is) :
    ∃ k w hi lo rest,
      w = Instr.byteWidth k ∧
      assembleBytes is =
        lockPrefixP1 k ++ [hi, lo] ++ lockPrefixP2 ++ rest ∧
      ofBytes2 hi lo = 13 + w ∧
      ((compileErased rt = some is ∧ k = memoryGuardK) ∨
        (compileErased rt = none ∧
          ∃ r, spillRuntime? rt = some r ∧ k = r.reserved)) := by
  cases compileBlock_elim h with
  | inl hE =>
    obtain ⟨asm, hp, _, hlow⟩ := yulCompile_inv hE
    obtain ⟨restAsm, hr, hge⟩ := compileProgram_erased_lockPrefix hrt hp
    obtain ⟨rest', hopt⟩ := optimizeAsm_lockPrefix memoryGuardK restAsm hge
    obtain ⟨w, hi, lo, restBytes, hw, hbytes, hdest⟩ :=
      runtime_prefix_of_compile memoryGuardK_lt hr hge
        (by simpa [hr] using hopt) hlow
    exact ⟨memoryGuardK, w, hi, lo, restBytes, hw, hbytes, hdest, Or.inl ⟨hE, rfl⟩⟩
  | inr hS =>
    obtain ⟨hne, hsp⟩ := hS
    obtain ⟨r, hsp', hcomp⟩ := compileSpilled_inv hsp
    obtain ⟨asm, hp, _, hlow⟩ := yulCompile_inv hcomp
    obtain ⟨restAsm, hr, hge⟩ := compileProgram_spilled_lockPrefix hrt hsp' hp
    obtain ⟨rest', hopt⟩ := optimizeAsm_lockPrefix r.reserved restAsm hge
    have hk : r.reserved < 2 ^ 256 := (spillRuntime_reserved_facts hsp').2
    obtain ⟨w, hi, lo, restBytes, hw, hbytes, hdest⟩ :=
      runtime_prefix_of_compile hk hr hge (by simpa [hr] using hopt) hlow
    exact ⟨r.reserved, w, hi, lo, restBytes, hw, hbytes, hdest,
      Or.inr ⟨hne, r, hsp', rfl⟩⟩

theorem runtime_prefix_k_lt {c : ContractDef} {rt : YBlock} {is : List Instr}
    {k : Nat}
    (h : (compileErased rt = some is ∧ k = memoryGuardK) ∨
      (compileErased rt = none ∧
        ∃ r, spillRuntime? rt = some r ∧ k = r.reserved)) :
    k < 2 ^ 256 := by
  cases h with
  | inl h =>
    obtain ⟨_, rfl⟩ := h
    exact memoryGuardK_lt
  | inr h =>
    obtain ⟨_, r, hsp, rfl⟩ := h
    exact (spillRuntime_reserved_facts hsp).2

theorem runtime_prefix_k_pos {c : ContractDef} {rt : YBlock} {is : List Instr}
    {k : Nat}
    (h : (compileErased rt = some is ∧ k = memoryGuardK) ∨
      (compileErased rt = none ∧
        ∃ r, spillRuntime? rt = some r ∧ k = r.reserved)) :
    0 < k := by
  cases h with
  | inl h =>
    obtain ⟨_, rfl⟩ := h
    simp [memoryGuardK]
  | inr h =>
    obtain ⟨_, r, hsp, rfl⟩ := h
    exact Nat.pos_of_ne_zero (spillRuntime_reserved_facts hsp).1

theorem uint8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨va⟩ := a
  obtain ⟨vb⟩ := b
  congr 1
  exact BitVec.eq_of_toNat_eq h

theorem uint8_toNat_lt (x : UInt8) : x.toNat < 256 :=
  x.toBitVec.isLt

theorem uint8_ofNat_toNat {n : Nat} (hn : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  change (BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem hi_lo_of_ofBytes2 {hi lo : UInt8} {n : Nat}
    (h : ofBytes2 hi lo = n) (hn : n < 256) :
    hi = 0 ∧ lo = UInt8.ofNat n := by
  have hsum : hi.toNat * 256 + lo.toNat = n := by
    simpa [ofBytes2] using h
  have hlo := uint8_toNat_lt lo
  have hhi0 : hi.toNat = 0 := by omega
  have hlon : lo.toNat = n := by omega
  refine ⟨uint8_eq_of_toNat ?_, uint8_eq_of_toNat ?_⟩
  · have hz : (0 : UInt8).toNat = 0 := rfl
    exact hhi0.trans hz.symm
  · exact hlon.trans (uint8_ofNat_toNat hn).symm

theorem runtime_prefix_instrs {c : ContractDef} {rt : YBlock} {is : List Instr}
    (hrt : runtimeBlock c = some rt) (h : compileBlock rt = some is) :
    ∃ k dest rest,
      k < 2 ^ 256 ∧ 0 < k ∧ dest = 13 + Instr.byteWidth k ∧
      assembleBytes is = assembleBytes (lockPrefixInstrs k dest) ++ rest := by
  obtain ⟨k, w, hi, lo, rest, hw, hbytes, hdest, hpath⟩ := runtime_prefix hrt h
  have hk := runtime_prefix_k_lt (c := c) hpath
  have hpos := runtime_prefix_k_pos (c := c) hpath
  subst hw
  have hpair := hi_lo_of_ofBytes2 hdest (dest_lockPrefix_lt_256 k hk)
  refine ⟨k, 13 + Instr.byteWidth k, rest, hk, hpos, rfl, ?_⟩
  rw [hbytes, assembleBytes_lockPrefix_bytes k hk, hpair.1, hpair.2]

end Proof

end Lsc.Compiler
