import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.EvmYulBridge
import Lsc.Compile.IR.WordEval

namespace Lsc.Compile.Bytecode

open EvmYul EvmYul.EVM EvmYul.Operation
open Lsc.Compile.IR
open EvmYulBridge
open EvmYulTrust

abbrev EWord := EvmYul.UInt256

/-- Exact expression fragment used by linear fixed-math views. `caller` is excluded because fixed
math views read their argument from calldata. -/
def ViewExpr : Expr → Prop
  | .lit n => pushWidth n ≤ 32
  | .sload _ => False
  | .calldataWord offset => pushWidth offset ≤ 32
  | .local name => name ≠ "caller"
  | .add a b | .sub a b | .mul a b | .div a b | .gt a b | .xor a b =>
      ViewExpr a ∧ ViewExpr b
  | .shr amount value => ViewExpr amount ∧ ViewExpr value
  | _ => False

/-- A view expression whose local reload graph fits in `fuel`.

Unlike `ViewExpr`, this predicate records the well-founded part of deep-local compilation:
every local has a recorded source, that source denotes the local's current word value, and
recursively rebuilding it consumes one unit of fuel.  Arithmetic recursion does not consume
reload fuel, matching `Codegen.codegenExprFuel`. -/
def ReloadableViewExpr : Nat → List (Lsc.Ident × LocalBinding) → WordState → Expr → Prop
  | _, _, _, .lit n => pushWidth n ≤ 32
  | _, _, _, .sload _ => False
  | _, _, _, .calldataWord offset => pushWidth offset ≤ 32
  | fuel, locals, word, .local name =>
      name ≠ "caller" ∧
      ∃ binding source,
        ({ locals := locals } : Ctx).lookupBinding name = some binding ∧
        binding.src = some source ∧
        evalExprWord word source = some (word.lookupLocal name) ∧
        match fuel with
        | 0 => False
        | next + 1 => ReloadableViewExpr next locals word source
  | fuel, locals, word, .add a b | fuel, locals, word, .sub a b
  | fuel, locals, word, .mul a b | fuel, locals, word, .div a b
  | fuel, locals, word, .gt a b | fuel, locals, word, .xor a b =>
      ReloadableViewExpr fuel locals word a ∧ ReloadableViewExpr fuel locals word b
  | fuel, locals, word, .shr amount value =>
      ReloadableViewExpr fuel locals word amount ∧ ReloadableViewExpr fuel locals word value
  | _, _, _, _ => False
termination_by fuel locals word e => (fuel, sizeOf e)

theorem ReloadableViewExpr.view {fuel : Nat} {locals : List (Lsc.Ident × LocalBinding)}
    {word : WordState} {e : Expr}
    (h : ReloadableViewExpr fuel locals word e) : ViewExpr e := by
  induction e with
  | lit n => simpa only [ReloadableViewExpr, ViewExpr] using h
  | «local» name =>
      simp only [ReloadableViewExpr] at h
      exact h.1
  | calldataWord offset => simpa only [ReloadableViewExpr, ViewExpr] using h
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
  | gt a b iha ihb | shr a b iha ihb | xor a b iha ihb =>
      simp only [ReloadableViewExpr] at h
      exact ⟨iha h.1, ihb h.2⟩
  | sload | mapSlot | mapSlot2 | dynSload | lt | eq | isZero =>
      simp [ReloadableViewExpr] at h

/-- A sequencing driver over EvmYul's own instruction semantics. It does not define opcode
behavior: every transition is the real `EVM.step`, after the same memory/gas precheck update used
by `EVM.X`. -/
def runView : List Instr → EVM.State → Except EVM.ExecutionException EVM.State
  | [], st => .ok st
  | instr :: rest, st => do
      let decoded := decodedPlainInstr instr
      let next ← EVM.step 1 (checkedCost st decoded.1) (some decoded)
        (checkedState st decoded.1)
      runView rest next

theorem runView_append (first rest : List Instr) (st : EVM.State) :
    runView (first ++ rest) st = (runView first st).bind (runView rest) := by
  induction first generalizing st with
  | nil => rfl
  | cons instr first ih =>
      simp only [List.cons_append, runView]
      cases hs : EVM.step 1 (checkedCost st (decodedPlainInstr instr).1)
          (some (decodedPlainInstr instr)) (checkedState st (decodedPlainInstr instr).1) <;>
        simp [hs, ih, Bind.bind, Except.bind]

def SourcesAgree (st : EVM.State) (word : WordState) : Prop :=
  (∀ slot, (EvmYul.State.sload st.toState (.ofNat slot)).2 = word.slots slot) ∧
  ∀ offset, EvmYul.State.calldataload st.toState (.ofNat offset) = word.calldata offset

structure FramePreserved (before after : EVM.State) : Prop where
  accountMap : after.accountMap = before.accountMap
  executionEnv : after.executionEnv = before.executionEnv
  memory : after.memory = before.memory

theorem FramePreserved.refl (st : EVM.State) : FramePreserved st st := ⟨rfl, rfl, rfl⟩

theorem FramePreserved.trans {a b c : EVM.State}
    (hab : FramePreserved a b) (hbc : FramePreserved b c) :
    FramePreserved a c :=
  ⟨hbc.accountMap.trans hab.accountMap, hbc.executionEnv.trans hab.executionEnv,
    hbc.memory.trans hab.memory⟩

theorem checkedState_setStack (st : EVM.State) (op : Operation .EVM)
    (stack : List EWord) (hstack : st.stack = stack) :
    checkedState st op = { checkedState st op with stack := stack } := by
  cases st with
  | mk shared pc currentStack execLength =>
      change currentStack = stack at hstack
      subst currentStack
      rfl

theorem state_setStack (st : EVM.State) (stack : List EWord)
    (hstack : st.stack = stack) :
    st = { st with stack := stack } := by
  cases st with
  | mk shared pc currentStack execLength =>
      change currentStack = stack at hstack
      subst currentStack
      rfl

theorem SourcesAgree.of_frame {before after : EVM.State} {word : WordState}
    (h : SourcesAgree before word) (frame : FramePreserved before after) :
    SourcesAgree after word := by
  constructor
  · intro slot
    simp only [EvmYul.State.sload, EvmYul.State.lookupAccount]
    rw [frame.accountMap, frame.executionEnv]
    exact h.1 slot
  · intro offset
    simp only [EvmYul.State.calldataload]
    rw [frame.executionEnv]
    exact h.2 offset

/-- Stack/context invariant. A binding's absolute position is converted to the zero-based EVM DUP
index from the current top. -/
structure ContextAgrees (ctx : Ctx) (st : EVM.State) (word : WordState) : Prop where
  depth : ctx.stackDepth = st.stack.length
  locals : ∀ name binding, ctx.lookupBinding name = some binding →
    binding.absPos ≤ ctx.stackDepth ∧
    ∃ h : ctx.stackDepth - binding.absPos < st.stack.length,
      st.stack[ctx.stackDepth - binding.absPos] = word.lookupLocal name
  reloads : ∀ name binding source, ctx.lookupBinding name = some binding →
    binding.src = some source →
    ViewExpr source ∧ evalExprWord word source = some (word.lookupLocal name)
  reloadPlans : ∀ name binding source, ctx.lookupBinding name = some binding →
    binding.src = some source →
    ReloadableViewExpr ctx.locals.length ctx.locals word source
  sources : SourcesAgree st word

theorem contextAgrees_empty (st : EVM.State) (word : WordState)
    (hstack : st.stack = []) (hsources : SourcesAgree st word) :
    ContextAgrees ({} : Ctx) st word := by
  constructor
  · simp [hstack]
  · intro name binding h
    simp [Ctx.lookupBinding] at h
  · intro name binding source h
    simp [Ctx.lookupBinding] at h
  · intro name binding source h
    simp [Ctx.lookupBinding] at h
  · exact hsources

theorem ContextAgrees.pushResult {ctx : Ctx} {st final : EVM.State}
    {word : WordState} (hctx : ContextAgrees ctx st word) (value : EWord)
    (hstack : final.stack = value :: st.stack)
    (hsources : SourcesAgree final word) :
    ContextAgrees { ctx with stackDepth := ctx.stackDepth + 1 } final word := by
  constructor
  · rw [hstack, List.length_cons, ← hctx.depth]
  · intro name binding hlookup
    have hold : ctx.lookupBinding name = some binding := by
      simpa [Ctx.lookupBinding] using hlookup
    obtain ⟨hle, hi, hvalue⟩ := hctx.locals name binding hold
    constructor
    · change binding.absPos ≤ ctx.stackDepth + 1
      omega
    · have hindex :
          ctx.stackDepth + 1 - binding.absPos =
            (ctx.stackDepth - binding.absPos) + 1 := by omega
      have hbound :
          ctx.stackDepth + 1 - binding.absPos < final.stack.length := by
        rw [hstack, List.length_cons, hindex]
        omega
      refine ⟨hbound, ?_⟩
      change final.stack[ctx.stackDepth + 1 - binding.absPos] = word.lookupLocal name
      simp only [hstack, hindex, List.getElem_cons_succ]
      simpa using hvalue
  · intro name binding source hlookup hsource
    have hold : ctx.lookupBinding name = some binding := by
      simpa [Ctx.lookupBinding] using hlookup
    exact hctx.reloads name binding source hold hsource
  · intro name binding source hlookup hsource
    have hold : ctx.lookupBinding name = some binding := by
      simpa [Ctx.lookupBinding] using hlookup
    simpa using hctx.reloadPlans name binding source hold hsource
  · exact hsources

theorem ContextAgrees.bindLocal {ctx : Ctx} {st : EVM.State} {word : WordState}
    (hctx : ContextAgrees ctx st word) (name : Lsc.Ident) (value : EWord)
    (src : Option Expr) (tail : List EWord) (hstack : st.stack = value :: tail)
    (hreload : ∀ source, src = some source →
      ViewExpr source ∧ evalExprWord (word.setLocal name value) source = some value)
    (hpreserve : ∀ queried binding source,
      ctx.lookupBinding queried = some binding →
      binding.src = some source →
      evalExprWord (word.setLocal name value) source =
        evalExprWord word source)
    (hplan : ∀ source, src = some source →
      ReloadableViewExpr (ctx.locals.length + 1)
        ((name, { absPos := ctx.stackDepth, src }) :: ctx.locals)
        (word.setLocal name value) source)
    (hplanPreserve : ∀ queried binding source,
      ctx.lookupBinding queried = some binding →
      binding.src = some source →
      ReloadableViewExpr ctx.locals.length ctx.locals word source →
      ReloadableViewExpr (ctx.locals.length + 1)
        ((name, { absPos := ctx.stackDepth, src }) :: ctx.locals)
        (word.setLocal name value) source) :
    ContextAgrees (ctx.bindLocal name src) st (word.setLocal name value) := by
  constructor
  · exact hctx.depth
  · intro queried binding hlookup
    by_cases hname : queried = name
    · subst queried
      simp [Ctx.bindLocal, Ctx.lookupBinding] at hlookup
      subst binding
      constructor
      · rfl
      · have hbound : ctx.stackDepth - ctx.stackDepth < st.stack.length := by
          rw [hstack]
          simp
        refine ⟨hbound, ?_⟩
        change st.stack[ctx.stackDepth - ctx.stackDepth] =
          (word.setLocal name value).lookupLocal name
        simp [hstack, WordState.lookupLocal, WordState.setLocal]
    · have hold : ctx.lookupBinding queried = some binding := by
        have hname' : name ≠ queried := Ne.symm hname
        simpa [Ctx.bindLocal, Ctx.lookupBinding, hname, hname'] using hlookup
      obtain ⟨hle, hi, hvalue⟩ := hctx.locals queried binding hold
      exact ⟨hle, hi, by
        change st.stack[ctx.stackDepth - binding.absPos] =
          (word.setLocal name value).lookupLocal queried
        rw [hvalue]
        simp [WordState.lookupLocal, WordState.setLocal, hname]⟩
  · intro queried binding source hlookup hsource
    by_cases hname : queried = name
    · subst queried
      simp [Ctx.bindLocal, Ctx.lookupBinding] at hlookup
      subst binding
      obtain ⟨hview, hvalue⟩ := hreload source hsource
      exact ⟨hview, by
        simpa [WordState.lookupLocal, WordState.setLocal] using hvalue⟩
    · have hold : ctx.lookupBinding queried = some binding := by
        have hname' : name ≠ queried := Ne.symm hname
        simpa [Ctx.bindLocal, Ctx.lookupBinding, hname, hname'] using hlookup
      obtain ⟨hview, hvalue⟩ :=
        hctx.reloads queried binding source hold hsource
      exact ⟨hview, by
        rw [hpreserve queried binding source hold hsource, hvalue]
        simp [WordState.lookupLocal, WordState.setLocal, hname]⟩
  · intro queried binding source hlookup hsource
    by_cases hname : queried = name
    · subst queried
      simp [Ctx.bindLocal, Ctx.lookupBinding] at hlookup
      subst binding
      exact hplan source hsource
    · have hold : ctx.lookupBinding queried = some binding := by
        have hname' : name ≠ queried := Ne.symm hname
        simpa [Ctx.bindLocal, Ctx.lookupBinding, hname, hname'] using hlookup
      exact hplanPreserve queried binding source hold hsource
        (hctx.reloadPlans queried binding source hold hsource)
  · constructor
    · intro slot
      exact hctx.sources.1 slot
    · intro offset
      exact hctx.sources.2 offset

def ReturnEpilogue : List Instr :=
  [.push 0, .op .MSTORE, .push 32, .push 0, .op .RETURN]

theorem word_ofNat_add (a b : Nat) :
    EvmYul.UInt256.ofNat (a + b) = .ofNat a + .ofNat b := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change (a + b) % EvmYul.UInt256.size =
    (a % EvmYul.UInt256.size + b % EvmYul.UInt256.size) % EvmYul.UInt256.size
  exact Nat.add_mod a b EvmYul.UInt256.size

theorem word_add_assoc (a b c : EWord) : a + b + c = a + (b + c) := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change ((a.val + b.val) % EvmYul.UInt256.size + c.val) % EvmYul.UInt256.size =
    (a.val + (b.val + c.val) % EvmYul.UInt256.size) % EvmYul.UInt256.size
  calc
    _ = (a.val + b.val + c.val) % EvmYul.UInt256.size := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt c.val.isLt]
    _ = (a.val + (b.val + c.val)) % EvmYul.UInt256.size := by
      rw [Nat.add_assoc]
    _ = _ := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt a.val.isLt]

theorem word_add_comm (a b : EWord) :
    EvmYul.UInt256.add a b = EvmYul.UInt256.add b a := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change (a.val + b.val) % EvmYul.UInt256.size =
    (b.val + a.val) % EvmYul.UInt256.size
  rw [Nat.add_comm]

theorem word_mul_comm (a b : EWord) :
    EvmYul.UInt256.mul a b = EvmYul.UInt256.mul b a := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change (a.val * b.val) % EvmYul.UInt256.size =
    (b.val * a.val) % EvmYul.UInt256.size
  rw [Nat.mul_comm]

theorem word_xor_comm (a b : EWord) :
    EvmYul.UInt256.xor a b = EvmYul.UInt256.xor b a := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simp [EvmYul.UInt256.xor, Fin.xor, Nat.xor_comm]

theorem dupOp_success_bounds (depth : Nat) (op : Operation .EVM)
    (h : Ctx.dupOp depth = .ok op) :
    1 ≤ depth ∧ depth ≤ 16 := by
  simp [Ctx.dupOp] at h
  split at h <;> simp_all

theorem getLast!_take (xs : List EWord) (depth : Nat)
    (hpos : 1 ≤ depth) (hdepth : depth ≤ xs.length) :
    (xs.take depth).getLast! = xs[depth - 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpos
  simp only [Nat.add_comm 1 k, Nat.add_sub_cancel]
  change (xs.take (k + 1)).getLast! = xs[k]
  have hk : k < xs.length := by omega
  have hlen : (xs.take (k + 1)).length = k + 1 := by
    simp [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ xs.length)]
  cases ht : xs.take (k + 1) with
  | nil => simp [ht] at hlen
  | cons a rest =>
      rw [List.getLast!]
      rw [List.getLast_eq_getElem]
      have hi : (a :: rest).length - 1 = k := by
        rw [ht] at hlen
        omega
      simp only [hi, Nat.add_sub_cancel]
      have helem := List.getElem_take (xs := xs) (j := k + 1) (i := k)
        (h := by simpa [hlen] using Nat.lt_succ_self k)
      simpa [ht] using helem

def dupForDepth : Nat → DupOp
  | 1 => .d1 | 2 => .d2 | 3 => .d3 | 4 => .d4
  | 5 => .d5 | 6 => .d6 | 7 => .d7 | 8 => .d8
  | 9 => .d9 | 10 => .d10 | 11 => .d11 | 12 => .d12
  | 13 => .d13 | 14 => .d14 | 15 => .d15 | _ => .d16

theorem dupForDepth_depth (depth : Nat) (hpos : 1 ≤ depth) (hle : depth ≤ 16) :
    (dupForDepth depth).depth = depth := by
  interval_cases depth <;> rfl

theorem dupForDepth_op (depth : Nat) (op : Operation .EVM)
    (hdup : Ctx.dupOp depth = .ok op) :
    (dupForDepth depth).op = op := by
  obtain ⟨hlo, hhi⟩ := dupOp_success_bounds depth op hdup
  interval_cases depth <;> simp_all [Ctx.dupOp, dupForDepth, DupOp.op]

theorem evmStep_dupOp (depth : Nat) (op : Operation .EVM)
    (hdup : Ctx.dupOp depth = .ok op) (stack : List EWord) (value : EWord)
    (hdepth : depth ≤ stack.length) (hpos : 1 ≤ depth)
    (hvalue : stack[depth - 1] = value)
    (st : EVM.State) (hstack : st.stack = stack) (cost : Nat) :
    EVM.step 1 cost (some (op, none)) st =
      .ok {
        st with
        stack := value :: stack
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  let top := stack.take depth
  let tail := stack.drop depth
  have hlen : top.length = depth := by
    simp [top, List.length_take, Nat.min_eq_left hdepth]
  have hlast : top.getLast! = value := by
    rw [getLast!_take stack depth hpos hdepth, hvalue]
  have hlast' : top.getLast?.getD default = value := by
    cases ht : top with
    | nil =>
        rw [ht] at hlen
        simp at hlen
        omega
    | cons a rest =>
        rw [ht] at hlast
        simpa [ht, List.getLast!] using hlast
  have happend : top ++ tail = stack := List.take_append_drop ..
  have hb := dupOp_success_bounds depth op hdup
  have hddepth := dupForDepth_depth depth hb.1 hb.2
  have hdop := dupForDepth_op depth op hdup
  have hstate : st = { st with stack := stack } := by
    cases st with
    | mk shared pc currentStack execLength =>
        change currentStack = stack at hstack
        subst currentStack
        rfl
  rw [hstate]
  have hstep := evmStep_dup (fuel := 0) (cost := cost) (st := { st with stack := stack })
    (top := top) (tail := tail) (d := dupForDepth depth)
    (by simpa [hddepth] using hlen)
  rw [hdop] at hstep
  simpa [hlast, hlast', happend] using hstep

theorem dupOp_encodable (depth : Nat) (op : Operation .EVM)
    (hdup : Ctx.dupOp depth = .ok op) :
    EncodablePlainInstrs [.op op] := by
  obtain ⟨hlo, hhi⟩ := dupOp_success_bounds depth op hdup
  interval_cases depth <;> simp [Ctx.dupOp] at hdup <;> subst op <;>
    simp [EncodablePlainInstrs, EncodablePlainInstr, PlainInstr, Operation.isPush]

theorem codegenLit_correct (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (n : Nat) (hwidth : pushWidth n ≤ 32) :
    ∃ final,
      runView [.push n] st = .ok final ∧
      final.stack = .ofNat n :: st.stack ∧
      final.pc = st.pc + .ofNat (instrsByteSize [.push n]) ∧
      FramePreserved st final ∧
      ContextAgrees { ctx with stackDepth := ctx.stackDepth + 1 } final word := by
  let op := (decodedPlainInstr (.push n)).1
  let final : EVM.State := {
    checkedState st op with
    stack := .ofNat n :: st.stack
    pc := st.pc + .ofNat (pushWidth n + 1)
    gasAvailable := (checkedState st op).gasAvailable - .ofNat (checkedCost st op)
    execLength := (checkedState st op).execLength + 1 }
  have hstep : EVM.step 1 (checkedCost st op) (some (decodedPlainInstr (.push n)))
      (checkedState st op) = .ok final := by
    simpa [final, op] using
      evmStep_decodedPush n 0 (checkedCost st op) hwidth (checkedState st op)
  refine ⟨final, ?_, by simp [final], ?_, ?_, ?_⟩
  · simp only [runView]
    rw [hstep]
    rfl
  · simp [final, instrsByteSize, instrByteSize, Nat.add_comm]
  · exact ⟨rfl, rfl, rfl⟩
  · apply hctx.pushResult (.ofNat n)
    · simp [final]
    · exact hctx.sources.of_frame ⟨rfl, rfl, rfl⟩

def ExprCodegenCorrect (ctx : Ctx) (st : EVM.State) (word : WordState)
    (value : EWord) (instrs : List Instr) (out : Ctx) : Prop :=
  out = { ctx with stackDepth := ctx.stackDepth + 1 } ∧
  ∃ final,
    runView instrs st = .ok final ∧
    final.stack = value :: st.stack ∧
    final.pc = st.pc + .ofNat (instrsByteSize instrs) ∧
    FramePreserved st final ∧
    ContextAgrees { ctx with stackDepth := ctx.stackDepth + 1 } final word ∧
    EncodablePlainInstrs instrs

theorem instrsByteSize_append (a b : List Instr) :
    instrsByteSize (a ++ b) = instrsByteSize a + instrsByteSize b := by
  simp [instrsByteSize, List.sum_append]

theorem EncodablePlainInstrs.append {a b : List Instr}
    (ha : EncodablePlainInstrs a) (hb : EncodablePlainInstrs b) :
    EncodablePlainInstrs (a ++ b) := by
  intro instr hmem
  exact (List.mem_append.mp hmem).elim (ha instr) (hb instr)

def BinarySuffixCorrect (mid base : EVM.State) (result : EWord)
    (suffix : List Instr) : Prop :=
  ∃ final,
    runView suffix mid = .ok final ∧
    final.stack = result :: base.stack ∧
    final.pc = mid.pc + .ofNat (instrsByteSize suffix) ∧
    FramePreserved mid final ∧
    EncodablePlainInstrs suffix

theorem composeBinaryRaw (ctx out : Ctx) (st first second : EVM.State)
    (word : WordState) (result : EWord) (i1 i2 suffix : List Instr)
    (hctx : ContextAgrees ctx st word)
    (hr1 : runView i1 st = .ok first)
    (hp1 : first.pc = st.pc + .ofNat (instrsByteSize i1))
    (hf1 : FramePreserved st first) (he1 : EncodablePlainInstrs i1)
    (hr2 : runView i2 first = .ok second)
    (hp2 : second.pc = first.pc + .ofNat (instrsByteSize i2))
    (hf2 : FramePreserved first second) (he2 : EncodablePlainInstrs i2)
    (hout : out = { ctx with stackDepth := ctx.stackDepth + 1 })
    (hsuffix : BinarySuffixCorrect second st result suffix) :
    ExprCodegenCorrect ctx st word result (i1 ++ (i2 ++ suffix)) out := by
  rcases hsuffix with ⟨final, hrs, hss, hps, hfs, hes⟩
  refine ⟨hout, final, ?_, hss, ?_, hf1.trans (hf2.trans hfs), ?_, ?_⟩
  · rw [runView_append, hr1]
    simp only [Except.bind]
    rw [runView_append, hr2]
    simp only [Except.bind]
    exact hrs
  · rw [instrsByteSize_append, instrsByteSize_append]
    rw [hps, hp2, hp1]
    rw [word_add_assoc, word_add_assoc, ← word_ofNat_add, ← word_ofNat_add]
  · apply hctx.pushResult result
    · exact hss
    · exact hctx.sources.of_frame (hf1.trans (hf2.trans hfs))
  · exact EncodablePlainInstrs.append he1 (EncodablePlainInstrs.append he2 hes)

theorem binaryOneSuffix (mid base : EVM.State) (lhs rhs : EWord)
    (op : Operation .EVM) (result : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack)
    (hstep : ∀ (cost : Nat) (checked : EVM.State),
      checked.stack = rhs :: lhs :: base.stack →
      EVM.step 1 cost (some (op, none)) checked =
        .ok {
          checked with
          stack := result :: base.stack
          pc := checked.pc + .ofNat 1
          gasAvailable := checked.gasAvailable - .ofNat cost
          execLength := checked.execLength + 1 })
    (hnpush : ¬ Operation.isPush op) :
    BinarySuffixCorrect mid base result [.op op] := by
  let checked := checkedState mid op
  let cost := checkedCost mid op
  let final : EVM.State := {
    checked with
    stack := result :: base.stack
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat cost
    execLength := checked.execLength + 1 }
  have hcstack : checked.stack = rhs :: lhs :: base.stack := hstack
  have hs : EVM.step 1 cost (some (op, none)) checked = .ok final :=
    hstep cost checked hcstack
  refine ⟨final, ?_, by simp [final], ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
  · simp only [runView]
    change (do
      let next ← EVM.step 1 cost (some (op, none)) checked
      Except.ok next) = .ok final
    rw [hs]
    rfl
  · change final.pc = mid.pc + .ofNat 1
    simp [final, checked, checkedState]
  · intro instr hmem
    simp only [List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with rfl | h
    · exact ⟨hnpush, trivial⟩
    · contradiction

theorem binarySuffix_add (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.add lhs rhs) [.op .ADD] := by
  apply binaryOneSuffix mid base lhs rhs .ADD (EvmYul.UInt256.add lhs rhs) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    simpa [word_add_comm] using
      evmStep_add 0 cost checked rhs lhs base.stack
  · decide

theorem binarySuffix_mul (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.mul lhs rhs) [.op .MUL] := by
  apply binaryOneSuffix mid base lhs rhs .MUL (EvmYul.UInt256.mul lhs rhs) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    simpa [word_mul_comm] using
      evmStep_mul 0 cost checked rhs lhs base.stack
  · decide

theorem binarySuffix_xor (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.xor lhs rhs) [.op .XOR] := by
  apply binaryOneSuffix mid base lhs rhs .XOR (EvmYul.UInt256.xor lhs rhs) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    simpa [word_xor_comm] using
      evmStep_xor 0 cost checked rhs lhs base.stack
  · decide

theorem binarySwapSuffix (mid base : EVM.State) (lhs rhs : EWord)
    (op : Operation .EVM) (result : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack)
    (hstep : ∀ (cost : Nat) (checked : EVM.State),
      checked.stack = lhs :: rhs :: base.stack →
      EVM.step 1 cost (some (op, none)) checked =
        .ok {
          checked with
          stack := result :: base.stack
          pc := checked.pc + .ofNat 1
          gasAvailable := checked.gasAvailable - .ofNat cost
          execLength := checked.execLength + 1 })
    (hnpush : ¬ Operation.isPush op) :
    BinarySuffixCorrect mid base result [.op .SWAP1, .op op] := by
  let checkedSwap := checkedState mid .SWAP1
  let swapCost := checkedCost mid .SWAP1
  let swapped : EVM.State := {
    checkedSwap with
    stack := lhs :: rhs :: base.stack
    pc := checkedSwap.pc + .ofNat 1
    gasAvailable := checkedSwap.gasAvailable - .ofNat swapCost
    execLength := checkedSwap.execLength + 1 }
  have hswap : EVM.step 1 swapCost (some (.SWAP1, none)) checkedSwap = .ok swapped := by
    rw [state_setStack checkedSwap _ hstack]
    simpa [swapped, checkedSwap] using evmStep_swap1 0 swapCost checkedSwap rhs lhs base.stack
  let checked := checkedState swapped op
  let cost := checkedCost swapped op
  let final : EVM.State := {
    checked with
    stack := result :: base.stack
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat cost
    execLength := checked.execLength + 1 }
  have hcstack : checked.stack = lhs :: rhs :: base.stack := by
    change swapped.stack = lhs :: rhs :: base.stack
    rfl
  have hs : EVM.step 1 cost (some (op, none)) checked = .ok final :=
    hstep cost checked hcstack
  refine ⟨final, ?_, by simp [final], ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
  · simp only [runView, decodedPlainInstr]
    rw [hswap]
    change (do
      let next ← EVM.step 1 cost (some (op, none)) checked
      Except.ok next) = .ok final
    rw [hs]
    rfl
  · change final.pc = mid.pc + .ofNat 2
    change (mid.pc + .ofNat 1) + .ofNat 1 = mid.pc + .ofNat 2
    rw [word_add_assoc, ← word_ofNat_add]
  · intro instr hmem
    simp only [List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with rfl | rfl | h
    · exact ⟨by simp [PlainInstr, Operation.isPush], trivial⟩
    · exact ⟨hnpush, trivial⟩
    · contradiction

theorem binarySuffix_sub (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.sub lhs rhs)
      [.op .SWAP1, .op .SUB] := by
  apply binarySwapSuffix mid base lhs rhs .SUB (EvmYul.UInt256.sub lhs rhs) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    exact evmStep_sub 0 cost checked lhs rhs base.stack
  · decide

theorem binarySuffix_div (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.div lhs rhs)
      [.op .SWAP1, .op .DIV] := by
  apply binarySwapSuffix mid base lhs rhs .DIV (EvmYul.UInt256.div lhs rhs) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    exact evmStep_div 0 cost checked lhs rhs base.stack
  · decide

theorem binarySuffix_gt (mid base : EVM.State) (lhs rhs : EWord)
    (hstack : mid.stack = rhs :: lhs :: base.stack) :
    BinarySuffixCorrect mid base (boolWord (decide (rhs < lhs)))
      [.op .SWAP1, .op .GT] := by
  apply binarySwapSuffix mid base lhs rhs .GT (boolWord (decide (rhs < lhs))) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    by_cases hlt : rhs < lhs <;>
      simpa [EvmYul.UInt256.gt, boolWord, hlt] using
        evmStep_gt 0 cost checked lhs rhs base.stack
  · decide

theorem binarySuffix_shr (mid base : EVM.State) (amount value : EWord)
    (hstack : mid.stack = value :: amount :: base.stack) :
    BinarySuffixCorrect mid base (EvmYul.UInt256.shiftRight value amount)
      [.op .SWAP1, .op .SHR] := by
  apply binarySwapSuffix mid base amount value .SHR
    (EvmYul.UInt256.shiftRight value amount) hstack
  · intro cost checked hs
    rw [state_setStack checked _ hs]
    exact evmStep_shr 0 cost checked amount value base.stack
  · decide

theorem codegenLit_result (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (n : Nat) (hwidth : pushWidth n ≤ 32) :
    ExprCodegenCorrect ctx st word (.ofNat n) [.push n]
      { ctx with stackDepth := ctx.stackDepth + 1 } := by
  obtain ⟨final, hrun, hstack, hpc, hframe, hcontext⟩ :=
    codegenLit_correct ctx st word hctx n hwidth
  exact ⟨rfl, final, hrun, hstack, hpc, hframe, hcontext,
    by
      intro instr hmem
      simp only [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with rfl | h
      · exact ⟨by simp [PlainInstr], hwidth⟩
      · contradiction⟩

theorem codegenLocalDup_result (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (name : Lsc.Ident) (binding : LocalBinding)
    (hb : ctx.lookupBinding name = some binding) (depth : Nat)
    (hdepth : depth = ctx.stackDepth - binding.absPos + 1)
    (op : Operation .EVM) (ho : Ctx.dupOp depth = .ok op) :
    ExprCodegenCorrect ctx st word (word.lookupLocal name) (Codegen.emitOp op)
      { ctx with stackDepth := ctx.stackDepth + 1 } := by
              obtain ⟨hle, hi, hvalue⟩ := hctx.locals name binding hb
              have hpos : 1 ≤ depth := by omega
              have hdepthStack : depth ≤ st.stack.length := by
                rw [hdepth]
                omega
              let checked := checkedState st op
              let cost := checkedCost st op
              let final : EVM.State := {
                checked with
                stack := word.lookupLocal name :: st.stack
                pc := checked.pc + .ofNat 1
                gasAvailable := checked.gasAvailable - .ofNat cost
                execLength := checked.execLength + 1 }
              have hstep : EVM.step 1 cost (some (op, none)) checked = .ok final := by
                have hidx : depth - 1 = ctx.stackDepth - binding.absPos := by omega
                have hval : st.stack[depth - 1] = word.lookupLocal name := by
                  simpa only [hidx] using hvalue
                simpa [final, checked] using
                  evmStep_dupOp depth op ho st.stack (word.lookupLocal name)
                    hdepthStack hpos hval checked rfl cost
              have hframe : FramePreserved st final := ⟨rfl, rfl, rfl⟩
              refine ⟨rfl, final, ?_, by simp [final], ?_, hframe, ?_,
                dupOp_encodable depth op ho⟩
              · simp only [Codegen.emitOp, runView]
                change (do
                  let next ← EVM.step 1 cost (some (op, none)) checked
                  Except.ok next) = .ok final
                rw [hstep]
                rfl
              · change final.pc = st.pc + .ofNat 1
                simp [final, checked, checkedState]
              · apply hctx.pushResult (word.lookupLocal name)
                · simp [final]
                · exact hctx.sources.of_frame hframe

theorem codegenCalldata_result (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (offset : Nat) (hwidth : pushWidth offset ≤ 32) :
    ExprCodegenCorrect ctx st word (word.calldata offset)
      [.push offset, .op .CALLDATALOAD]
      { ctx with stackDepth := ctx.stackDepth + 1 } := by
  obtain ⟨pushed, hpush, hpstack, hppc, hpframe, hpctx⟩ :=
    codegenLit_correct ctx st word hctx offset hwidth
  let checked := checkedState pushed .CALLDATALOAD
  let cost := checkedCost pushed .CALLDATALOAD
  let final : EVM.State := {
    checked with
    stack := word.calldata offset :: st.stack
    pc := checked.pc + .ofNat 1
    gasAvailable := checked.gasAvailable - .ofNat cost
    execLength := checked.execLength + 1 }
  have hpSource : SourcesAgree pushed word := hctx.sources.of_frame hpframe
  have hsource :
      EvmYul.State.calldataload checked.toState (.ofNat offset) = word.calldata offset :=
    hpSource.2 offset
  have hcheckedStack : checked.stack = .ofNat offset :: st.stack := hpstack
  have hstep : EVM.step 1 cost (some (.CALLDATALOAD, none)) checked = .ok final := by
    have hstate : checked = { checked with stack := .ofNat offset :: st.stack } := by
      exact checkedState_setStack pushed .CALLDATALOAD _ hpstack
    rw [hstate]
    have hs := evmStep_calldataload 0 cost checked (.ofNat offset) st.stack
    rw [hsource] at hs
    simpa [final, checked] using hs
  have hopframe : FramePreserved pushed final := ⟨rfl, rfl, rfl⟩
  have hframe := hpframe.trans hopframe
  refine ⟨rfl, final, ?_, by simp [final], ?_, hframe, ?_, ?_⟩
  · change runView ([Instr.push offset] ++ [Instr.op .CALLDATALOAD]) st = .ok final
    rw [runView_append, hpush]
    simp only [Bind.bind, Except.bind, runView]
    change (do
      let next ← EVM.step 1 cost (some (.CALLDATALOAD, none)) checked
      Except.ok next) = .ok final
    rw [hstep]
    rfl
  · rw [show instrsByteSize [Instr.push offset, Instr.op .CALLDATALOAD] =
      2 + pushWidth offset by
        simp [instrsByteSize, instrByteSize]
        omega]
    change pushed.pc + .ofNat 1 = st.pc + .ofNat (2 + pushWidth offset)
    rw [hppc]
    change st.pc + .ofNat (1 + pushWidth offset) + .ofNat 1 =
      st.pc + .ofNat (2 + pushWidth offset)
    rw [word_add_assoc, ← word_ofNat_add]
    congr 2
    omega
  · apply hctx.pushResult (word.calldata offset)
    · simp [final]
    · exact hctx.sources.of_frame hframe
  · intro instr hmem
    simp only [List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with rfl | rfl | h
    · exact ⟨by simp [PlainInstr], hwidth⟩
    · exact ⟨by simp [PlainInstr, Operation.isPush], trivial⟩
    · contradiction

/-- Fuel-indexed direct-EvmYul correctness for expression rebuilding.  The reload predicate is
the well-founded semantic invariant: local sources consume one unit of fuel and evaluate to the
word value represented by the local. -/
theorem codegenExprFuel_correct (fuel : Nat) (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (e : Expr)
    (hreload : ReloadableViewExpr fuel ctx.locals word e)
    (value : EWord) (hvalue : evalExprWord word e = some value)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.codegenExprFuel fuel ctx e = .ok (instrs, out)) :
    ExprCodegenCorrect ctx st word value instrs out := by
  induction fuel using Nat.strong_induction_on generalizing ctx e st value instrs out with
  | h fuel ihFuel =>
    induction e generalizing ctx st value instrs out with
    | lit n =>
      simp only [ReloadableViewExpr] at hreload
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      simp only [Codegen.codegenExprFuel, Except.ok.injEq] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact codegenLit_result ctx st word hctx n hreload
    | «local» name =>
      simp only [ReloadableViewExpr] at hreload
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      simp only [Codegen.codegenExprFuel] at hgen
      rw [if_neg (by simpa using hreload.1)] at hgen
      obtain ⟨binding, source, hb, hs, hsourceValue, hfuel⟩ := hreload.2
      have hbCtx : ctx.lookupBinding name = some binding := by
        simpa [Ctx.lookupBinding] using hb
      rw [hbCtx] at hgen
      let depth := ctx.stackDepth - binding.absPos + 1
      cases ho : Ctx.dupOp depth with
      | ok op =>
          simp [depth, ho] at hgen
          obtain ⟨rfl, rfl⟩ := hgen
          exact codegenLocalDup_result ctx st word hctx name binding hbCtx depth rfl op ho
      | error err =>
          simp only [depth, ho, hs] at hgen
          cases fuel with
          | zero => contradiction
          | succ next =>
              simp only at hfuel
              exact ihFuel next (Nat.lt_succ_self next) ctx st hctx source hfuel
                (word.lookupLocal name) hsourceValue instrs out hgen
    | sload slot =>
      simp only [ReloadableViewExpr] at hreload
    | calldataWord offset =>
      simp only [ReloadableViewExpr] at hreload
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      simp only [Codegen.codegenExprFuel, Except.ok.injEq] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact codegenCalldata_result ctx st word hctx offset hreload
    | add a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok pair1 =>
            rcases pair1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok pair2 =>
              rcases pair2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by
                rw [hc1]
                exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]
                exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
              change ExprCodegenCorrect ctx st word (EvmYul.UInt256.add lhs rhs)
                (i1 ++ (i2 ++ [.op .ADD]))
                { c2 with stackDepth := c2.stackDepth - 1 }
              apply composeBinaryRaw ctx
                { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.add lhs rhs)
                i1 i2 [.op .ADD] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]
                simp
              · exact binarySuffix_add second st lhs rhs (by rw [hs2, hs1])
    | sub a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by
                rw [hc1]; exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]; exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.sub lhs rhs)
                i1 i2 [.op .SWAP1, .op .SUB] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_sub second st lhs rhs (by rw [hs2, hs1])
    | mul a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by rw [hc1]; exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]; exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              change ExprCodegenCorrect ctx st word (EvmYul.UInt256.mul lhs rhs)
                (i1 ++ (i2 ++ [.op .MUL])) _
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.mul lhs rhs)
                i1 i2 [.op .MUL] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_mul second st lhs rhs (by rw [hs2, hs1])
    | div a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by rw [hc1]; exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]; exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.div lhs rhs)
                i1 i2 [.op .SWAP1, .op .DIV] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_div second st lhs rhs (by rw [hs2, hs1])
    | gt a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by rw [hc1]; exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]; exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (boolWord (decide (rhs < lhs)))
                i1 i2 [.op .SWAP1, .op .GT] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_gt second st lhs rhs (by rw [hs2, hs1])
    | shr amount val ihAmount ihVal =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hvView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word amount with
      | none => simp [hva] at hvalue
      | some amountWord =>
        cases hvv : evalExprWord word val with
        | none => simp [hva, hvv] at hvalue
        | some valueWord =>
          simp [hva, hvv] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx amount with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgv : Codegen.codegenExprFuel fuel c1 val with
            | error err => simp [hga, hgv, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgv, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases ihAmount ctx st hctx haView amountWord hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by rw [hc1]; exact hctx1
              have hvView' : ReloadableViewExpr fuel c1.locals word val := by
                rw [hc1]; exact hvView
              rcases ihVal c1 first hctx1' hvView' valueWord hvv i2 c2 hgv with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.shiftRight valueWord amountWord)
                i1 i2 [.op .SWAP1, .op .SHR] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_shr second st amountWord valueWord (by rw [hs2, hs1])
    | xor a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
        cases hvb : evalExprWord word b with
        | none => simp [hva, hvb] at hvalue
        | some rhs =>
          simp [hva, hvb] at hvalue
          subst value
          simp only [Codegen.codegenExprFuel] at hgen
          cases hga : Codegen.codegenExprFuel fuel ctx a with
          | error err => simp [hga, Bind.bind, Except.bind] at hgen
          | ok p1 =>
            rcases p1 with ⟨i1, c1⟩
            cases hgb : Codegen.codegenExprFuel fuel c1 b with
            | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
            | ok p2 =>
              rcases p2 with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases iha ctx st hctx haView lhs hva i1 c1 hga with
                ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
              have hctx1' : ContextAgrees c1 first word := by rw [hc1]; exact hctx1
              have hbView' : ReloadableViewExpr fuel c1.locals word b := by
                rw [hc1]; exact hbView
              rcases ihb c1 first hctx1' hbView' rhs hvb i2 c2 hgb with
                ⟨hc2, second, hr2, hs2, hp2, hf2, _, he2⟩
              change ExprCodegenCorrect ctx st word (EvmYul.UInt256.xor lhs rhs)
                (i1 ++ (i2 ++ [.op .XOR])) _
              apply composeBinaryRaw ctx { c2 with stackDepth := c2.stackDepth - 1 }
                st first second word (EvmYul.UInt256.xor lhs rhs)
                i1 i2 [.op .XOR] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
              · rw [hc2, hc1]; simp
              · exact binarySuffix_xor second st lhs rhs (by rw [hs2, hs1])
    | mapSlot | mapSlot2 | dynSload | lt | eq | isZero =>
      simp [ReloadableViewExpr] at hreload

theorem codegenLocal_result (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (name : Lsc.Ident) (hname : name ≠ "caller")
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.expr ctx (.local name) = .ok (instrs, out)) :
    ExprCodegenCorrect ctx st word (word.lookupLocal name) instrs out := by
  simp only [Codegen.expr, Codegen.codegenExpr] at hgen
  rw [if_neg (by simpa using hname)] at hgen
  cases hb : ctx.lookupBinding name with
  | none => simp [hb] at hgen
  | some binding =>
      let depth := ctx.stackDepth - binding.absPos + 1
      cases ho : Ctx.dupOp depth with
      | ok op =>
          simp [hb, depth, ho] at hgen
          obtain ⟨rfl, rfl⟩ := hgen
          exact codegenLocalDup_result ctx st word hctx name binding hb depth rfl op ho
      | error depthError =>
          cases hs : binding.src with
          | none => simp [hb, depth, ho, hs] at hgen
          | some source =>
              obtain ⟨_, hvalue⟩ := hctx.reloads name binding source hb hs
              have hsource := hctx.reloadPlans name binding source hb hs
              simp [hb, depth, ho, hs, Codegen.codegenExprFuel] at hgen
              exact codegenExprFuel_correct ctx.locals.length ctx st word hctx source
                hsource (word.lookupLocal name) hvalue instrs out hgen

theorem codegenExpr_correct (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (e : Expr) (he : ViewExpr e)
    (value : EWord) (hvalue : evalExprWord word e = some value)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.expr ctx e = .ok (instrs, out)) :
    ExprCodegenCorrect ctx st word value instrs out := by
  induction e generalizing ctx st value instrs out with
  | lit n =>
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      simp only [Codegen.expr, Codegen.codegenExpr, Except.ok.injEq] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact codegenLit_result ctx st word hctx n he
  | «local» name =>
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      exact codegenLocal_result ctx st word hctx name he instrs out hgen
  | sload slot => contradiction
  | calldataWord offset =>
      simp only [evalExprWord, Option.some.injEq] at hvalue
      subst value
      simp only [Codegen.expr, Codegen.codegenExpr, Except.ok.injEq] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact codegenCalldata_result ctx st word hctx offset he
  | add a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      have hca := iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga)
                      rcases hca with ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      have hcb := ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb)
                      rcases hcb with ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      have hsuffix := binarySuffix_add second st lhs rhs (by
                        rw [hs2, hs1])
                      change ExprCodegenCorrect ctx st word (EvmYul.UInt256.add lhs rhs)
                        (i1 ++ (i2 ++ [.op .ADD]))
                        { c2 with stackDepth := c2.stackDepth - 1 }
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (EvmYul.UInt256.add lhs rhs)
                        i1 i2 [.op .ADD] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact hsuffix
  | sub a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (EvmYul.UInt256.sub lhs rhs)
                        i1 i2 [.op .SWAP1, .op .SUB] hctx
                        hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_sub second st lhs rhs (by rw [hs2, hs1])
  | mul a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      change ExprCodegenCorrect ctx st word (EvmYul.UInt256.mul lhs rhs)
                        (i1 ++ (i2 ++ [.op .MUL]))
                        { c2 with stackDepth := c2.stackDepth - 1 }
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (EvmYul.UInt256.mul lhs rhs)
                        i1 i2 [.op .MUL] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_mul second st lhs rhs (by rw [hs2, hs1])
  | div a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (EvmYul.UInt256.div lhs rhs)
                        i1 i2 [.op .SWAP1, .op .DIV] hctx
                        hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_div second st lhs rhs (by rw [hs2, hs1])
  | gt a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (boolWord (decide (rhs < lhs)))
                        i1 i2 [.op .SWAP1, .op .GT] hctx
                        hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_gt second st lhs rhs (by rw [hs2, hs1])
  | shr amount val ihAmount ihVal =>
      rcases he with ⟨haView, hvView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word amount with
      | none => simp [hva] at hvalue
      | some amountWord =>
          cases hvv : evalExprWord word val with
          | none => simp [hva, hvv] at hvalue
          | some valueWord =>
              simp [hva, hvv] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx amount with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgv : Codegen.codegenExpr c1 val with
                  | error err => simp [hga, hgv, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgv, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases ihAmount ctx st hctx haView amountWord hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihVal c1 first hctx1' hvView valueWord hvv i2 c2 (by
                        simpa [Codegen.expr] using hgv) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word
                        (EvmYul.UInt256.shiftRight valueWord amountWord)
                        i1 i2 [.op .SWAP1, .op .SHR] hctx
                        hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_shr second st amountWord valueWord
                          (by rw [hs2, hs1])
  | xor a b iha ihb =>
      rcases he with ⟨haView, hbView⟩
      simp only [evalExprWord] at hvalue
      cases hva : evalExprWord word a with
      | none => simp [hva] at hvalue
      | some lhs =>
          cases hvb : evalExprWord word b with
          | none => simp [hva, hvb] at hvalue
          | some rhs =>
              simp [hva, hvb] at hvalue
              subst value
              simp only [Codegen.expr, Codegen.codegenExpr] at hgen
              cases hga : Codegen.codegenExpr ctx a with
              | error err => simp [hga, Bind.bind, Except.bind] at hgen
              | ok pair1 =>
                  rcases pair1 with ⟨i1, c1⟩
                  cases hgb : Codegen.codegenExpr c1 b with
                  | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
                  | ok pair2 =>
                      rcases pair2 with ⟨i2, c2⟩
                      simp [hga, hgb, Bind.bind, Except.bind] at hgen
                      obtain ⟨rfl, rfl⟩ := hgen
                      rcases iha ctx st hctx haView lhs hva i1 c1 (by
                        simpa [Codegen.expr] using hga) with
                        ⟨hc1, first, hr1, hs1, hp1, hf1, hctx1, he1⟩
                      have hctx1' : ContextAgrees c1 first word := by
                        rw [hc1]
                        exact hctx1
                      rcases ihb c1 first hctx1' hbView rhs hvb i2 c2 (by
                        simpa [Codegen.expr] using hgb) with
                        ⟨hc2, second, hr2, hs2, hp2, hf2, hctx2, he2⟩
                      change ExprCodegenCorrect ctx st word (EvmYul.UInt256.xor lhs rhs)
                        (i1 ++ (i2 ++ [.op .XOR]))
                        { c2 with stackDepth := c2.stackDepth - 1 }
                      apply composeBinaryRaw ctx
                        { c2 with stackDepth := c2.stackDepth - 1 }
                        st first second word (EvmYul.UInt256.xor lhs rhs)
                        i1 i2 [.op .XOR] hctx hr1 hp1 hf1 he1 hr2 hp2 hf2 he2
                      · rw [hc2, hc1]
                        simp
                      · exact binarySuffix_xor second st lhs rhs (by rw [hs2, hs1])
  | mapSlot _ _ _ | mapSlot2 _ _ _ _ _ | dynSload _ _ | lt _ _ _ _
  | eq _ _ _ _ | isZero _ _ =>
      contradiction

/-- The generated one-word return epilogue, executed only by EvmYul, returns the exact canonical
32-byte serialization. -/
theorem runView_returnEpilogue (st : EVM.State) (value : EWord) (tail : List EWord)
    (hmemory : st.memory = ByteArray.empty) :
    ∃ final,
      runView ReturnEpilogue { st with stack := value :: tail } = .ok final ∧
      final.stack = tail ∧ final.H_return = value.toByteArray := by
  let b0 := { st with stack := value :: tail }
  let c1 := checkedState b0 .PUSH0
  let k1 := checkedCost b0 .PUSH0
  let s1 : EVM.State := {
    c1 with
    stack := .ofNat 0 :: value :: tail,
    pc := c1.pc + .ofNat 1,
    gasAvailable := c1.gasAvailable - .ofNat k1,
    execLength := c1.execLength + 1 }
  let c2 := checkedState s1 .MSTORE
  let k2 := checkedCost s1 .MSTORE
  let s2 : EVM.State := {
    c2 with
    stack := tail,
    toMachineState := EvmYul.MachineState.mstore
      { c2.toMachineState with gasAvailable := c2.gasAvailable - .ofNat k2 }
      (.ofNat 0) value,
    pc := c2.pc + .ofNat 1,
    execLength := c2.execLength + 1 }
  let c3 := checkedState s2 .PUSH1
  let k3 := checkedCost s2 .PUSH1
  let s3 : EVM.State := {
    c3 with
    stack := .ofNat 32 :: tail,
    pc := c3.pc + .ofNat 2,
    gasAvailable := c3.gasAvailable - .ofNat k3,
    execLength := c3.execLength + 1 }
  let c4 := checkedState s3 .PUSH0
  let k4 := checkedCost s3 .PUSH0
  let s4 : EVM.State := {
    c4 with
    stack := .ofNat 0 :: .ofNat 32 :: tail,
    pc := c4.pc + .ofNat 1,
    gasAvailable := c4.gasAvailable - .ofNat k4,
    execLength := c4.execLength + 1 }
  let c5 := checkedState s4 .RETURN
  let k5 := checkedCost s4 .RETURN
  let s5 : EVM.State := {
    c5 with
    stack := tail,
    toMachineState := EvmYul.MachineState.evmReturn
      { c5.toMachineState with gasAvailable := c5.gasAvailable - .ofNat k5 }
      (.ofNat 0) (.ofNat 32),
    pc := c5.pc + .ofNat 1,
    execLength := c5.execLength + 1 }
  have h1 : EVM.step 1 k1 (some (.PUSH0, none)) c1 = .ok s1 := by
    simpa [s1, c1, b0] using evmStep_push0 0 k1 c1
  have h2 : EVM.step 1 k2 (some (.MSTORE, none)) c2 = .ok s2 := by
    have hc2stack : c2.stack = .ofNat 0 :: value :: tail := by rfl
    rw [state_setStack c2 _ hc2stack]
    simpa [s2] using evmStep_mstore 0 k2 c2 (.ofNat 0) value tail
  have h3 : EVM.step 1 k3
      (some (.PUSH1, some (.ofNat 32, 1))) c3 = .ok s3 := by
    simpa [s3] using evmStep_push 0 k3 c3 .PUSH1 (.ofNat 32) 1 (by decide)
  have h4 : EVM.step 1 k4 (some (.PUSH0, none)) c4 = .ok s4 := by
    simpa [s4] using evmStep_push0 0 k4 c4
  have h5 : EVM.step 1 k5 (some (.RETURN, none)) c5 = .ok s5 := by
    have hc5stack : c5.stack = .ofNat 0 :: .ofNat 32 :: tail := by rfl
    rw [state_setStack c5 _ hc5stack]
    simpa [s5] using evmStep_return 0 k5 c5 (.ofNat 0) (.ofNat 32) tail
  refine ⟨s5, ?_, by simp [s5], ?_⟩
  · simp only [ReturnEpilogue, runView, decodedPlainInstr, pushWidth, pushOp]
    change (do
      let a ← EVM.step 1 k1 (some (.PUSH0, none)) c1
      let b ← EVM.step 1 k2 (some (.MSTORE, none)) (checkedState a .MSTORE)
      let c ← EVM.step 1 k3 (some (.PUSH1, some (.ofNat 32, 1)))
        (checkedState b .PUSH1)
      let d ← EVM.step 1 k4 (some (.PUSH0, none)) (checkedState c .PUSH0)
      let e ← EVM.step 1 k5 (some (.RETURN, none)) (checkedState d .RETURN)
      Except.ok e) = .ok s5
    rw [h1]
    simp only [Bind.bind, Except.bind]
    rw [h2]
    simp only [Bind.bind, Except.bind]
    rw [h3]
    simp only [Bind.bind, Except.bind]
    rw [h4]
    simp only [Bind.bind, Except.bind]
    rw [h5]
  · simp only [s5, c5, checkedState, s4, c4, s3, c3, s2, c2, s1, c1, b0,
      EvmYul.MachineState.evmReturn]
    simp only [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
      EvmYul.writeBytes, EvmYul.UInt256.toNat, hmemory]
    exact write_readWithPadding_32_empty value.toByteArray
      (uint256_toByteArray_size value)

def PureViewInstr : Instr → Prop
  | .push n => pushWidth n ≤ 32
  | .op op =>
      op = .ADD ∨ op = .SUB ∨ op = .MUL ∨ op = .DIV ∨ op = .GT ∨ op = .SHR ∨
      op = .XOR ∨ op = .SWAP1 ∨ op = .CALLDATALOAD ∨ op = .MSTORE ∨
      op = .DUP1 ∨ op = .DUP2 ∨ op = .DUP3 ∨ op = .DUP4 ∨ op = .DUP5 ∨
      op = .DUP6 ∨ op = .DUP7 ∨ op = .DUP8 ∨ op = .DUP9 ∨ op = .DUP10 ∨
      op = .DUP11 ∨ op = .DUP12 ∨ op = .DUP13 ∨ op = .DUP14 ∨ op = .DUP15 ∨
      op = .DUP16
  | _ => False

def PureViewInstrs (instrs : List Instr) : Prop :=
  ∀ instr ∈ instrs, PureViewInstr instr

theorem PureViewInstrs.append {first rest : List Instr}
    (hfirst : PureViewInstrs first) (hrest : PureViewInstrs rest) :
    PureViewInstrs (first ++ rest) := by
  intro instr hmem
  exact (List.mem_append.mp hmem).elim (hfirst instr) (hrest instr)

private theorem pureView_dupOp (depth : Nat) (op : Operation .EVM)
    (hdup : Ctx.dupOp depth = .ok op) :
    PureViewInstr (.op op) := by
  have hb := dupOp_success_bounds depth op hdup
  rcases hb with ⟨hlo, hhi⟩
  interval_cases depth <;> simp [Ctx.dupOp] at hdup <;> subst op <;>
    simp [PureViewInstr]

/-- Fuel-indexed purity for deep expression rebuilding. -/
theorem codegenExprFuel_pure (fuel : Nat) (ctx : Ctx) (word : WordState) (e : Expr)
    (hreload : ReloadableViewExpr fuel ctx.locals word e)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.codegenExprFuel fuel ctx e = .ok (instrs, out)) :
    PureViewInstrs instrs ∧ out.locals = ctx.locals := by
  induction fuel using Nat.strong_induction_on generalizing ctx e instrs out with
  | h fuel ihFuel =>
    induction e generalizing ctx instrs out with
    | lit n =>
      simp only [ReloadableViewExpr] at hreload
      simp [Codegen.codegenExprFuel] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact ⟨by simpa [PureViewInstrs, PureViewInstr] using hreload, rfl⟩
    | calldataWord offset =>
      simp only [ReloadableViewExpr] at hreload
      simp [Codegen.codegenExprFuel] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact ⟨by simpa [PureViewInstrs, PureViewInstr] using hreload, rfl⟩
    | «local» name =>
      simp only [ReloadableViewExpr] at hreload
      simp only [Codegen.codegenExprFuel] at hgen
      rw [if_neg (by simpa using hreload.1)] at hgen
      obtain ⟨binding, source, hb, hs, _, hsource⟩ := hreload.2
      have hbCtx : ctx.lookupBinding name = some binding := by
        simpa [Ctx.lookupBinding] using hb
      rw [hbCtx] at hgen
      let depth := ctx.stackDepth - binding.absPos + 1
      cases hd : Ctx.dupOp depth with
      | ok op =>
        simp [depth, hd] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        exact ⟨by
          intro instr hmem
          simp only [Codegen.emitOp, List.mem_singleton] at hmem
          subst instr
          exact pureView_dupOp depth op hd, rfl⟩
      | error err =>
        simp only [depth, hd, hs] at hgen
        cases fuel with
        | zero => contradiction
        | succ next =>
          exact ihFuel next (Nat.lt_succ_self next) ctx source hsource instrs out hgen
    | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
    | gt a b iha ihb | shr a b iha ihb | xor a b iha ihb =>
      simp only [ReloadableViewExpr] at hreload
      rcases hreload with ⟨ha, hb⟩
      simp only [Codegen.codegenExprFuel] at hgen
      cases hga : Codegen.codegenExprFuel fuel ctx a with
      | error err => simp [hga, Bind.bind, Except.bind] at hgen
      | ok first =>
        rcases first with ⟨i1, c1⟩
        cases hgb : Codegen.codegenExprFuel fuel c1 b with
        | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
        | ok second =>
          rcases second with ⟨i2, c2⟩
          simp [hga, hgb, Bind.bind, Except.bind] at hgen
          obtain ⟨rfl, rfl⟩ := hgen
          obtain ⟨hp1, hc1⟩ := iha ctx ha i1 c1 hga
          have hb' : ReloadableViewExpr fuel c1.locals word b := by
            rw [hc1]
            exact hb
          obtain ⟨hp2, hc2⟩ := ihb c1 hb' i2 c2 hgb
          constructor
          · apply PureViewInstrs.append hp1
            apply PureViewInstrs.append hp2
            intro instr hmem
            simp only [Codegen.emitOp, List.mem_cons, List.mem_singleton] at hmem
            aesop (add simp [PureViewInstr])
          · simpa [hc2, hc1]
    | sload | mapSlot | mapSlot2 | dynSload | lt | eq | isZero =>
      simp [ReloadableViewExpr] at hreload

def ReloadableSources (ctx : Ctx) (word : WordState) : Prop :=
  ∀ name binding source,
    ctx.lookupBinding name = some binding →
    binding.src = some source →
    ReloadableViewExpr ctx.locals.length ctx.locals word source

theorem reloadableSources_forFunction (ctx : Ctx) (word : WordState) (name : Lsc.Ident) :
    ReloadableSources (Ctx.forFunction ctx name) word := by
  intro localName binding source h
  simp [Ctx.forFunction, Ctx.lookupBinding] at h

/-- View-expression compilation emits only fuel-independent view instructions and preserves the
local-binding table. -/
theorem codegenExpr_pure
    (ctx : Ctx) (word : WordState) (e : Expr) (hview : ViewExpr e)
    (hreloads : ReloadableSources ctx word)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.expr ctx e = .ok (instrs, out)) :
    PureViewInstrs instrs ∧ out.locals = ctx.locals := by
  induction e generalizing ctx instrs out with
  | lit n =>
      simp only [ViewExpr] at hview
      simp [Codegen.expr, Codegen.codegenExpr] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact ⟨by simpa [PureViewInstrs, PureViewInstr], rfl⟩
  | calldataWord offset =>
      simp only [ViewExpr] at hview
      simp [Codegen.expr, Codegen.codegenExpr] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact ⟨by simpa [PureViewInstrs, PureViewInstr] using hview, rfl⟩
  | «local» name =>
      simp only [ViewExpr] at hview
      simp only [Codegen.expr, Codegen.codegenExpr] at hgen
      rw [if_neg (by simpa using hview)] at hgen
      cases hb : ctx.lookupBinding name with
      | none => simp [hb] at hgen
      | some binding =>
          simp only [hb] at hgen
          cases hd : Ctx.dupOp (ctx.stackDepth - binding.absPos + 1) with
          | ok op =>
              rw [hd] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              exact ⟨by
                intro instr hmem
                simp only [Codegen.emitOp, List.mem_singleton] at hmem
                subst instr
                exact pureView_dupOp (ctx.stackDepth - binding.absPos + 1) op hd, rfl⟩
          | error err =>
              cases hs : binding.src with
              | none => simp [hd, hs] at hgen
              | some source =>
                  have hsource := hreloads name binding source hb hs
                  simp [hd, hs, Codegen.codegenExprFuel] at hgen
                  exact codegenExprFuel_pure ctx.locals.length ctx word source hsource
                    instrs out hgen
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
  | gt a b iha ihb | shr a b iha ihb | xor a b iha ihb =>
      simp only [ViewExpr] at hview
      rcases hview with ⟨ha, hb⟩
      simp only [Codegen.expr, Codegen.codegenExpr] at hgen
      cases hga : Codegen.codegenExpr ctx a with
      | error err => simp [hga, Bind.bind, Except.bind] at hgen
      | ok first =>
          rcases first with ⟨i1, c1⟩
          cases hgb : Codegen.codegenExpr c1 b with
          | error err => simp [hga, hgb, Bind.bind, Except.bind] at hgen
          | ok second =>
              rcases second with ⟨i2, c2⟩
              simp [hga, hgb, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              obtain ⟨hp1, hc1⟩ := iha ctx ha hreloads i1 c1
                (by simpa [Codegen.expr] using hga)
              have hr1 : ReloadableSources c1 word := by
                intro name binding source hlookup hsource
                have hold : ctx.lookupBinding name = some binding := by
                  simpa [Ctx.lookupBinding, hc1] using hlookup
                have hp := hreloads name binding source hold hsource
                simpa [hc1] using hp
              obtain ⟨hp2, hc2⟩ := ihb c1 hb hr1 i2 c2
                (by simpa [Codegen.expr] using hgb)
              constructor
              · apply PureViewInstrs.append hp1
                apply PureViewInstrs.append hp2
                intro instr hmem
                simp only [Codegen.emitOp, List.mem_cons, List.mem_singleton] at hmem
                aesop (add simp [PureViewInstr])
              · simpa [hc2, hc1]
  | sload slot | mapSlot base key | mapSlot2 base key₁ key₂ | dynSload slot
  | lt a b | eq a b | isZero a =>
      simp [ViewExpr] at hview

theorem pureViewStep_fuel (instr : Instr) (h : PureViewInstr instr)
    (fuel cost : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (decodedPlainInstr instr)) st =
      EVM.step 1 cost (some (decodedPlainInstr instr)) st := by
  cases instr with
  | push n =>
      exact (evmStep_decodedPush n fuel cost h st).trans
        (evmStep_decodedPush n 0 cost h st).symm
  | push32 n => contradiction
  | op op =>
      simp only [decodedPlainInstr]
      simp only [PureViewInstr] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        simp only [EVM.step, Bind.bind, Except.bind] <;> rfl
  | pushLabel _ | jump _ | jumpi _ | jumpDest _ => contradiction

theorem pureView_xHaltOutput_none (instr : Instr) (h : PureViewInstr instr)
    (st : MachineState) :
    xHaltOutput st (decodedPlainInstr instr).1 = none := by
  cases instr with
  | push n =>
      simp only [PureViewInstr] at h
      generalize heq : pushWidth n = width
      have hw : width ≤ 32 := by simpa [heq] using h
      interval_cases width <;> simp [xHaltOutput, decodedPlainInstr, heq, pushOp]
  | push32 n => contradiction
  | op op =>
      simp only [PureViewInstr] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> rfl
  | pushLabel _ | jump _ | jumpi _ | jumpDest _ => contradiction

/-- Computable safety/alignment invariant for a stream ending in the generated `RETURN`.
It contains no caller-supplied step equation: each successor is obtained by reducing EvmYul's
actual `EVM.step`. -/
def XReady (validJumps : Array EWord) (code : ByteArray) :
    Nat → List Instr → EVM.State → Prop
  | pc, [.op .RETURN], st =>
      st.executionEnv.code = code ∧ st.pc = .ofNat pc ∧
      XPrecheckSafe validJumps .RETURN st
  | pc, instr :: rest, st =>
      PureViewInstr instr ∧ instr ≠ .op .RETURN ∧
      st.executionEnv.code = code ∧ st.pc = .ofNat pc ∧
      XPrecheckSafe validJumps (decodedPlainInstr instr).1 st ∧
      match EVM.step 1 (checkedCost st (decodedPlainInstr instr).1)
          (some (decodedPlainInstr instr))
          (checkedState st (decodedPlainInstr instr).1) with
      | .error _ => False
      | .ok next =>
          xHaltOutput next.toMachineState (decodedPlainInstr instr).1 = none ∧
          XReady validJumps code (pc + instrByteSize [] instr) rest next
  | _, _, _ => False

theorem X_eq_success_of_runView (validJumps : Array EWord) (code : ByteArray)
    (pc : Nat) (instrs : List Instr) (st final : EVM.State)
    (hdecode : DecoderAlong code pc instrs)
    (hready : XReady validJumps code pc instrs st)
    (hrun : runView instrs st = .ok final) :
    EVM.X (instrs.length + 1) validJumps st =
      .ok (.success final final.H_return) := by
  induction instrs generalizing pc st with
  | nil => simp [XReady] at hready
  | cons instr rest ih =>
      cases hdecode with
      | cons _ _ _ hdecoded hdecodeRest =>
          cases rest with
          | nil =>
              have hi : instr = .op .RETURN := by
                by_contra hne
                simp [XReady, hne] at hready
                split at hready <;> simp_all
              subst instr
              simp only [XReady] at hready
              simp only [runView, decodedPlainInstr] at hrun
              cases hs : EVM.step 1 (checkedCost st .RETURN) (some (.RETURN, none))
                  (checkedState st .RETURN) with
              | error err =>
                  rw [hs] at hrun
                  contradiction
              | ok next =>
                  rw [hs] at hrun
                  injection hrun with heq
                  subst final
                  apply X_return_of_precheck 1 validJumps st (checkedState st .RETURN)
                    next (checkedCost st .RETURN)
                  · simpa [hready.1, hready.2.1, decodedPlainInstr] using hdecoded
                  · simpa [checkedState, checkedCost] using
                      xPrecheck_ok_of_safe validJumps .RETURN st hready.2.2
                  · exact hs
          | cons nextInstr tail =>
              simp only [XReady] at hready
              rcases hready with
                ⟨hpure, hnotRet, hcode, hpc, hsafe, hrunStep⟩
              cases hs : EVM.step 1 (checkedCost st (decodedPlainInstr instr).1)
                  (some (decodedPlainInstr instr))
                  (checkedState st (decodedPlainInstr instr).1) with
              | error err =>
                  rw [hs] at hrunStep
                  contradiction
              | ok next =>
                  rw [hs] at hrunStep
                  rcases hrunStep with ⟨hhalt, hreadyRest⟩
                  simp only [runView] at hrun
                  rw [hs] at hrun
                  change runView (nextInstr :: tail) next = .ok final at hrun
                  change EVM.X (((nextInstr :: tail).length + 1) + 1) validJumps st =
                    .ok (.success final final.H_return)
                  rw [X_step_of_precheck ((nextInstr :: tail).length + 1) validJumps st
                    (checkedState st (decodedPlainInstr instr).1) next
                    (decodedPlainInstr instr) (checkedCost st (decodedPlainInstr instr).1)
                    (by simpa [hcode, hpc] using hdecoded)
                    (by simpa [checkedState, checkedCost] using
                      xPrecheck_ok_of_safe validJumps (decodedPlainInstr instr).1 st hsafe)
                    (by simpa [Nat.add_comm] using
                      (pureViewStep_fuel instr hpure (nextInstr :: tail).length
                        (checkedCost st (decodedPlainInstr instr).1)
                        (checkedState st (decodedPlainInstr instr).1)).trans hs)
                    hhalt]
                  exact ih (pc + instrByteSize [] instr) next
                    hdecodeRest hreadyRest hrun

theorem X_encode_eq_success_of_runView (validJumps : Array EWord)
    (instrs : List Instr) (code : ByteArray)
    (hencodable : EncodablePlainInstrs instrs)
    (hencode : encode instrs = .ok code) (hlimit : code.size + 33 < 2^64)
    (st final : EVM.State) (hready : XReady validJumps code 0 instrs st)
    (hrun : runView instrs st = .ok final) :
    EVM.X (instrs.length + 1) validJumps st =
      .ok (.success final final.H_return) := by
  apply X_eq_success_of_runView validJumps code 0 instrs st final
  · exact decoderAlong_encode instrs hencodable code hencode hlimit
  · exact hready
  · exact hrun

theorem X_encode_returns_word (validJumps : Array EWord)
    (instrs : List Instr) (code : ByteArray)
    (hencodable : EncodablePlainInstrs instrs)
    (hencode : encode instrs = .ok code) (hlimit : code.size + 33 < 2^64)
    (st final : EVM.State) (value : EWord)
    (hready : XReady validJumps code 0 instrs st)
    (hrun : runView instrs st = .ok final)
    (hreturn : final.H_return = value.toByteArray) :
    EVM.X (instrs.length + 1) validJumps st =
      .ok (.success final value.toByteArray) := by
  rw [← hreturn]
  exact X_encode_eq_success_of_runView validJumps instrs code hencodable
    hencode hlimit st final hready hrun

theorem returnEpilogue_encodable : EncodablePlainInstrs ReturnEpilogue := by
  intro instr hmem
  simp only [ReturnEpilogue, List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h
  · exact ⟨by simp [PlainInstr], by decide⟩
  · exact ⟨by simp [PlainInstr, Operation.isPush], trivial⟩
  · exact ⟨by simp [PlainInstr], by decide⟩
  · exact ⟨by simp [PlainInstr], by decide⟩
  · exact ⟨by simp [PlainInstr, Operation.isPush], trivial⟩
  · contradiction

/-- Direct EvmYul execution correctness for a generated pure-view return statement. -/
theorem codegenRet_runView_correct (ctx : Ctx) (st : EVM.State) (word : WordState)
    (hctx : ContextAgrees ctx st word) (hmemory : st.memory = ByteArray.empty)
    (e : Expr) (he : ViewExpr e) (value : EWord)
    (hvalue : evalExprWord word e = some value)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx (.ret e) = .ok (instrs, out)) :
    ∃ final,
      runView instrs st = .ok final ∧
      final.H_return = value.toByteArray ∧
      EncodablePlainInstrs instrs := by
  simp only [Codegen.stmt, Codegen.codegenStmt] at hgen
  cases hge : Codegen.codegenExpr ctx e with
  | error err => simp [hge, Bind.bind, Except.bind] at hgen
  | ok pair =>
      rcases pair with ⟨exprInstrs, c1⟩
      simp [hge, Bind.bind, Except.bind] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      rcases codegenExpr_correct ctx st word hctx e he value hvalue
          exprInstrs c1 (by simpa [Codegen.expr] using hge) with
        ⟨hc1, exprFinal, hrunExpr, hstack, hpc, hframe, hctxFinal, hencExpr⟩
      have hmemoryFinal : exprFinal.memory = ByteArray.empty := by
        rw [hframe.memory, hmemory]
      have hstate : exprFinal =
          { exprFinal with stack := value :: st.stack } :=
        state_setStack exprFinal _ hstack
      rcases runView_returnEpilogue exprFinal value st.stack hmemoryFinal with
        ⟨final, hrunRet, htail, hreturn⟩
      rw [← hstate] at hrunRet
      refine ⟨final, ?_, hreturn,
        EncodablePlainInstrs.append hencExpr returnEpilogue_encodable⟩
      rw [runView_append, hrunExpr]
      exact hrunRet

inductive ViewProgram : WordState → Stmt → EWord → Prop
  | ret (word : WordState) (e : Expr) (value : EWord)
      (hview : ViewExpr e) (heval : evalExprWord word e = some value) :
      ViewProgram word (.ret e) value
  | letSeq (word : WordState) (name : Lsc.Ident) (e : Expr) (bound : EWord)
      (rest : Stmt) (value : EWord)
      (hview : ViewExpr e) (heval : evalExprWord word e = some bound)
      (hrest : ViewProgram (word.setLocal name bound) rest value) :
      ViewProgram word (.seq (.letBind name e) rest) value

/-- The extra, context-indexed obligations needed when a let source is retained for later deep
reload.  They state source-value stability and lift every older reload plan across the fresh bind. -/
structure BindReloadSafe (ctx : Ctx) (word : WordState)
    (name : Lsc.Ident) (bound : EWord) (source : Expr) : Prop where
  sourceStable :
    evalExprWord (word.setLocal name bound) source = evalExprWord word source
  sourceValue :
    evalExprWord (word.setLocal name bound) source = some bound
  oldValues : ∀ queried binding oldSource,
    ctx.lookupBinding queried = some binding →
    binding.src = some oldSource →
    evalExprWord (word.setLocal name bound) oldSource = evalExprWord word oldSource
  sourcePlan :
    ReloadableViewExpr (ctx.locals.length + 1)
      ((name, { absPos := ctx.stackDepth, src := some source }) :: ctx.locals)
      (word.setLocal name bound) source
  oldPlans : ∀ queried binding oldSource,
    ctx.lookupBinding queried = some binding →
    binding.src = some oldSource →
    ReloadableViewExpr ctx.locals.length ctx.locals word oldSource →
    ReloadableViewExpr (ctx.locals.length + 1)
      ((name, { absPos := ctx.stackDepth, src := some source }) :: ctx.locals)
      (word.setLocal name bound) oldSource

/-- Reload-plan threading for a `ViewProgram`.  Expression compilation preserves `locals`, so its
only context transition before binding is the one-word stack-depth increment recorded here. -/
inductive ViewProgramReloadSafe : Ctx → WordState → Stmt → Prop
  | ret (ctx word e) : ViewProgramReloadSafe ctx word (.ret e)
  | letSeq (ctx word name e bound rest)
      (hsafe : BindReloadSafe { ctx with stackDepth := ctx.stackDepth + 1 }
        word name bound e)
      (hrest : ViewProgramReloadSafe
        (({ ctx with stackDepth := ctx.stackDepth + 1 }).bindLocal name (some e))
        (word.setLocal name bound) rest) :
      ViewProgramReloadSafe ctx word (.seq (.letBind name e) rest)

/-- A generated `ViewProgram` body contains only pure-view instructions; callers need not provide
this compiler invariant separately. -/
theorem codegenViewProgram_pure
    {word : WordState} {program : Stmt} {value : EWord}
    (hprogram : ViewProgram word program value)
    (ctx : Ctx) (hreloadSafe : ViewProgramReloadSafe ctx word program)
    (st : EVM.State) (hctx : ContextAgrees ctx st word)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx program = .ok (instrs, out)) :
    ∃ pre, instrs = pre ++ [.op .RETURN] ∧ PureViewInstrs pre := by
  induction hreloadSafe generalizing value st instrs out with
  | ret ctx word e =>
    cases hprogram with
    | ret _ _ value hview heval =>
      simp only [Codegen.stmt, Codegen.codegenStmt] at hgen
      cases hge : Codegen.codegenExpr ctx e with
      | error err => simp [hge, Bind.bind, Except.bind] at hgen
      | ok pair =>
          rcases pair with ⟨exprInstrs, exprCtx⟩
          simp [hge, Bind.bind, Except.bind] at hgen
          obtain ⟨rfl, rfl⟩ := hgen
          obtain ⟨hpure, _⟩ := codegenExpr_pure ctx word e hview hctx.reloadPlans
            exprInstrs exprCtx (by simpa [Codegen.expr] using hge)
          refine ⟨exprInstrs ++ [.push 0, .op .MSTORE, .push 32, .push 0], ?_, ?_⟩
          · simp [ReturnEpilogue]
          · apply PureViewInstrs.append hpure
            intro instr hmem
            have hzero : pushWidth 0 ≤ 32 := by decide
            have hthirtyTwo : pushWidth 32 ≤ 32 := by decide
            simp only [List.mem_cons, List.mem_singleton] at hmem
            aesop (add simp [PureViewInstr])
  | letSeq ctx word name e bound rest hsafe hsafeRest ih =>
    cases hprogram with
    | letSeq _ _ _ bound' _ value hview heval hrest =>
      have hbound : bound = bound' := by
        apply Option.some.inj
        rw [← hsafe.sourceValue, hsafe.sourceStable, heval]
      subst bound'
      simp only [Codegen.stmt, Codegen.codegenStmt] at hgen
      cases hgExpr : Codegen.codegenExpr ctx e with
      | error err => simp [hgExpr, Bind.bind, Except.bind] at hgen
      | ok exprPair =>
          rcases exprPair with ⟨exprInstrs, exprCtx⟩
          cases hgRest : Codegen.codegenStmt (exprCtx.bindLocal name (some e)) rest with
          | error err => simp [hgExpr, hgRest, Bind.bind, Except.bind] at hgen
          | ok restPair =>
              rcases restPair with ⟨restInstrs, restCtx⟩
              simp [hgExpr, hgRest, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              obtain ⟨hpure, _⟩ := codegenExpr_pure ctx word e hview hctx.reloadPlans
                exprInstrs exprCtx (by simpa [Codegen.expr] using hgExpr)
              rcases codegenExpr_correct ctx st word hctx e hview bound heval
                  exprInstrs exprCtx (by simpa [Codegen.expr] using hgExpr) with
                ⟨hExprCtx, exprFinal, _, hstack, _, _, hctxExpr, _⟩
              subst exprCtx
              have hctxBound :
                  ContextAgrees
                    (({ ctx with stackDepth := ctx.stackDepth + 1 }).bindLocal name (some e))
                    exprFinal
                    (word.setLocal name bound) := by
                apply hctxExpr.bindLocal name bound (some e) st.stack hstack
                · intro source hsource
                  simp only [Option.some.injEq] at hsource
                  subst source
                  exact ⟨hview, hsafe.sourceValue⟩
                · exact hsafe.oldValues
                · intro source hsource
                  simp only [Option.some.injEq] at hsource
                  subst source
                  exact hsafe.sourcePlan
                · exact hsafe.oldPlans
              obtain ⟨pre, hrestShape, hpureRest⟩ := ih hrest
                exprFinal hctxBound restInstrs restCtx
                (by simpa [Codegen.stmt] using hgRest)
              refine ⟨exprInstrs ++ pre, ?_, PureViewInstrs.append hpure hpureRest⟩
              rw [hrestShape, List.append_assoc]

/-- Let-chain/return codegen correctness using only EvmYul's VM. -/
theorem codegenViewProgram_runView_correct
    {word : WordState} {program : Stmt} {value : EWord}
    (hprogram : ViewProgram word program value)
    (ctx : Ctx) (hreloadSafe : ViewProgramReloadSafe ctx word program)
    (st : EVM.State) (hctx : ContextAgrees ctx st word)
    (hmemory : st.memory = ByteArray.empty)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx program = .ok (instrs, out)) :
    ∃ final,
      runView instrs st = .ok final ∧
      final.H_return = value.toByteArray ∧
      EncodablePlainInstrs instrs := by
  induction hreloadSafe generalizing value st instrs out with
  | ret ctx word e =>
    cases hprogram with
    | ret _ _ value hview heval =>
      exact codegenRet_runView_correct ctx st word hctx hmemory e hview value
        heval instrs out hgen
  | letSeq ctx word name e bound rest hsafe hsafeRest ih =>
    cases hprogram with
    | letSeq _ _ _ bound' _ value hview heval hrest =>
      have hbound : bound = bound' := by
        apply Option.some.inj
        rw [← hsafe.sourceValue, hsafe.sourceStable, heval]
      subst bound'
      simp only [Codegen.stmt, Codegen.codegenStmt] at hgen
      cases hgExpr : Codegen.codegenExpr ctx e with
      | error err => simp [hgExpr, Bind.bind, Except.bind] at hgen
      | ok exprPair =>
          rcases exprPair with ⟨exprInstrs, exprCtx⟩
          cases hgRest : Codegen.codegenStmt (exprCtx.bindLocal name (some e)) rest with
          | error err => simp [hgExpr, hgRest, Bind.bind, Except.bind] at hgen
          | ok restPair =>
              rcases restPair with ⟨restInstrs, restCtx⟩
              simp [hgExpr, hgRest, Bind.bind, Except.bind] at hgen
              obtain ⟨rfl, rfl⟩ := hgen
              rcases codegenExpr_correct ctx st word hctx e hview bound heval
                  exprInstrs exprCtx (by simpa [Codegen.expr] using hgExpr) with
                ⟨hExprCtx, exprFinal, hrunExpr, hstack, hpc, hframe,
                  hctxExpr, hencExpr⟩
              subst exprCtx
              have hctxBound :
                  ContextAgrees
                    (({ ctx with stackDepth := ctx.stackDepth + 1 }).bindLocal name (some e))
                    exprFinal
                    (word.setLocal name bound) := by
                apply hctxExpr.bindLocal name bound (some e) st.stack hstack
                · intro source hsource
                  simp only [Option.some.injEq] at hsource
                  subst source
                  exact ⟨hview, hsafe.sourceValue⟩
                · exact hsafe.oldValues
                · intro source hsource
                  simp only [Option.some.injEq] at hsource
                  subst source
                  exact hsafe.sourcePlan
                · exact hsafe.oldPlans
              have hmemoryFinal : exprFinal.memory = ByteArray.empty := by
                rw [hframe.memory, hmemory]
              rcases ih hrest exprFinal hctxBound hmemoryFinal restInstrs restCtx
                  (by simpa [Codegen.stmt] using hgRest) with
                ⟨final, hrunRest, hreturn, hencRest⟩
              refine ⟨final, ?_, hreturn,
                EncodablePlainInstrs.append hencExpr hencRest⟩
              rw [runView_append, hrunExpr]
              exact hrunRest

/-- Conjunctive form convenient for exact lowering/building theorems, which establish the
semantic and reload-plan invariants together for one unoptimized view program. -/
theorem codegenViewProgram_runView_correct_of_spec
    {word : WordState} {program : Stmt} {value : EWord}
    (hspec :
      ViewProgram word program value ∧
      ViewProgramReloadSafe ctx word program)
    (st : EVM.State) (hctx : ContextAgrees ctx st word)
    (hmemory : st.memory = ByteArray.empty)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx program = .ok (instrs, out)) :
    ∃ final,
      runView instrs st = .ok final ∧
      final.H_return = value.toByteArray ∧
      EncodablePlainInstrs instrs :=
  codegenViewProgram_runView_correct hspec.1 ctx hspec.2 st hctx hmemory instrs out hgen

/-- A generated view body embedded at an arbitrary byte PC in production code executes through
EvmYul's actual decoder/checker/`X` and returns the exact 32-byte result. -/
theorem codegenViewProgram_X_returns
    {word : WordState} {program : Stmt} {value : EWord}
    (hprogram : ViewProgram word program value)
    (ctx : Ctx) (hreloadSafe : ViewProgramReloadSafe ctx word program)
    (st : EVM.State) (hctx : ContextAgrees ctx st word)
    (hmemory : st.memory = ByteArray.empty)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx program = .ok (instrs, out))
    (code : ByteArray) (pc : Nat)
    (hdecode : DecoderAlong code pc instrs)
    (validJumps : Array EWord)
    (hready : XReady validJumps code pc instrs st) :
    ∃ final,
      EVM.X (instrs.length + 1) validJumps st =
        .ok (.success final value.toByteArray) := by
  rcases codegenViewProgram_runView_correct hprogram ctx hreloadSafe st hctx hmemory
      instrs out hgen with
    ⟨final, hrun, hreturn, _⟩
  refine ⟨final, ?_⟩
  rw [← hreturn]
  exact X_eq_success_of_runView validJumps code pc instrs st final hdecode hready hrun

/-- End-to-end theorem: successful pure let/return WordEval codegen and encoding executes through
EvmYul's actual decoder/checker/`X` and returns the corresponding 32-byte word. -/
theorem codegenViewProgram_encode_X_returns
    {word : WordState} {program : Stmt} {value : EWord}
    (hprogram : ViewProgram word program value)
    (ctx : Ctx) (hreloadSafe : ViewProgramReloadSafe ctx word program)
    (st : EVM.State) (hctx : ContextAgrees ctx st word)
    (hmemory : st.memory = ByteArray.empty)
    (instrs : List Instr) (out : Ctx)
    (hgen : Codegen.stmt ctx program = .ok (instrs, out))
    (code : ByteArray) (hencode : encode instrs = .ok code)
    (hlimit : code.size + 33 < 2^64)
    (validJumps : Array EWord)
    (hready : XReady validJumps code 0 instrs st) :
    ∃ final,
      EVM.X (instrs.length + 1) validJumps st =
        .ok (.success final value.toByteArray) := by
  rcases codegenViewProgram_runView_correct hprogram ctx hreloadSafe st hctx hmemory
      instrs out hgen with
    ⟨_, _, _, hencodable⟩
  exact codegenViewProgram_X_returns hprogram ctx hreloadSafe st hctx hmemory instrs out hgen
    code 0 (decoderAlong_encode instrs hencodable code hencode hlimit)
    validJumps hready

end Lsc.Compile.Bytecode
