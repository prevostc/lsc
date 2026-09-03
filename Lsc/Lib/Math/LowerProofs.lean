import Lsc.Lib.Fixed.IRExpand
import Lsc.Lib.Fixed.Optimize
import Lsc.Compile.IR.Eval
import Lsc.Compile.IR.BuilderSemantics
import Lsc.Lib.Math.SqrtAlgo
import Lsc.Lib.Math.SqrtSharingProofs
import Lsc.Lib.Math.Stmt

namespace Lsc.Math.LowerProofs

open Lsc.Compile.IR
open Lsc.Compile.IR.Builder
open Lsc.Math

private theorem eval_irOps_hom (st : IRState) :
    SqrtAlgo.OpsHom Lsc.Fixed.IRExpand.irOps SqrtAlgo.natOps (evalExpr st) := by
  constructor <;> intros <;> rfl

theorem eval_sqrt_irOps (st : IRState) (e : Expr) :
    evalExpr st (SqrtAlgo.sqrt Lsc.Fixed.IRExpand.irOps e) =
      SqrtAlgo.sqrtNat (evalExpr st e) := by
  exact SqrtAlgo.map_sqrt (eval_irOps_hom st) e

theorem eval_expandSqrtDown (st : IRState) (scale : Nat) (x : Expr) :
    evalExpr st (Lsc.Fixed.IRExpand.expandSqrtDown scale x) =
      SqrtAlgo.sqrtNat (if scale == 1 then evalExpr st x else evalExpr st x * scale) := by
  simp only [Lsc.Fixed.IRExpand.expandSqrtDown]
  split
  · simpa using eval_sqrt_irOps st x
  · simpa using eval_sqrt_irOps st (.mul x (.lit scale))

theorem sqrtBinds_is_single_source (a : Expr) (build : Build) :
    Lsc.Fixed.IRExpand.sqrtBinds a build =
      SqrtAlgo.sqrtWith Lsc.Fixed.IRExpand.irOps
        Lsc.Fixed.IRExpand.irSharing build a := rfl

private def builderSimulation (st : IRState) (inv : FreshnessInvariant st) :
    SqrtAlgo.SharingSimulation Lsc.Fixed.IRExpand.irOps Lsc.Fixed.IRExpand.irSharing
      SqrtAlgo.natOps SqrtAlgo.Sharing.identity where
  StateRel _ _ := True
  ValRel build _ e n := inv.Safe build e ∧ evalExpr (Builder.run st build) e = n
  lit _ n := ⟨inv.lit _ n, rfl⟩
  add _ ha hb := ⟨inv.add ha.1 hb.1, by
    simp only [Lsc.Fixed.IRExpand.irOps, SqrtAlgo.natOps, evalExpr]
    rw [ha.2, hb.2]
    rfl⟩
  sub _ ha hb := ⟨inv.sub ha.1 hb.1, by
    simp only [Lsc.Fixed.IRExpand.irOps, SqrtAlgo.natOps, evalExpr]
    rw [ha.2, hb.2]
    rfl⟩
  mul _ ha hb := ⟨inv.mul ha.1 hb.1, by
    simp only [Lsc.Fixed.IRExpand.irOps, SqrtAlgo.natOps, evalExpr]
    rw [ha.2, hb.2]
    rfl⟩
  div _ ha hb := ⟨inv.div ha.1 hb.1, by
    simp only [Lsc.Fixed.IRExpand.irOps, SqrtAlgo.natOps, evalExpr]
    rw [ha.2, hb.2]
    rfl⟩
  gt _ ha hb := by
    refine ⟨inv.gt ha.1 hb.1, ?_⟩
    simp only [Lsc.Fixed.IRExpand.irOps, SqrtAlgo.natOps, evalExpr]
    rw [ha.2, hb.2]
  shr _ ha hb := by
    refine ⟨inv.shr ha.1 hb.1, ?_⟩
    simp only [Lsc.Fixed.IRExpand.irOps, evalExpr, SqrtAlgo.natOps]
    rw [ha.2, hb.2]
  bind _ hv tag := by
    obtain ⟨hresult, hpreserve⟩ := inv.bind hv.1 tag
    refine ⟨trivial, ⟨hresult, ?_⟩, ?_⟩
    · simp only [Lsc.Fixed.IRExpand.irSharing, SqrtAlgo.Sharing.identity]
      rw [Builder.eval_bind_result, hv.2]
    · intro old old' hold
      obtain ⟨hsafe, heval⟩ := hpreserve hold.1
      exact ⟨hsafe, heval.trans hold.2⟩

/-- Kernel-checked semantics of the linear bindings emitted by `sqrtBinds`.

`FreshnessInvariant` is the precise required name-supply hypothesis: every sharing bind preserves
the denotation of all expressions that are live across it.  It permits an arbitrary initial
builder prefix; both the input and result are interpreted after executing that prefix. -/
theorem eval_sqrtBinds (st : IRState) (inv : FreshnessInvariant st)
    (build : Build) (a : Expr) (ha : inv.Safe build a) :
    let result := Lsc.Fixed.IRExpand.sqrtBinds a build
    evalExpr (Builder.run st result.1) result.2 =
      SqrtAlgo.sqrtNat (evalExpr (Builder.run st build) a) := by
  have h := SqrtAlgo.sqrtWith_rel (builderSimulation st inv)
    (sa := build) (sb := ()) (a := a)
    (a' := evalExpr (Builder.run st build) a) trivial
    ⟨ha, rfl⟩
  exact h.2.2

/-- Compiler-style specialization: seeding `Fresh.used` with every free variable is sufficient;
the concrete name-supply invariant and the empty builder prefix require no caller assumption. -/
theorem eval_sqrtBinds_seeded (st : IRState) (fresh : Fresh) (a : Expr)
    (ha : NameSafe { fresh } a) :
    let result := Lsc.Fixed.IRExpand.sqrtBinds a { fresh }
    evalExpr (Builder.run st result.1) result.2 =
      SqrtAlgo.sqrtNat (evalExpr st a) := by
  simpa [Builder.run, Build.finish, seqLets] using
    eval_sqrtBinds st (nameFreshnessInvariant st) { fresh } a ha

def sqrtProductIR (a b : Expr) : Expr :=
  let scale := 10 ^ 18
  let rounded := .div (.add (.mul a b) (.div (.lit scale) (.lit 2))) (.lit scale)
  Lsc.Fixed.IRExpand.expandSqrtDown scale rounded

theorem eval_sqrtProductIR (st : IRState) (a b : Nat)
    (ha : st.lookupLocal "a" = a) (hb : st.lookupLocal "b" = b) :
    evalExpr st (sqrtProductIR (.local "a") (.local "b")) =
      SqrtAlgo.sqrtNat
        (((a * b + (10 ^ 18) / 2) / (10 ^ 18)) * (10 ^ 18)) := by
  unfold sqrtProductIR
  rw [eval_expandSqrtDown]
  simp only [evalExpr, ha, hb]
  rfl

/-- The linear sqrt expansion has a fixed number of shallow bindings: fourteen magnitude
    bindings, one initializer, six Newton steps, and one floor correction. -/
example :
    let (build, _) :=
      Lsc.Fixed.IRExpand.sqrtBinds (.lit 144) { fresh := {} }
    build.binds.length = 22 := by
  native_decide

/-- Focused evaluator check for the statement-level sharing path. -/
example :
    let (build, _) :=
      Lsc.Fixed.IRExpand.sqrtBinds (.lit 144) { fresh := {} }
    (evalStmt {} (build.finish .skip)).lookupLocal
        "lsc_sqrt_floor_xxxxxxxxxxxxxxxxxx" =
      SqrtAlgo.sqrtNat 144 := by
  native_decide

/-- A user local matching the first compiler candidate is skipped, preventing capture. -/
example :
    let fresh : Fresh := { used := ["lsc_sqrt_aa_0"] }
    let (build, _) :=
      Lsc.Fixed.IRExpand.sqrtBinds (.local "lsc_sqrt_aa_0") { fresh }
    build.binds.head?.map (·.1) = some "lsc_sqrt_aa_xx" := by
  native_decide

/-- The return-lowering entry point seeds freshness from user locals, not only direct builder
    callers. -/
example :
    (match Lsc.Fixed.lowerRetStmt (fun _ => none) (fun _ => none)
        (.sqrtDownChecked (.static 0) (.var "lsc_sqrt_aa_0")) with
      | .ok (.seq (.letBind name _) _) => name == "lsc_sqrt_aa_xx"
      | _ => false) = true := by
  native_decide

end Lsc.Math.LowerProofs
