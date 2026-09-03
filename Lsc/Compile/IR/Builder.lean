import Lsc.Compile.IR

namespace Lsc.Compile.IR.Builder

open Lsc (Ident)

/-- Fresh-name supply for compiler-generated IR locals. `used` contains every user local that
    may be read by the expression being lowered. -/
structure Fresh where
  used : List Ident := []
  next : Nat := 0

/-- Maximum identifier length in a used-name list. -/
def maxNameLength : List Ident → Nat
  | [] => 0
  | name :: used => max name.length (maxNameLength used)

theorem length_le_maxNameLength {used : List Ident} {name : Ident} (h : name ∈ used) :
    name.length ≤ maxNameLength used := by
  induction used with
  | nil => cases h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      simp only [maxNameLength]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Keep ASCII Yul identifier characters and replace all other tag characters with `_`. -/
def sanitizeTagChar (c : Char) : Char :=
  if c = '_' then c
  else if 'a' ≤ c ∧ c ≤ 'z' then c
  else if 'A' ≤ c ∧ c ≤ 'Z' then c
  else if '0' ≤ c ∧ c ≤ '9' then c
  else '_'

def sanitizeTag (tag : String) : String :=
  String.ofList (tag.toList.map sanitizeTagChar)

/-- A Yul-compatible generated name, padded until the whole name is longer than every identifier
in `used`; the readable tag is retained for generated Yul and debugging. -/
def generatedName (tag : String) (used : List Ident) : Ident :=
  let base := "lsc_" ++ sanitizeTag tag ++ "_"
  base ++ String.ofList
    (List.replicate (maxNameLength used + 1 - base.length) 'x')

theorem maxNameLength_lt_generatedName_length (tag : String) (used : List Ident) :
    maxNameLength used < (generatedName tag used).length := by
  simp only [generatedName, String.length_append, String.length_ofList, List.length_replicate]
  omega

theorem generatedName_not_mem (tag : String) (used : List Ident) :
    generatedName tag used ∉ used := by
  intro h
  have hle := length_le_maxNameLength h
  have hlt := maxNameLength_lt_generatedName_length tag used
  omega

/-- Generate a fresh Yul-compatible compiler local in one total, kernel-reducible step.
`next` remains a monotonically increasing compatibility counter; freshness itself follows from
the generated name's length and does not depend on searching from that counter. -/
def Fresh.take (fresh : Fresh) (tag : String) : Ident × Fresh :=
  let name := generatedName tag fresh.used
  (name, { used := name :: fresh.used, next := fresh.next + 1 })

theorem take_name_not_used (fresh : Fresh) (tag : String) :
    (fresh.take tag).1 ∉ fresh.used := by
  exact generatedName_not_mem tag fresh.used

@[simp] theorem take_used (fresh : Fresh) (tag : String) :
    (fresh.take tag).2.used = (fresh.take tag).1 :: fresh.used := by
  rfl

@[simp] theorem take_next (fresh : Fresh) (tag : String) :
    (fresh.take tag).2.next = fresh.next + 1 := by
  rfl

theorem take_used_extends (fresh : Fresh) (tag : String) :
    ∀ {name}, name ∈ fresh.used → name ∈ (fresh.take tag).2.used := by
  intro name h
  simp [h]

theorem take_name_used (fresh : Fresh) (tag : String) :
    (fresh.take tag).1 ∈ (fresh.take tag).2.used := by
  simp

theorem take_used_nodup (fresh : Fresh) (tag : String) (h : fresh.used.Nodup) :
    (fresh.take tag).2.used.Nodup := by
  simp [take_name_not_used fresh tag, h]

/-- A linear sequence of local bindings under construction. -/
structure Build where
  fresh : Fresh
  binds : List (Ident × Expr) := []

/-- Append one binding and return its local expression. -/
def Build.bind (build : Build) (tag : String) (value : Expr) : Build × Expr :=
  let (name, fresh) := build.fresh.take tag
  ({ fresh, binds := build.binds ++ [(name, value)] }, .local name)

theorem bind_name_not_used (build : Build) (tag : String) (value : Expr) :
    let result := build.bind tag value
    ∃ name, result.2 = .local name ∧ name ∉ build.fresh.used ∧
      result.1.fresh.used = name :: build.fresh.used := by
  simp only [Build.bind]
  exact ⟨_, rfl, take_name_not_used build.fresh tag, rfl⟩

theorem bind_used_extends (build : Build) (tag : String) (value : Expr) :
    ∀ {name}, name ∈ build.fresh.used → name ∈ (build.bind tag value).1.fresh.used := by
  exact take_used_extends build.fresh tag

theorem bind_fresh_nodup (build : Build) (tag : String) (value : Expr)
    (h : build.fresh.used.Nodup) :
    (build.bind tag value).1.fresh.used.Nodup := by
  exact take_used_nodup build.fresh tag h

/-- Consecutive builder binds always return distinct locals, independently of their tags. -/
theorem bind_bind_names_ne (build : Build) (tag₁ tag₂ : String) (value₁ value₂ : Expr) :
    let first := build.bind tag₁ value₁
    let second := first.1.bind tag₂ value₂
    second.2 ≠ first.2 := by
  dsimp only [Build.bind]
  intro h
  injection h with hname
  apply take_name_not_used (build.fresh.take tag₁).2 tag₂
  rw [hname]
  exact take_name_used build.fresh tag₁

/-- Turn a binding list into a right-nested statement sequence. -/
def seqLets : List (Ident × Expr) → Stmt → Stmt
  | [], tail => tail
  | (name, value) :: rest, tail =>
      .seq (.letBind name value) (seqLets rest tail)

def Build.finish (build : Build) (tail : Stmt) : Stmt :=
  seqLets build.binds tail

end Lsc.Compile.IR.Builder
