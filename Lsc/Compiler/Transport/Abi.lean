import Lsc.Compiler.Proof.Core

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Generic ABI list-length lemmas for `TransportCodec.encode` / `decode`.
-/

namespace Lsc.Compiler

theorem length_eq_zero {α} {l : List α} : l.length = 0 ↔ l = [] := by
  cases l <;> simp

theorem length_eq_two {α} {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b rest =>
      cases rest with
      | nil => simp
      | cons _ _ => simp

end Lsc.Compiler
