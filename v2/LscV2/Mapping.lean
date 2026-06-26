import Mathlib.Data.Finmap
import LscV2.Types

namespace LscV2

structure Mapping (K V : Type) [DecidableEq K] where
  inner : Finmap (fun _ : K => V)

namespace Mapping

variable {K V : Type} [DecidableEq K] [Inhabited V]

def empty : Mapping K V := ⟨∅⟩

def get (m : Mapping K V) (k : K) : V :=
  (m.inner.lookup k).getD default

def set (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  ⟨m.inner.insert k v⟩

@[simp]
theorem get_set_same (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v := by
  simp [get, set, Finmap.lookup_insert]

@[simp]
theorem get_set_different (m : Mapping K V) (k1 k2 : K) (v : V)
    (h : k1 ≠ k2) : (m.set k1 v).get k2 = m.get k2 := by
  simp [get, set]
  rw [Finmap.lookup_insert_of_ne (s := m.inner) (h := h.symm)]

end Mapping

end LscV2
