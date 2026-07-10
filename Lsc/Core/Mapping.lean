import Mathlib.Data.Finmap
import Lsc.Types
import Lsc.Core.MapKey

namespace Lsc

/-!
# `Mapping` — opaque finite maps for contract storage

EVM storage maps support only point reads and writes (`SLOAD`/`SSTORE` per key). This type wraps
`Mathlib.Data.Finmap` and exposes **only** `get`/`set`/`empty` — no `toList`, `fold`, or
`filter` — so contract authors cannot express unbounded iteration that has no on-chain equivalent.

Missing keys read as `Inhabited.default` (zero for numeric value types), matching EVM semantics.
See `docs/DESIGN.md` §9 and `docs/framework/IMPLEMENTATION.md` Step 3.
-/

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
theorem get_set_same (m : Mapping K V) (k : K) (v : V) : (m.set k v).get k = v := by
  simp [get, set, Finmap.lookup_insert]

@[simp]
theorem get_set_different (m : Mapping K V) (k1 k2 : K) (v : V) (h : k1 ≠ k2) :
    (m.set k1 v).get k2 = m.get k2 := by
  simp [get, set, Finmap.lookup_insert_of_ne, Ne.symm h]

end Mapping

end Lsc
