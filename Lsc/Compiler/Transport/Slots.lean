import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.Layout

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Read a scalar / `map1` slot out of `σ` from `storageRel`.
-/

namespace Lsc.Compiler

open YulSemantics.EVM

namespace Proof

theorem storageRel_scalar {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .scalar) :
    σ (BitVec.ofNat 256 slot) = BitVec.ofNat 256 (Γ.st.scalar slot s) := by
  have h := hs slot fd hfd
  simp [hkind] at h
  exact h

theorem storageRel_scalar_toNat {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {v : Nat}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .scalar)
    (hval : Γ.st.scalar slot s = v)
    (hv : v < wordBound) :
    (σ (BitVec.ofNat 256 slot)).toNat = v := by
  have h := storageRel_scalar hs hfd hkind
  rw [hval] at h
  simpa [h] using toNat_ofNat_of_lt hv

theorem storageRel_map1 {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {a : Address}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .map1)
    (ha : Nat.lt a wordBound) :
    σ (mapSlot1 κ slot a) = BitVec.ofNat 256 (Γ.st.map1 slot s a) := by
  have h := hs slot fd hfd
  simp [hkind] at h
  exact h a ha

theorem storageRel_map1_toNat {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {a : Address} {v : Nat}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .map1)
    (hval : Γ.st.map1 slot s a = v)
    (ha : Nat.lt a wordBound) (hv : v < wordBound) :
    (σ (mapSlot1 κ slot a)).toNat = v := by
  have h := storageRel_map1 hs hfd hkind ha
  rw [hval] at h
  simpa [h] using toNat_ofNat_of_lt hv

end Proof

end Lsc.Compiler
