import Lsc.Lang.Core
import Lsc.Lang.Interface
import KeccakEngine.Sponge

/-!
# Contract assembly: the `ContractDef` data model

`lsc_contract C f₁ … fₙ` (in `Lsc.Lang.Reify`) reifies the listed entrypoints under namespace
`C` and produces `C.contract : ContractDef` plus `C.Fn` / `C.entry` / `C.spec`. Everything
downstream of `C.contract` is a Lean function of that value: ABI JSON, selectors, the Yul
dispatcher and codegen (`Lsc.Compiler.toYul`).

This file is the data model plus the ABI hashing helpers (KeccakEngine); it has no
metaprogramming. `FnDef.core` is a dependent field, so `ToExpr`/`Repr` are hand-written by
the assembly command rather than derived.
-/

namespace Lsc

/-- ABI types the surface can expose. `Nat`/`Amount τ s` are `uint256`, `Address` is
`address`, `Flag` is `bool`. -/
inductive AbiTy
  | uint256
  | address
  | bool
  deriving DecidableEq, Repr, Lean.ToExpr

def AbiTy.render : AbiTy → String
  | .uint256 => "uint256"
  | .address => "address"
  | .bool => "bool"

/-- A named ABI parameter (function input, event or error field). -/
structure Param where
  name : String
  ty : AbiTy
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Entrypoint kinds. `tx` mutates state (and, once the lock lands, acquires it); `view`
must have no writes/emits (checked at assembly); `constructor` runs once at deployment. -/
inductive FnKind
  | tx
  | view
  | constructor
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Storage field shapes, in declaration order; the index is the storage slot. -/
inductive FieldKind
  | scalar
  | map1
  | map2
  deriving DecidableEq, Repr, Lean.ToExpr

structure FieldDef where
  name : String
  kind : FieldKind
  /-- Value type (for mappings, the type stored at a key). -/
  ty : AbiTy
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A reified entrypoint. -/
structure FnDef where
  /-- ABI name (the Lean declaration's last component). -/
  name : String
  /-- The Lean constant this was reified from. -/
  decl : Lean.Name
  kind : FnKind
  params : List Param
  ret : RetTy
  core : Core ret

structure EventDef where
  name : String
  params : List Param
  deriving DecidableEq, Repr, Lean.ToExpr

structure ErrorDef where
  name : String
  params : List Param
  deriving DecidableEq, Repr, Lean.ToExpr

/-- One static binding: storage field holding the callee address, plus the interface's
methods in declaration = method-index order. -/
structure BindingDef where
  name : String
  fieldSlot : Nat
  ifaceName : String
  methods : List (String × AbiSpec)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Everything the compiler needs about one contract. -/
structure ContractDef where
  name : String
  fields : List FieldDef
  /-- `tx` and `view` entrypoints, in dispatch order. -/
  functions : List FnDef
  ctor : Option FnDef
  events : List EventDef
  errors : List ErrorDef
  bindings : List BindingDef := []

/-! ## ABI hashing -/

/-- Big-endian bytes as a natural number. -/
def bytesToNat (bytes : ByteArray) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `keccak256` of a byte string, as a word. -/
def keccakWord (bytes : ByteArray) : Nat :=
  bytesToNat (KeccakEngine.keccak256 bytes)

/-- Canonical signature, e.g. `transfer(address,uint256)`. -/
def abiSignature (name : String) (params : List Param) : String :=
  s!"{name}({String.intercalate "," (params.map (·.ty.render))})"

/-- 4-byte function/error selector as a number below `2^32`. -/
def selectorOf (name : String) (params : List Param) : Nat :=
  keccakWord (abiSignature name params).toUTF8 / 2 ^ 224

/-- Full 32-byte event topic. -/
def topic0Of (name : String) (params : List Param) : Nat :=
  keccakWord (abiSignature name params).toUTF8

def FnDef.signature (f : FnDef) : String := abiSignature f.name f.params
def FnDef.selector (f : FnDef) : Nat := selectorOf f.name f.params
def ErrorDef.selector (e : ErrorDef) : Nat := selectorOf e.name e.params
def EventDef.topic0 (e : EventDef) : Nat := topic0Of e.name e.params

/-- ABI return types of a `RetTy` (pairs flatten to a tuple of outputs). -/
def RetTy.abi : RetTy → List AbiTy
  | .unit => []
  | .word => [.uint256]
  | .addr => [.address]
  | .flag => [.bool]
  | .pair a b => a.abi ++ b.abi

/-! ## Storage-schema laws

`lsc_schema` fills `StorageSchema` with `List.getD` tables. These nine equations say that an
update of field `j` writes that field and leaves every other field unchanged. Generated per
contract as `C.schema_lawful`; `toYulFn_correct` takes `(hΓ : Γ.st.Lawful c.fields)`. -/

structure StorageSchema.Lawful {S : Type} (st : StorageSchema S) (fields : List FieldDef) : Prop where
  scalar_scalar : ∀ (i j : Nat) (σ : S) (v : Nat),
    (fields[j]?).map (·.kind) = some FieldKind.scalar →
      st.scalar i (st.scalarUpd j σ v) = if i = j then v else st.scalar i σ
  scalar_map1 : ∀ (i j : Nat) (σ : S) (v : Nat),
    (fields[j]?).map (·.kind) = some FieldKind.scalar →
      st.map1 i (st.scalarUpd j σ v) = st.map1 i σ
  scalar_map2 : ∀ (i j : Nat) (σ : S) (v : Nat),
    (fields[j]?).map (·.kind) = some FieldKind.scalar →
      st.map2 i (st.scalarUpd j σ v) = st.map2 i σ
  map1_scalar : ∀ (i j : Nat) (σ : S) (m : Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map1 →
      st.scalar i (st.map1Upd j σ m) = st.scalar i σ
  map1_map1 : ∀ (i j : Nat) (σ : S) (m : Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map1 →
      st.map1 i (st.map1Upd j σ m) = if i = j then m else st.map1 i σ
  map1_map2 : ∀ (i j : Nat) (σ : S) (m : Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map1 →
      st.map2 i (st.map1Upd j σ m) = st.map2 i σ
  map2_scalar : ∀ (i j : Nat) (σ : S) (m : Nat → Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map2 →
      st.scalar i (st.map2Upd j σ m) = st.scalar i σ
  map2_map1 : ∀ (i j : Nat) (σ : S) (m : Nat → Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map2 →
      st.map1 i (st.map2Upd j σ m) = st.map1 i σ
  map2_map2 : ∀ (i j : Nat) (σ : S) (m : Nat → Nat → Nat),
    (fields[j]?).map (·.kind) = some FieldKind.map2 →
      st.map2 i (st.map2Upd j σ m) = if i = j then m else st.map2 i σ

end Lsc
