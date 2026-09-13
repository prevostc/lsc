import Lsc.Lang.Amount
import Lsc.Lang.Word
import KeccakEngine.Sponge
import Lean.Elab.Term

/-!
# External-contract interfaces: `Fn`/`View` signatures, oracle callee, `Ref`

An interface is an ordinary Lean structure whose fields are `Fn`/`View` markers
(the ABI). `deriving Interface` (see `Lsc.Lang.InterfaceDeriving`) generates the
method table, typed calls, a per-interface `I.Ref`, `I.Impl`, and `Impl.ofRef`.

Callee behaviour is a deterministic, memory-blind `Oracle` on `World.ext`.
`Tx.call` / `Tx.view` / `Tx.tryCall` consult `w.oracle` at a concrete address;
a `Fn` revert is `oracle.call = none` (`Err.callFailed`). `View` methods are
pure oracle reads and leave the world unchanged. The oracle field is never
modified by a Tx primitive. Reentrancy during a call is not modelled in this
slice (`self` is unchanged).

`I.Spec` is a user-written `Prop` structure over `T : I.Impl …`, in the same
shape as our theorems (success as hypothesis, state delta as conclusion). The
adversary is the baseline oracle; a `Spec` hypothesis restricts it.

Dot notation `asset.transferFrom …` is `I.Ref.transferFrom` via a generated
`I.Ref` structure. `Ref (I args)` is a macro expanding to `I.Ref args`.
`asset.try.transferFrom` is the non-reverting form
(`Tx … (Except (Err ε) R)`). `asset.impl w` is `I.Impl.ofRef asset`, used as
`(hT : I.Spec (asset.impl w))`.

TODO: payable methods are not modelled yet.
-/

namespace Lsc

/-- Field-type marker: a state-changing ABI method. `τ` is the curried
argument telescope ending at the return type, e.g. `Address → Amount a → Bool`. -/
structure Fn (τ : Type) : Type where

/-- Field-type marker: a pure ABI view. `τ` is the curried argument telescope
ending at the return type, e.g. `Address → Amount a`. -/
structure View (τ : Type) : Type where

/-- How a successful CALL's return data is read. -/
inductive AbiRet
  | word
  | boolOpt
  | none
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Compiler-only ABI of one interface method (selector, arity, return kind). -/
structure AbiSpec where
  selector : Nat
  arity : Nat
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

/-- One ABI method: name, selector (`keccak(name(types))/2^224`), arity, view bit,
return kind. -/
structure MethodSig where
  name : String
  selector : Nat
  arity : Nat
  isView : Bool
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

def MethodSig.toAbiSpec (m : MethodSig) : AbiSpec :=
  ⟨m.selector, m.arity, m.ret⟩

/-! ## ABI hashing (same formula as `selectorOf` in `Contract.lean`) -/

/-- Big-endian bytes as a natural number. -/
def bytesToNat (bytes : ByteArray) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `keccak256` of a byte string, as a word. -/
def keccakWord (bytes : ByteArray) : Nat :=
  bytesToNat (KeccakEngine.keccak256 bytes)

/-- 4-byte selector: `keccak256("name(type,…)") / 2^224`. Same as `selectorOf`. -/
def methodSelector (name : String) (argTys : List String) : Nat :=
  keccakWord (s!"{name}({String.intercalate "," argTys})").toUTF8 / 2 ^ 224

/-! ## ABI types -/

/-- Solidity ABI name and one-word encoding of a surface type. -/
class AbiType (α : Type) where
  name : String
  encode : α → Word

instance : AbiType Word where
  name := "uint256"
  encode := id

instance {a : Asset} : AbiType (Amount a) where
  name := "uint256"
  encode := Amount.raw

instance : AbiType Address where
  name := "address"
  encode := Address.toWord

instance : AbiType Bool where
  name := "bool"
  encode := fun b => if b then 1 else 0

/-- Decode of a method's return words. Bool uses the `boolOpt` convention:
empty return is `true`, otherwise the word is non-zero. Word/Amount/Address
need exactly one word. `Unit` ignores the payload. -/
class AbiRetType (α : Type) where
  kind : AbiRet
  decode : List Word → Option α

instance : AbiRetType Bool where
  kind := .boolOpt
  decode
    | [] => some true
    | [w] => some (w != 0)
    | _ => none

instance : AbiRetType Word where
  kind := .word
  decode
    | [w] => some w
    | _ => none

instance {a : Asset} : AbiRetType (Amount a) where
  kind := .word
  decode
    | [w] => some ⟨w⟩
    | _ => none

instance : AbiRetType Address where
  kind := .word
  decode
    | [w] => some (w : Address)
    | _ => none

instance : AbiRetType Unit where
  kind := .none
  decode := fun _ => some ()

/-- View/`Impl` reads are total: a malformed ABI payload becomes `default`. -/
def decodeOrDefault {α} [AbiRetType α] [Inhabited α] (rets : List Word) : α :=
  (AbiRetType.decode rets).getD default

/-! ## `Interface` class -/

/-- Method table of an interface type `I` (the ABI structure, e.g. `IERC20 a`). -/
class Interface (I : Type) where
  methods : List MethodSig

/-- Look up a method selector by ABI name. `0` if missing (should not happen
for a derived table). -/
def Interface.selector {I : Type} [Interface I] (name : String) : Nat :=
  match (methods (I := I)).find? (fun m => m.name = name) with
  | some m => m.selector
  | none => 0

/-! ## `Ref (I args)` → `I.Ref args`

Per-interface `I.Ref` is a one-field `{ addr : Address }` structure generated
by `deriving Interface`. This macro makes `Ref (IERC20 vaultAsset)` that type,
so `asset.transferFrom` resolves to `IERC20.Ref.transferFrom`. -/
syntax:arg (name := lscRefTy) "Ref" "(" ident term:arg* ")" : term

macro_rules
  | `(Ref ($f:ident $args:term*)) =>
    let r := Lean.mkIdent (f.getId ++ `Ref)
    `($r $args*)

/-! ## Oracle CALL / STATICCALL primitives

`self` is unchanged: reentrancy during a call is not modelled in this slice. -/

namespace Tx

variable {S X E ε α : Type} [AbiRetType α]

/-- CALL through the world's oracle. `none` or an undecodable payload is
`.callFailed`. Success updates `ext` only. -/
def call (addr : Address) (sel : Nat) (args : List Word) : Tx S X E ε α :=
  fun _ctx w =>
    match w.oracle.call addr sel args w.ext with
    | none => .error .callFailed
    | some (rets, x') =>
      match AbiRetType.decode (α := α) rets with
      | none => .error .callFailed
      | some v => .ok (v, { w with ext := x' })

/-- STATICCALL-like view: `oracle.view`, world unchanged. Undecodable payload
is `.callFailed`. -/
def view (addr : Address) (sel : Nat) (args : List Word) : Tx S X E ε α :=
  fun _ctx w =>
    match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
    | none => .error .callFailed
    | some v => .ok (v, w)

/-- Non-reverting CALL: oracle `none` or an undecodable payload becomes
`.ok (.error .callFailed, w)` (world unchanged). A decoded success updates
`ext` and returns `.ok (.ok v, w')`. -/
def tryCall (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε (Except (Err ε) α) :=
  fun _ctx w =>
    match w.oracle.call addr sel args w.ext with
    | none => .ok (.error .callFailed, w)
    | some (rets, x') =>
      match AbiRetType.decode (α := α) rets with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, { w with ext := x' })

/-- Non-reverting view: decode failure is `.ok (.error .callFailed, w)`. -/
def tryView (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε (Except (Err ε) α) :=
  fun _ctx w =>
    match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
    | none => .ok (.error .callFailed, w)
    | some v => .ok (.ok v, w)

@[simp] theorem run_call (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .error .callFailed
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .error .callFailed
        | some v => .ok (v, { w with ext := x' }) :=
  rfl

@[simp] theorem call_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (call (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (call (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

@[simp] theorem run_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .error .callFailed
      | some v => .ok (v, w) :=
  rfl

@[simp] theorem view_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (view (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (view (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

/-- A successful CALL: the oracle returned a decodable payload and `ext`
was updated. -/
theorem run_call_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    ∃ rets x', w.oracle.call addr sel args w.ext = some (rets, x') ∧
      AbiRetType.decode (α := α) rets = some v ∧
      w' = { w with ext := x' } := by
  simp only [run_call] at h
  cases hcall : w.oracle.call addr sel args w.ext with
  | none =>
    simp [hcall] at h
  | some pair =>
    rcases pair with ⟨rets, x'⟩
    simp [hcall] at h
    cases hdec : AbiRetType.decode (α := α) rets with
    | none =>
      simp [hdec] at h
    | some v' =>
      simp [hdec] at h
      rcases h with ⟨hv, hw⟩
      subst hv
      exact ⟨rets, x', rfl, hdec, hw.symm⟩

/-- Oracle `none` is `.callFailed`. -/
theorem run_call_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : w.oracle.call addr sel args w.ext = none) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed := by
  simp [run_call, h]

/-- A successful view: the oracle payload decoded and the world is unchanged. -/
theorem run_view_ok {addr : Address} {sel : Nat} {args : List Word}
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E}
    (h : Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w')) :
    AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = some v ∧
      w' = w := by
  simp only [run_view] at h
  split at h
  · cases h
  · next hv =>
    cases h
    exact ⟨hv, rfl⟩

/-- Decode failure on a view is `.callFailed`; the world is unchanged. -/
theorem run_view_none (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E)
    (h : AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) = none) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .error .callFailed := by
  simp [run_view, h]

@[simp] theorem run_tryCall (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .ok (.error .callFailed, w)
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .ok (.error .callFailed, w)
        | some v => .ok (.ok v, { w with ext := x' }) :=
  rfl

@[simp] theorem tryCall_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (tryCall (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

@[simp] theorem run_tryView (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryView (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, w) :=
  rfl

/-- A successful CALL leaves `self` unchanged (no reentrancy in this slice). -/
theorem call_self (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.self = w.self := by
  simp [run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

/-- A successful CALL leaves the oracle unchanged. -/
theorem call_oracle (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.oracle = w.oracle := by
  simp [run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

/-- A successful view returns the pre-world. -/
theorem view_world (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w' = w := by
  simp [run_view]
  split
  · intro h; cases h
  · intro h; cases h; rfl

end Tx

/-! ### Core-word wrappers

Core binds `Nat`. `callAsNat .word` is definitionally `Tx.call (α := Nat)`.
`boolOpt` / `none` are `<$>` of the typed `Tx.call` so ABI decode matches
`AbiRetType` exactly. -/
namespace Tx

variable {S X E ε : Type}

/-- Bit encoding of a `Bool` ABI result (`true` ↔ `1`). -/
@[inline] def boolBit (b : Bool) : Nat := if b then 1 else 0

/-- Inverse of `boolBit` on `{0,1}`. Non-zero is `true`, matching
`AbiRetType Bool` (`w != 0`) and ERC20 `boolOpt`. Reify wraps a Core
`boolOpt` word with this (a named function, so certificate `simp` can
match it). -/
@[inline] def natToBool (n : Nat) : Bool := n != 0

@[simp] theorem natToBool_boolBit (b : Bool) : natToBool (boolBit b) = b := by
  cases b <;> rfl

@[simp] theorem natToBool_eq (n : Nat) : natToBool n = (n != 0) := rfl

@[simp] theorem natToBool_eq_true (n : Nat) : natToBool n = true ↔ n ≠ 0 := by
  simp [natToBool]

@[simp] theorem natToBool_zero : natToBool 0 = false := rfl
@[simp] theorem natToBool_one : natToBool 1 = true := rfl

/-- `decide (n ≠ 0) = true` is `n ≠ 0`. Used when `require (ok = true)`
meets a `n != 0` decode. -/
@[simp] theorem decide_ne_zero_eq_true (n : Nat) :
    decide (n ≠ 0) = true ↔ n ≠ 0 :=
  decide_eq_true_iff

@[simp] theorem bne_zero_eq_true (n : Nat) : (n != 0) = true ↔ n ≠ 0 := by
  simp [bne]

/-- `Tx.call` with the result erased to a Core word. -/
def callAsNat (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε Nat :=
  match ret with
  | .word => call (α := Nat) addr sel args
  | .boolOpt => boolBit <$> call (α := Bool) addr sel args
  | .none => (fun _ : Unit => (0 : Nat)) <$> call (α := Unit) addr sel args

/-- `Tx.view` with the result erased to a Core word. -/
def viewAsNat (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε Nat :=
  match ret with
  | .word => view (α := Nat) addr sel args
  | .boolOpt => boolBit <$> view (α := Bool) addr sel args
  | .none => (fun _ : Unit => (0 : Nat)) <$> view (α := Unit) addr sel args

@[simp] theorem callAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  rfl

@[simp] theorem viewAsNat_word (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (S := S) (X := X) (E := E) (α := Nat) addr sel args :=
  rfl

@[simp] theorem boolBit_true : boolBit true = 1 := rfl
@[simp] theorem boolBit_false : boolBit false = 0 := rfl

@[simp] theorem boolBit_eq_one (b : Bool) : (boolBit b = 1) = (b = true) := by
  cases b <;> simp [boolBit]

@[simp] theorem boolBit_beq_one (b : Bool) : (boolBit b == 1) = b := by
  cases b <;> rfl

/-- `require (ok = true)` is the Core bit-test `require (boolBit ok = 1)`. -/
theorem require_bool_eq_true_iff_bit (b : Bool) (err : ε) :
    require (S := S) (X := X) (E := E) (b = true) err =
      require (boolBit b = 1) err := by
  cases b <;> rfl

/-- Recover a `Bool` CALL from the Core-word wrapper. -/
theorem map_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  simp only [callAsNat]
  rw [map_eq_pure_bind, bind_map]
  simp only [natToBool_boolBit]
  exact bind_pure _

/-- `Tx.call` at `Bool` is `natToBool <$> callAsNat .boolOpt` (`n ≠ 0`). -/
theorem call_bool (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  (map_callAsNat_bool addr sel args).symm

/-- Recover a `Bool` view from the Core-word wrapper. -/
theorem map_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  simp only [viewAsNat]
  rw [map_eq_pure_bind, bind_map]
  simp only [natToBool_boolBit]
  exact bind_pure _

/-- `Tx.view` at `Bool` is `natToBool <$> viewAsNat .boolOpt`. -/
theorem view_bool (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args =
      natToBool <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args :=
  (map_viewAsNat_bool addr sel args).symm

/-- Bind form of `map_callAsNat_bool` (`simp` may rewrite `<$>` to `>>= pure`). -/
theorem bind_callAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      call (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_callAsNat_bool addr sel args

theorem bind_viewAsNat_bool (addr : Address) (sel : Nat) (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => pure (natToBool n)) =
      view (S := S) (X := X) (E := E) (α := Bool) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_viewAsNat_bool addr sel args

@[simp] theorem encode_address (a : Address) :
    AbiType.encode a = Address.toWord a :=
  rfl

@[simp] theorem encode_amount {a : Asset} (x : Amount a) :
    AbiType.encode x = Amount.raw x :=
  rfl

@[simp] theorem encode_word (w : Word) : AbiType.encode w = w :=
  rfl

/-- `Address.toWord` is the identity; CALL targets from Core env atoms use it. -/
theorem callAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      callAsNat ret addr sel args :=
  rfl

theorem viewAsNat_addr (ret : AbiRet) (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr.toWord sel args =
      viewAsNat ret addr sel args :=
  rfl

/-- Recover an `Amount` CALL from the Core-word wrapper. -/
theorem map_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      call (α := Amount a) addr sel args := by
  funext ctx w
  change Tx.run (Amount.ofWord (a := a) <$>
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args) ctx w =
    Tx.run (call (α := Amount a) addr sel args) ctx w
  simp only [callAsNat]
  rw [run_map, run_call (α := Nat), run_call (α := Amount a)]
  cases w.oracle.call addr sel args w.ext with
  | none => rfl
  | some p =>
    rcases p with ⟨rets, _x'⟩
    match rets with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- Recover an `Amount` view from the Core-word wrapper. -/
theorem map_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    Amount.ofWord (a := a) <$>
        viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args =
      view (α := Amount a) addr sel args := by
  funext ctx w
  change Tx.run (Amount.ofWord (a := a) <$>
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args) ctx w =
    Tx.run (view (α := Amount a) addr sel args) ctx w
  simp only [viewAsNat]
  rw [run_map, run_view (α := Nat), run_view (α := Amount a)]
  match w.oracle.view addr sel args w.ext with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- Bind form of `map_viewAsNat_amount`. -/
theorem bind_viewAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      view (α := Amount a) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_viewAsNat_amount addr sel args

/-- Bind form of `map_callAsNat_amount`. -/
theorem bind_callAsNat_amount {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) :
    callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun n => pure (Amount.ofWord (a := a) n)) =
      call (α := Amount a) addr sel args := by
  rw [← map_eq_pure_bind]
  exact map_callAsNat_amount addr sel args

/-- `f <$> (x >>= k)` with an Amount wrapper; named so certificate `simp` matches
after `Core.denote` of a `letOp` sequence. -/
theorem map_bind_ofWord {a : Asset} {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    Amount.ofWord (a := a) <$> (x >>= k) =
      x >>= fun b => Amount.ofWord (a := a) <$> k b :=
  map_bind (Amount.ofWord (a := a)) x k

/-- `natToBool <$> (x >>= k)` after `Core.denote` of a Bool-returning sequence. -/
theorem map_bind_natToBool {β : Type} (x : Tx S X E ε β)
    (k : β → Tx S X E ε Nat) :
    natToBool <$> (x >>= k) = x >>= fun b => natToBool <$> k b :=
  map_bind natToBool x k

/-- Push `ofWord` through `selfAddress >>= viewAsNat` (view after a storage load).
`addr` is `Nat` so `simp` matches Core `load (S → Nat)` binders; `Address := Nat`. -/
theorem map_bind_viewAsNat_amount {a : Asset} {β : Type}
    (x : Tx S X E ε β) (addr : Nat) (sel : Nat) (args : β → List Word) :
    Amount.ofWord (a := a) <$>
        (x >>= fun v => viewAsNat (S := S) (X := X) (E := E) (ε := ε)
          .word addr sel (args v)) =
      x >>= fun v => view (α := Amount a) addr sel (args v) := by
  rw [map_bind_ofWord]
  refine congrArg (fun k => x >>= k) ?_
  funext v
  exact map_viewAsNat_amount addr sel (args v)

/-- `Address.toWord` is the identity; Core env atoms of `selfAddress` omit it. -/
theorem view_toWord_arg {a : Asset} (addr : Address) (sel : Nat) (v : Address) :
    view (S := S) (X := X) (E := E) (ε := ε) (α := Amount a) addr sel [v.toWord] =
      view (α := Amount a) addr sel [v] :=
  rfl

/-- After `map_bind_ofWord`, ofWord sits on the inner `selfAddress >>= viewAsNat`. -/
theorem bind_load_inner_viewAsNat_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load proj >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  refine congrArg (fun k => load proj >>= k) ?_
  funext addr
  exact map_bind_viewAsNat_amount (a := a) (S := S) (X := X) (E := E) (ε := ε)
    selfAddress addr sel (fun me => [me])

/-- Same as `bind_load_inner_viewAsNat_amount` with an `Address` projection
(`Address := Nat`, but `simp` keys on the binder type). -/
theorem bind_load_inner_viewAsNat_amount_addr {a : Asset}
    (proj : S → Address) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load proj >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] :=
  bind_load_inner_viewAsNat_amount (fun σ => proj σ) sel

/-- Schema `getD` form of `bind_load_inner_viewAsNat_amount`. -/
theorem bind_load_getD_inner_viewAsNat_amount {a : Asset}
    (p : S → Nat) (rest : List (S → Nat)) (d : S → Nat) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε) (List.getD (p :: rest) 0 d) >>=
        fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load p >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  have hproj : List.getD (p :: rest) 0 d = p := rfl
  rw [hproj]
  exact bind_load_inner_viewAsNat_amount p sel

/-- `getD [p, q]` with `Address` projections, as `lsc_schema` pretty-prints them. -/
theorem bind_load_getD_pair_addr_view_amount {a : Asset}
    (p q : S → Address) (sel : Nat) :
    (load (S := S) (X := X) (E := E) (ε := ε)
        (List.getD [p, q] 0 (fun _ => (0 : Address))) >>= fun addr =>
      Amount.ofWord (a := a) <$>
        (selfAddress >>= fun me =>
          viewAsNat .word addr sel [me])) =
    load p >>= fun addr =>
      selfAddress >>= fun me =>
        view (α := Amount a) addr sel [me] := by
  have hproj : List.getD [p, q] 0 (fun _ => (0 : Address)) = p := rfl
  rw [hproj]
  exact bind_load_inner_viewAsNat_amount_addr p sel

/-- Load a callee address, then `selfAddress`, then an Amount view. -/
theorem load_selfAddress_view_amount {a : Asset} (proj : S → Nat) (sel : Nat) :
    Amount.ofWord (a := a) <$>
        (load (S := S) (X := X) (E := E) (ε := ε) proj >>= fun addr =>
          selfAddress >>= fun me =>
            viewAsNat .word addr sel [me]) =
      load proj >>= fun addr =>
        selfAddress >>= fun me =>
          view (α := Amount a) addr sel [me.toWord] := by
  rw [map_bind_ofWord]
  trans (load proj >>= fun addr =>
    selfAddress >>= fun me =>
      view (S := S) (X := X) (E := E) (ε := ε) (α := Amount a) addr sel [me])
  · exact bind_load_inner_viewAsNat_amount (a := a) proj sel
  · refine congrArg (fun k => load proj >>= k) ?_
    funext addr
    refine congrArg (fun k => selfAddress >>= k) ?_
    funext me
    exact (view_toWord_arg (a := a) addr sel me).symm

/-- `require (ok = true)` after a Bool CALL is the Core `boolOpt` bit-test. -/
theorem callAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) := by
  have hreq :
      (fun ok : Bool => require (S := S) (X := X) (E := E) (ok = true) err) =
        fun ok => require (boolBit ok = 1) err := by
    funext ok
    exact require_bool_eq_true_iff_bit ok err
  rw [hreq]
  simp only [callAsNat]
  exact (bind_map boolBit (call (α := Bool) addr sel args)
    (fun n => require (n = 1) err)).symm

/-- `require (ok = true)` after a Bool view is the Core `boolOpt` bit-test. -/
theorem viewAsNat_bool_bind_require (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err) := by
  have hreq :
      (fun ok : Bool => require (S := S) (X := X) (E := E) (ok = true) err) =
        fun ok => require (boolBit ok = 1) err := by
    funext ok
    exact require_bool_eq_true_iff_bit ok err
  rw [hreq]
  simp only [viewAsNat]
  exact (bind_map boolBit (view (α := Bool) addr sel args)
    (fun n => require (n = 1) err)).symm

/-- `require (ok = true)` then a continuation after a Bool CALL. -/
theorem callAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) := by
  have h := callAsNat_bool_bind_require (S := S) (X := X) (E := E)
    addr sel args err
  rw [← bind_assoc, h, bind_assoc]

/-- `require (ok = true)` then a continuation after a Bool view. -/
theorem viewAsNat_bool_bind_require_bind {β : Type} (addr : Address) (sel : Nat)
    (args : List Word) (err : ε) (k : Tx S X E ε β) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun ok => require (ok = true) err >>= fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun n => require (n = 1) err >>= fun _ => k) := by
  have h := viewAsNat_bool_bind_require (S := S) (X := X) (E := E)
    addr sel args err
  rw [← bind_assoc, h, bind_assoc]

/-- Discarded Bool CALL: Core `boolOpt` vs surface `Bool`. -/
theorem callAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    call (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) := by
  simp only [callAsNat]
  rw [bind_map]

/-- Discarded Bool view: Core `boolOpt` vs surface `Bool`. -/
theorem viewAsNat_bool_bind_unit (addr : Address) (sel : Nat) (args : List Word) :
    view (S := S) (X := X) (E := E) (α := Bool) addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .boolOpt addr sel args >>=
        (fun _ => (pure () : Tx S X E ε Unit)) := by
  simp only [viewAsNat]
  rw [bind_map]

/-- Discarded Amount view: Core `word` vs surface `Amount`. -/
theorem viewAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    view (α := Amount a) addr sel args >>= (fun _ => k) =
      viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) := by
  funext ctx w
  change Tx.run (view (α := Amount a) addr sel args >>= fun _ => k) ctx w =
    Tx.run (viewAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
      fun _ => k) ctx w
  simp only [viewAsNat]
  rw [run_bind, run_bind, run_view (α := Amount a), run_view (α := Nat)]
  match w.oracle.view addr sel args w.ext with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- Discarded Amount CALL: Core `word` vs surface `Amount`. -/
theorem callAsNat_word_bind_const {β} {a : Asset} (addr : Address) (sel : Nat)
    (args : List Word) (k : Tx S X E ε β) :
    call (α := Amount a) addr sel args >>= (fun _ => k) =
      callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
        (fun _ => k) := by
  funext ctx w
  change Tx.run (call (α := Amount a) addr sel args >>= fun _ => k) ctx w =
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) .word addr sel args >>=
      fun _ => k) ctx w
  simp only [callAsNat]
  rw [run_bind, run_bind, run_call (α := Amount a), run_call (α := Nat)]
  cases w.oracle.call addr sel args w.ext with
  | none => rfl
  | some p =>
    rcases p with ⟨rets, _x'⟩
    match rets with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- A successful `callAsNat` leaves `self` unchanged. -/
theorem callAsNat_self (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.self = w.self := by
  cases ret with
  | word => exact call_self (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_self (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_self (α := Unit) addr sel args hrun

/-- A successful `callAsNat` leaves the oracle unchanged. -/
theorem callAsNat_oracle (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (callAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w'.oracle = w.oracle := by
  cases ret with
  | word => exact call_oracle (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_oracle (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [callAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (call (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact call_oracle (α := Unit) addr sel args hrun

/-- A successful `viewAsNat` returns the pre-world. -/
theorem viewAsNat_world (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (viewAsNat (S := S) (X := X) (E := E) (ε := ε) ret addr sel args) ctx w =
        .ok (v, w') →
      w' = w := by
  cases ret with
  | word => exact view_world (α := Nat) addr sel args
  | boolOpt =>
    intro h
    simp only [viewAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (view (S := S) (X := X) (E := E) (α := Bool) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact view_world (α := Bool) addr sel args hrun
  | none =>
    intro h
    simp only [viewAsNat] at h
    rw [run_map] at h
    cases hrun :
        Tx.run (view (S := S) (X := X) (E := E) (α := Unit) addr sel args) ctx w with
    | error _ =>
      rw [hrun] at h; cases h
    | ok p =>
      rw [hrun] at h
      cases h
      exact view_world (α := Unit) addr sel args hrun

end Tx

/-! ### `read` / `write` elaborators

`Amount` / `*.Ref` fields are stored as words in Core. The sugar elaborates to
the same `ofWord` / `.raw` (and `{ addr := · }` / `.addr`) wrappers the schema
uses, so `lsc_reify` certificates close. -/
namespace Syntax
open Lean Elab Term Meta PrettyPrinter

private def isAmount : Expr → Bool := fun ty => ty.isAppOf ``Lsc.Amount
/-- Per-interface `I.Ref` (and any leftover `Lsc.Ref`) is a one-field address. -/
private def isRef (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some n => n.getString! == "Ref"
  | none => false

/-- Storage type `S` of an expected `Tx S _ _ _ _` (or its `ReaderT` unfold). -/
def txStorage? (ty? : Option Expr) : TermElabM (Option Expr) := do
  let some ty0 := ty? | return none
  let ty ← instantiateMVars ty0
  -- Reducible only: unfold `M` / `Tx`, not `StateT`.
  let ty ← withReducible (whnf ty)
  if ty.isAppOf ``Lsc.Tx then return some (ty.getArg! 0)
  if ty.isAppOf ``ReaderT then
    let st := ty.getArg! 1
    if st.isAppOf ``StateT then
      let w ← withReducible (whnf (st.getArg! 0))
      if w.isAppOf ``Lsc.World then return some (w.getArg! 0)
  return none

def elabFieldProj (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  let some S ← txStorage? expectedType? |
    throwError "read/write: could not infer storage type (use in a `Tx` context)"
  let α ← mkFreshExprMVar none
  let expected ← mkArrow S α
  elabTerm (← `(fun $(sigma) => $(projOf f))) expected

/-- Value type of storage field `f` (scalar / map1 / map2). -/
def fieldValTy (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun _ body =>
    whnfD body

/-- Number of mapping keys `f` expects (0 = scalar). -/
def fieldKeyCount (f : Ident) (expectedType? : Option Expr) : TermElabM Nat := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun xs _ =>
    return xs.size - 1

def wrapLoad (α : Expr) (load : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let α ← whnfD α
  if isRef α then
    let tyStx ← delab α
    elabTerm (← `(Functor.map (fun n : Nat => ({ addr := n } : $tyStx)) $load))
      expectedType?
  else
    elabTerm load expectedType?

@[term_elab lscRead]
def elabRead : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(read $f:ident) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "read: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    let load ←
      if isRef (← whnfD α) then
        `(Lsc.Tx.load (fun $(sigma) =>
            (($(← fieldProj f α)).addr : Nat)))
      else
        `(Lsc.Tx.load (fun $(sigma) => $(← fieldProj f α)))
    wrapLoad α load expectedType?
  | `(read $f:ident [ $ks:term,* ]) => do
    let keys := ks.getElems
    let n ← fieldKeyCount f expectedType?
    unless n == keys.size do
      throwError "read: `{f.getId}` expects {n} key(s)"
    let α ← fieldValTy f expectedType?
    match keys.toList with
    | [k] =>
      let kk := mkIdent `k
      let load ←
        if isRef (← whnfD α) then
          `(Lsc.Tx.loadMap (fun $(sigma) $kk =>
            (($(← fieldProjKey f kk α)).addr : Nat)) $k)
        else
          `(Lsc.Tx.loadMap (fun $(sigma) $kk =>
            $(← fieldProjKey f kk α)) $k)
      wrapLoad α load expectedType?
    | [k₁, k₂] =>
      let a := mkIdent `k₁
      let b := mkIdent `k₂
      let load ←
        if isRef (← whnfD α) then
          `(Lsc.Tx.loadMap2 (fun $(sigma) $a $b =>
            (($(← fieldProjKey2 f a b α)).addr : Nat)) $k₁ $k₂)
        else
          `(Lsc.Tx.loadMap2 (fun $(sigma) $a $b =>
            $(← fieldProjKey2 f a b α)) $k₁ $k₂)
      wrapLoad α load expectedType?
    | _ => throwError "read: mappings have one or two keys"
  | _ => throwUnsupportedSyntax

where
  fieldProj (f : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p)
  fieldProjKey (f k : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p $k)
  fieldProjKey2 (f k₁ k₂ : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p $k₁ $k₂)

@[term_elab lscWrite]
def elabWrite : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(write $f:ident $v) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "write: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    elabTerm (← storeScalar f α v) expectedType?
  | `(write $f:ident [ $ks:term,* ] $v) => do
    let keys := ks.getElems
    let n ← fieldKeyCount f expectedType?
    unless n == keys.size do
      throwError "write: `{f.getId}` expects {n} key(s)"
    let α ← fieldValTy f expectedType?
    match keys.toList with
    | [k] => elabTerm (← storeMap1 f α k v) expectedType?
    | [k₁, k₂] => elabTerm (← storeMap2 f α k₁ k₂ v) expectedType?
    | _ => throwError "write: mappings have one or two keys"
  | _ => throwUnsupportedSyntax

where
  storeScalar (f : Ident) (α : Expr) (v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    if isAmount α then
      let tyStx ← delab α
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := Lsc.Amount.ofWord m })
          (Lsc.Amount.raw ($v : $tyStx)))
    else if isRef α then
      let tyStx ← delab α
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := { addr := m } })
          (($v : $tyStx).addr))
    else
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := m }) $v)
  storeMap1 (f : Ident) (α : Expr) (k v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    let p := projOf f
    let kk := mkIdent `k
    let mm := mkIdent `m
    if isAmount α then
      `(Lsc.Tx.storeMap (fun $σ $kk => Lsc.Amount.raw ($p $kk))
          (fun $σ $mm => { $σ with $f:ident := fun $kk => Lsc.Amount.ofWord ($mm $kk) })
          $k (Lsc.Amount.raw $v))
    else if isRef α then
      `(Lsc.Tx.storeMap (fun $σ $kk => ($p $kk).addr)
          (fun $σ $mm => { $σ with $f:ident := fun $kk => { addr := $mm $kk } })
          $k ($v).addr)
    else
      `(Lsc.Tx.storeMap (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm }) $k $v)
  storeMap2 (f : Ident) (α : Expr) (k₁ k₂ v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    let p := projOf f
    let a := mkIdent `k₁
    let b := mkIdent `k₂
    let mm := mkIdent `m
    if isAmount α then
      `(Lsc.Tx.storeMap2 (fun $σ $a $b => Lsc.Amount.raw ($p $a $b))
          (fun $σ $mm => { $σ with $f:ident := fun $a $b => Lsc.Amount.ofWord ($mm $a $b) })
          $k₁ $k₂ (Lsc.Amount.raw $v))
    else if isRef α then
      `(Lsc.Tx.storeMap2 (fun $σ $a $b => ($p $a $b).addr)
          (fun $σ $mm => { $σ with $f:ident := fun $a $b => { addr := $mm $a $b } })
          $k₁ $k₂ ($v).addr)
    else
      `(Lsc.Tx.storeMap2 (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
          $k₁ $k₂ $v)

end Syntax

end Lsc
