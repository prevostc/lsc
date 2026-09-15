/-!
# `[Payable]` / `[Reentrant]` capabilities

Marker classes used as instance binders on contract entrypoints. There are
**no** instances in user space: a helper that asks for `[Payable]` is
callable only from a function that already has the binder. `lsc_contract`
reads the binders and records them on `FnDef`.
-/

set_option warn.classDefReducibility false

namespace Lsc

/-- This entrypoint may receive native value. The dispatcher skips the
`callvalue()` revert. No user instances. `Tx.value` arrives with the
native-asset chain profile (`Chain.native`). -/
class Payable : Prop

/-- This entrypoint does not acquire or release the transient reentrancy
lock. The runtime prologue still `tload`s. No user instances. -/
class Reentrant : Prop

namespace Reentrant

/-- Skip the compile-time store-after-call rejection. Implies `Reentrant`.
No user instances. Same as the old `@[reentrant (unsafe := true)]`. -/
class Unsafe : Prop extends Reentrant

end Reentrant

/-- Witnesses used only by `lsc_contract` when applying an entrypoint
(the dispatcher is the caller). Not for contract authors. -/
def Payable.entrypoint : Payable := ⟨⟩
def Reentrant.entrypoint : Reentrant := ⟨⟩
def Reentrant.Unsafe.entrypoint : Reentrant.Unsafe := {}

end Lsc
