import Lsc.Lang.Word
import Lsc.Lang.Reify
import Stdlib.ERC20

set_option maxHeartbeats 8000000

/-!
# Token — an ERC20 written as plain Lean

Every function is an ordinary definition in the `Tx` monad. There is no custom grammar:
`read`/`write` are macros over the storage primitives, `+?`/`-?` are the checked
arithmetic primitives, and control flow is Lean's own `let`/`if`/`do`.

`lsc_contract … implements IERC20 tokenAsset` checks names and signatures against
`IERC20` and emits `Token.impl`. Nested allowances are a two-key `Mapping`
(`lsc_schema` `map2`); the language supports that shape directly.

Bool-returning IERC20 mutators wrap a Unit body (`transferU` / `transferFromU`)
and `pure true`. `lsc_reify` cannot certify `natToBool <$>` of that mix
(the Bool certificate simp keys on `Tx Nat`, while Core flag programs are
`Tx Flag`), so `transfer.core` / `transferFrom.core` are the Unit cores
with a trailing `pure 1`, and `*.core_denote` is proved from the Unit
certificates. Self-spend in `transferFrom` still requires and decrements
allowance (`IERC20.Spec.transferFrom_allowance` hypothesises `sender ≠ src`).
-/

open Lsc Lsc.Syntax Lsc.Stdlib

namespace Token

/-- This contract's token. Decimals are not static. -/
def tokenAsset : Asset := ⟨`tokenAsset, none⟩

structure Storage where
  owner : Address
  totalSupply : Amount tokenAsset
  balances : Mapping Address (Amount tokenAsset)
  allowances : Mapping Address (Mapping Address (Amount tokenAsset))

inductive Event
  | Transfer (src to : Address) (amount : Amount tokenAsset)
  | Approval (owner spender : Address) (amount : Amount tokenAsset)
  deriving DecidableEq, Repr

inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | NotOwner
  deriving DecidableEq, Repr

abbrev M := Tx Storage ExtState Event Error

/-- Deployment: the deployer owns the whole initial supply. -/
def constructor (owner : Address) (supply : Amount tokenAsset) : M Unit := do
  write owner owner
  write totalSupply supply
  write balances[owner] supply
  Tx.emit (.Transfer 0 owner supply)

/-- Move `amount` from the sender to `to`. -/
def transferU (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write balances[src] (← b -? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer src to amount)

/-- Move `amount` from the sender to `to`. Returns `true` on success. -/
def transfer (to : Address) (amount : Amount tokenAsset) : M Bool := do
  transferU to amount
  pure true

/-- Set the sender's allowance for `spender`. Returns `true` on success. -/
def approve (spender : Address) (amount : Amount tokenAsset) : M Bool := do
  let owner ← Tx.sender
  write allowances[owner, spender] amount
  let _ ← Tx.emit (.Approval owner spender amount)
  pure true

/-- Move `amount` from `src` to `to`, spending `allowances src sender`. Self-spend
(`sender = src`) still requires and decrements that allowance — same as a
self-`approve` plus `transferFrom`. `IERC20.Spec.transferFrom_allowance` is
stated only for `sender ≠ src`, so omitting the self-spend exception is
compatible with the spec. -/
def transferFromU (src to : Address) (amount : Amount tokenAsset) : M Unit := do
  let spender ← Tx.sender
  let a ← read allowances[src, spender]
  Tx.require (amount ≤ a) .InsufficientAllowance
  let b ← read balances[src]
  Tx.require (amount ≤ b) .InsufficientBalance
  write allowances[src, spender] (← a -? amount)
  write balances[src] (← b -? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer src to amount)

/-- Move `amount` from `src` to `to`, spending `allowances src sender`. Returns
`true` on success. See `transferFromU` for the self-spend policy. -/
def transferFrom (src to : Address) (amount : Amount tokenAsset) : M Bool := do
  transferFromU src to amount
  pure true

def mint (to : Address) (amount : Amount tokenAsset) : M Unit := do
  let caller ← Tx.sender
  let owner ← read owner
  Tx.require (caller = owner) .NotOwner
  let supply ← read totalSupply
  write totalSupply (← supply +? amount)
  let r ← read balances[to]
  write balances[to] (← r +? amount)
  Tx.emit (.Transfer 0 to amount)

/-- Burn with an `if` in statement position, to exercise join points. -/
def burn (amount : Amount tokenAsset) : M Unit := do
  let src ← Tx.sender
  let b ← read balances[src]
  if amount ≤ b then
    write balances[src] (← b -? amount)
    let supply ← read totalSupply
    write totalSupply (← supply -? amount)
  else
    Tx.revert .InsufficientBalance
  Tx.emit (.Transfer src 0 amount)

def balanceOf (who : Address) : M (Amount tokenAsset) := read balances[who]

def allowance (owner spender : Address) : M (Amount tokenAsset) :=
  read allowances[owner, spender]

/-- IERC20 `totalSupply` is a `Word` view of the stored amount. -/
def totalSupply : M Word := do
  let s ← read totalSupply
  pure s.raw

/-- Append `pure 1` (ABI `true`) to a Unit Core program. -/
def Core.withTrue : Core .unit → Core .flag
  | .ret _ => .ret (.flag (.lit 1))
  | .stmtTail s => .seq s (.ret (.flag (.lit 1)))
  | .revertTail e args => .revertTail e args
  | .letOp op k => .letOp op (withTrue k)
  | .seq s k => .seq s (withTrue k)
  | .letPure p as k => .letPure p as (withTrue k)
  | .ite c a b => .ite c (withTrue a) (withTrue b)

end Token

lsc_schema Token
lsc_reify Token.constructor Token.transferU Token.approve Token.transferFromU
lsc_reify Token.mint Token.burn
lsc_reify Token.balanceOf Token.allowance Token.totalSupply

namespace Token

private theorem natToBool_bind_pure_one {S X E ε : Type}
    (u : Tx S X E ε Unit) :
    Tx.natToBool <$> (u >>= fun _ => (pure Flag.on : Tx S X E ε Flag)) =
      u >>= fun _ => (pure true : Tx S X E ε Bool) := by
  change Tx.natToBool <$> (u >>= fun _ => (pure (1 : Nat) : Tx S X E ε Nat)) =
    u >>= fun _ => pure true
  rw [Tx.map_bind_natToBool (k := fun _ => pure (1 : Nat))]
  refine congrArg (Bind.bind u) ?_
  funext _
  rw [Tx.map_pure]
  rfl

theorem denote_withTrue {S X E ε : Type} (Γ : ContractSchema S X E ε)
    (c : Core .unit) (env : List Nat) :
    Core.denote Γ (Core.withTrue c) env =
      Core.denote Γ c env >>= fun _ => (pure Flag.on : Tx S X E ε Flag) := by
  match c with
  | .ret _ =>
    simp [Core.withTrue, Core.denote]; rfl
  | .stmtTail s =>
    simp [Core.withTrue, Core.denote]; rfl
  | .revertTail e args =>
    simp [Core.withTrue, Core.denote]
    funext ctx w
    rfl
  | .letOp op k =>
    simp [Core.withTrue, Core.denote]
    refine congrArg (Bind.bind (Op.denote Γ env op)) ?_
    funext v
    exact denote_withTrue Γ k (v :: env)
  | .seq s k =>
    simp [Core.withTrue, Core.denote]
    refine congrArg (Bind.bind (Stmt.denote Γ env s)) ?_
    funext _
    exact denote_withTrue Γ k env
  | .letPure p as k =>
    simpa [Core.withTrue, Core.denote] using denote_withTrue Γ k _
  | .ite c a b =>
    simp [Core.withTrue, Core.denote]
    split
    · exact denote_withTrue Γ a env
    · exact denote_withTrue Γ b env

@[reducible] def transfer.core : Core .flag := Core.withTrue transferU.core

theorem transfer.core_denote (to : Address) (amount : Amount tokenAsset) :
    Tx.natToBool <$> Core.denote schema transfer.core [amount.raw, to.toWord] =
      transfer to amount := by
  simp only [transfer.core, transfer, denote_withTrue, transferU.core_denote]
  exact natToBool_bind_pure_one _

@[reducible] def transferFrom.core : Core .flag := Core.withTrue transferFromU.core

theorem transferFrom.core_denote (src to : Address) (amount : Amount tokenAsset) :
    Tx.natToBool <$>
        Core.denote schema transferFrom.core
          [amount.raw, to.toWord, src.toWord] =
      transferFrom src to amount := by
  simp only [transferFrom.core, transferFrom, denote_withTrue,
    transferFromU.core_denote]
  exact natToBool_bind_pure_one _

end Token

lsc_contract Token constructor transfer transferFrom approve totalSupply
  balanceOf allowance mint burn
  implements IERC20 Token.tokenAsset
