import Lsc.Lang.Amount
import Lsc.Lang.AmountAlgebra
import Lsc.Security.InvariantTheorems

/-!
Public surface of a deployed contract: `State C` is a world the contract can
actually be in, and `Txs w` is any sequence of calls by anyone plus
environment steps the spec's `HasRely` permits. `spent` is defined per
example as a fold over accepted calls. `Reachable` / `Wf` / `RelyAlong`
stay internal.
-/

namespace Lsc.Security

variable {S X E ε : Type}

/-- A state of the deployed contract: anything it can be in after
deployment and any sequence of transactions by anyone. -/
structure State (C : Spec S X E ε)
    [HasCreditValue X] [HasPayable C] [HasSelfBalance X] [HasDeploy C]
    [HasRely C] where
  w : World S X E
  addr : Address
  reachable :
    Reachable (S := S) (X := X) (E := E) (ε := ε) (C := C)
      (HasRely.rely (C := C) addr) addr w

variable {C : Spec S X E ε}
variable [HasCreditValue X] [HasPayable C] [HasSelfBalance X] [HasDeploy C]
variable [HasRely C]

/-- Underlying world. Tried as a coercion; if instance search sticks, use `.w`. -/
@[coe] def State.toWorld (s : State C) : World S X E := s.w

instance : CoeOut (State C) (World S X E) := ⟨State.toWorld⟩

/-- A message to the contract in state `w`: a sender other than the contract
itself, and the value sent. -/
structure Msg (w : State C) where
  sender : Address
  value : Nat := 0
  notSelf : sender ≠ w.addr

/-- Unpack a message into the `Tx` context at this state's callee. -/
@[coe] def Msg.toCtx {w : State C} (m : Msg w) : Ctx where
  sender := m.sender
  value := m.value
  self := w.addr

/-- So `Tx.run f msg w` elaborates when `msg : Msg w`. -/
instance {w : State C} : CoeOut (Msg w) Ctx := ⟨Msg.toCtx⟩

@[simp] theorem Msg.toCtx_sender {w : State C} (m : Msg w) :
    m.toCtx.sender = m.sender := rfl

@[simp] theorem Msg.toCtx_value {w : State C} (m : Msg w) :
    m.toCtx.value = m.value := rfl

@[simp] theorem Msg.toCtx_self {w : State C} (m : Msg w) :
    m.toCtx.self = w.addr := rfl

/-- Storage of the executing contract. -/
def State.self (s : State C) : S := s.w.self

/-- Native-balance projection, only for chain profiles with a native asset. -/
class HasNative (C : Spec S ExtState E ε) where
  asset : Asset

def State.nativeBalance {S E ε : Type} {C : Spec S ExtState E ε}
    [HasCreditValue ExtState] [HasPayable C] [HasSelfBalance ExtState]
    [HasDeploy C] [HasRely C] [HasNative C]
    (s : State C) : Amount (HasNative.asset (C := C)) :=
  ⟨World.nativeBalance s.w⟩

/-- World after one call targeting this contract. -/
def State.afterCall (s : State C) (c : Call C) (hne : c.sender ≠ s.addr) :
    State C :=
  let tr := [Step.call c]
  { w := run s.addr tr s.w
    addr := s.addr
    reachable :=
      reachable_run (tr := tr) s.reachable
        (by
          change External s.addr tr
          exact And.intro hne True.intro)
        (by
          exact True.intro) }

/-- World after an environment step permitted by `HasRely`. -/
def State.afterEnv (s : State C) (x' : X)
    (hr : HasRely.rely (C := C) s.addr s.w x') : State C :=
  let tr := [Step.env x']
  { w := run s.addr tr s.w
    addr := s.addr
    reachable :=
      reachable_run (tr := tr) s.reachable
        (by
          change External s.addr tr
          exact True.intro)
        (by
          exact And.intro hr True.intro) }

/-- Transactions after `w`: any calls by anyone, and anything other contracts
do in between. The call constructor carries `sender ≠ self`; the env
constructor carries the spec's rely proof. -/
inductive Txs : State C → Type where
  | nil {s} : Txs s
  | call {s} (c : Call C) (hne : c.sender ≠ s.addr)
      (rest : Txs (s.afterCall c hne)) : Txs s
  | env {s} (x' : X) (hr : HasRely.rely (C := C) s.addr s.w x')
      (rest : Txs (s.afterEnv x' hr)) : Txs s

/-- The world after this transaction sequence. -/
def Txs.end : {s : State C} → Txs s → State C
  | s, .nil => s
  | _, .call _ _ rest => rest.end
  | _, .env _ _ rest => rest.end

@[simp] theorem State.afterCall_w (s : State C) (c : Call C)
    (hne : c.sender ≠ s.addr) :
    (s.afterCall c hne).w = step s.addr (.call c) s.w := rfl

@[simp] theorem State.afterCall_addr (s : State C) (c : Call C)
    (hne : c.sender ≠ s.addr) :
    (s.afterCall c hne).addr = s.addr := rfl

@[simp] theorem State.afterEnv_self (s : State C) (x' : X)
    (hr : HasRely.rely (C := C) s.addr s.w x') :
    (s.afterEnv x' hr).self = s.self := rfl

@[simp] theorem State.afterEnv_addr (s : State C) (x' : X)
    (hr : HasRely.rely (C := C) s.addr s.w x') :
    (s.afterEnv x' hr).addr = s.addr := rfl

@[simp] theorem Txs.end_nil (s : State C) : Txs.end (.nil : Txs s) = s := rfl

@[simp] theorem Txs.end_call {s : State C} (c : Call C)
    (hne : c.sender ≠ s.addr) (rest : Txs (s.afterCall c hne)) :
    Txs.end (.call c hne rest) = rest.end := rfl

@[simp] theorem Txs.end_env {s : State C} (x' : X)
    (hr : HasRely.rely (C := C) s.addr s.w x') (rest : Txs (s.afterEnv x' hr)) :
    Txs.end (.env x' hr rest) = rest.end := rfl

/-- Fold `f` over accepted calls, left to right, at the pre-call world. -/
def Txs.foldAccepted {α : Type} (f : α → Call C → World S X E → α) (init : α) :
    ∀ {s : State C}, Txs s → α
  | _, .nil => init
  | s, .call c _hne rest =>
    foldAccepted f (if accepted s.addr c s.w then f init c s.w else init) rest
  | _, .env _ _ rest =>
    foldAccepted f init rest

/-- Per-example outflow on `a`'s authority. `Txs.spent` sums this over
accepted calls. -/
class HasSpent (C : Spec S X E ε) where
  asset : Asset
  spentCall : Address → Call C → Amount asset

/-- Sum over accepted calls of `HasSpent.spentCall a`. -/
def Txs.spent [HasSpent C] {s : State C} (t : Txs s) (a : Address) :
    Amount (HasSpent.asset (C := C)) :=
  t.foldAccepted (fun acc c _ => acc + HasSpent.spentCall (C := C) a c) 0

end Lsc.Security
