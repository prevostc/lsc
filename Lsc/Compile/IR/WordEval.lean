import Lsc.Compile.IR
import EvmYul.UInt256

namespace Lsc.Compile.IR

open Lsc (Ident)

abbrev Word := EvmYul.UInt256

inductive Halt where
  | running
  | returned (value : Word)
  | reverted (selector : Nat)
  deriving Repr, DecidableEq

/-- EVM-word semantics for the pure view fragment. Unsupported effects return `none` rather than
silently receiving reference semantics. -/
structure WordState where
  locals : Ident → Option Word := fun _ => none
  slots : Nat → Word := fun _ => .ofNat 0
  calldata : Nat → Word := fun _ => .ofNat 0
  halt : Halt := .running

namespace WordState

def lookupLocal (st : WordState) (name : Ident) : Word :=
  (st.locals name).getD (.ofNat 0)

def setLocal (st : WordState) (name : Ident) (value : Word) : WordState :=
  { st with locals := fun other => if other == name then some value else st.locals other }

def setSlot (st : WordState) (slot : Nat) (value : Word) : WordState :=
  { st with slots := fun other => if other == slot then value else st.slots other }

end WordState

/-- Encode an EVM boolean as a word. -/
def boolWord (b : Bool) : Word :=
  .ofNat (if b then 1 else 0)

def evalExprWord (st : WordState) : Expr → Option Word
  | .lit n => some (.ofNat n)
  | .local name => some (st.lookupLocal name)
  | .sload slot => some (st.slots slot)
  | .mapSlot .. | .mapSlot2 .. => none
  | .dynSload slot => do
      let slot ← evalExprWord st slot
      some (st.slots slot.toNat)
  | .calldataWord offset => some (st.calldata offset)
  | .add a b => return EvmYul.UInt256.add (← evalExprWord st a) (← evalExprWord st b)
  | .sub a b => return EvmYul.UInt256.sub (← evalExprWord st a) (← evalExprWord st b)
  | .mul a b => return EvmYul.UInt256.mul (← evalExprWord st a) (← evalExprWord st b)
  | .div a b => return EvmYul.UInt256.div (← evalExprWord st a) (← evalExprWord st b)
  | .lt a b => return boolWord ((← evalExprWord st a) < (← evalExprWord st b))
  | .eq a b => return boolWord ((← evalExprWord st a) == (← evalExprWord st b))
  | .isZero a => return boolWord ((← evalExprWord st a) == .ofNat 0)
  | .gt a b => return boolWord ((← evalExprWord st a) > (← evalExprWord st b))
  | .shr amount value =>
      return EvmYul.UInt256.shiftRight (← evalExprWord st value) (← evalExprWord st amount)
  | .xor a b => return EvmYul.UInt256.xor (← evalExprWord st a) (← evalExprWord st b)

def evalStmtWord (st : WordState) : Stmt → Option WordState
  | .skip => some st
  | .seq first rest => do
      let st ← evalStmtWord st first
      match st.halt with
      | .running => evalStmtWord st rest
      | _ => some st
  | .letBind name value => do
      some (st.setLocal name (← evalExprWord st value))
  | .sstore slot value => do
      some (st.setSlot slot (← evalExprWord st value))
  | .sstoreDyn slot value => do
      let slot ← evalExprWord st slot
      let value ← evalExprWord st value
      some (st.setSlot slot.toNat value)
  | .ifRevertSelector cond selector => do
      let cond ← evalExprWord st cond
      if cond == .ofNat 1 then some { st with halt := .reverted selector } else some st
  | .revertSelector selector => some { st with halt := .reverted selector }
  | .ret value => do
      some { st with halt := .returned (← evalExprWord st value) }
  | .log .. | .checkReentrancyLock .. | .setReentrancyLock ..
  | .externalCall .. | .externalCallBind .. | .staticCall .. | .staticCallBind .. => none

end Lsc.Compile.IR
