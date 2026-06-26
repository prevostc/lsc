namespace LscV1

inductive ArithError where
  | overflow
  | divisionByZero
  deriving DecidableEq, Repr

inductive ContractError (E : Type) where
  | contract : E → ContractError E
  | arith    : ArithError → ContractError E
  deriving Repr

class LscError (E : Type) where
  arith : ArithError → E

instance : LscError ArithError where
  arith := id

end LscV1
