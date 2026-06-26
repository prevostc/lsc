import LscV2.Types

namespace LscV2

/-- Linear type stubs — enforcement deferred to later phases. -/
structure TokenAmount where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

structure Allowance where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

structure FlashLoanReceipt where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

structure Lock where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

structure Capability where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

structure PositionTicket where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

end LscV2
