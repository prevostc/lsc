namespace LscV2

/-- The EVM's native word size. All storage values are Word. -/
abbrev Word := BitVec 256

/-- UInt256 is Word. We use UInt256 in type signatures for clarity. -/
abbrev UInt256 := Word

/-- Addresses are 160-bit values but we store them as Word for ABI simplicity. -/
abbrev Address := Word

/-- Storage slot index. -/
abbrev Slot := Word

/-- Variable names in the AST. -/
abbrev Ident := String

end LscV2
