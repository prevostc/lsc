[ ] evaluate if we should add Optional<Address> to replace Address 0
[ ] reentrancy lock is cumbersome, define better
[ ] define public/private variables access
[ ] implement math decorator extension
[ ] implement constrained types extensions
[ ] rework comments (too blobby)
[ ] syntax delab, make sure errors are amazing
[ ] make sure no user-land code is referenced in the framework lib (incrementBody, increment_body_lowers_ok)
[ ] compilation proofs 
[ ] handle proofs against oracle manipulation attacks 
[ ] handle proofs against sandwitch attacks
[ ] handle proofs against flashloans attacks
[ ] real "interface" concept for exec/read call sites: opt-in per-call-site declaration of a
    callee's assumed function signatures/events/errors/extra theorems, richer than a Solidity
    interface, for stronger proofs than the fully black-box ExternalCallFailed/no-events
    default (see docs/reference/INTERFACES.md)
[ ] general address-indexed N-contract dispatch registry (WorldSpec/HonestWorld-style) with
    real ABI-encoded calldata, replacing exec/read's "one statically-named callee type" scope
[ ] wire exec/read end-to-end to the real IR.Stmt.safeExternalCall/Yul codegen that already
    exists (Lsc/Compile/IR.lean, Yul.lean, SafeExternalCallTest.lean): extend
    Lsc/Compile/Lower.lean to lower a genuinely two-contract ContractDef and generate real
    ABI-encoded calldata for a tx's actual arguments (depends on the N-contract registry item
    above for a real target address)
[ ] once exec/read are wired to safeExternalCall (above), (re-)design a real Lean-level signal
    for "callee returned ABI-encoded false" (the non-compliant-ERC20 case safeExternalCall's
    checkBoolReturn already reverts on at the bytecode level, docs/reference/ESCROW.md) — not
    necessarily as a FrameworkError case; a prior placeholder constructor
    (FrameworkError.ExternalCallReturnedFalse) was removed for being unconnected to any real
    Lean semantics or theorem
[ ] approve/transferFrom for Token (needs a double-keyed Address -> Address -> Wad allowance
    mapping; current mapping storage only supports single-keyed Address -> Wad)
[ ] generalize Lang/Derive.lean's FieldKind/Wad.Expr pipeline to real per-decimals scaling (today
    only Fixed 18 (= Wad) is accepted by the tx/storage-field grammar, Lsc.Deriving.
    fieldKindOfExpr's docstring) so a genuinely non-18-decimals token (e.g. Fixed 6) can be
    authored directly in the DSL instead of as a hand-written ContractM contract
