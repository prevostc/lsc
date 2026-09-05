# 0006: `deriving` handlers replaced the bespoke `ContractGen` codegen

## Context

Storage/error/event glue (`getField`/`setField`/`resolveError`/`buildEvent`, plus dispatch
codegen) was originally synthesized by `ContractGen.lean`, from a bespoke custom-syntax parse
tree, via a `contract … where` macro. That macro had to hand-build raw `Syntax.node` trees to
dodge a tokeniser conflict with the (also since-superseded, see
[`0001`](0001-txm-superseded-by-syntax.md)) custom `lsc_*` syntax categories it lived alongside.

## Decision

Three real `deriving` handlers (`deriving ContractStorage`/`ContractEvent`/`ContractError`),
attached directly to plain `structure`/`inductive` declarations, plus one small
`derive_contract_dsl` assembly command, replace `ContractGen`'s codegen entirely
(`Lsc/Lang/Derive.lean`). Because this file imports neither the old `Syntax.lean`/`Contract.lean`
nor `ContractGen.lean`, plain Lean quasiquotes work normally, and `Lean.Elab.
registerDerivingHandler`'s ordinary introspection (`getStructureFields`, `getConstInfoInduct`,
`getConstInfoCtor`) is enough once the `structure`/`inductive` is elaborated.

## Consequences

`ContractGen.lean`/`Contract.lean` (the old custom-syntax pipeline) were deleted once this
migration completed; they no longer exist in the tree. One resolved implementation wrinkle worth
recording: `Address` and `UInt256` are both literally `abbrev`s for `Word := BitVec 256`, so a
fully-`whnf`'d field type can't distinguish them — but a structure's field-projection type, as
stored in the `ConstantInfo` Lean records when elaborating the `structure`, is *not*
auto-unfolded through reducible `abbrev`s (verified empirically against this project's Lean
toolchain). `fieldKindOfExpr` (`Lsc/Lang/Derive.lean`) relies on exactly this and never calls
`whnf`, so it can tell `Address`/`UInt256`/`Wei`/`Bool` apart from the unreduced stored type
alone. A field spelled out as some *other* alias of `BitVec 256` is rejected with a clear
"unsupported field type" error at `deriving` time, rather than silently miscategorized.
