# 0008: Two earlier custom-syntax/codegen attempts, deleted

## Context

The current framework went through two full implement-then-delete cycles before settling on its
current shape.

**Attempt 1 — a custom `lsc_*` grammar (`Lang/Syntax.lean` v1) + hand-built codegen
(`Lang/Contract.lean`, `Lang/ContractGen.lean`).** Following the dss2024 prior-art design exactly:
`declare_syntax_cat lsc_ty/lsc_expr/lsc_stmt/...` + `macro_rules` for the grammar, and a
`contract … where` command using `elab_rules` to synthesize a storage struct, error/event
inductives, AST defs, and `ContractM` defs all from one parsed custom-syntax body
(`generateStorageStruct`, `generateContractErrorsInstance`, `generateContractMDefs`, etc. in
`Lang/ContractGen.lean`, using hand-built raw `Syntax.node` trees like `mkStructSimpleBinder`,
`mkMatchArm`).

## Decision

Both were fully deleted:

- The custom `lsc_*` grammar was replaced by `Lang/TxM.lean`'s `do`-notation-over-`WriterT`
  builder monad (itself later superseded again — see
  [`0001`](0001-txm-superseded-by-syntax.md)).
- `Lang/Contract.lean`/`Lang/ContractGen.lean`'s codegen was replaced by three independent
  `deriving` handlers (`ContractStorage`/`ContractEvent`/`ContractError`) attached directly to
  plain `structure`/`inductive` declarations, plus one small `derive_contract_dsl` assembly
  command — no `contract` umbrella command at all (see
  [`0006`](0006-deriving-handlers-replace-contractgen.md)).

## Rejected alternatives (why attempt 1 didn't work)

Once `Syntax.lean`'s custom tokens were registered globally, ordinary `` `(structure ...) ``
quasiquotes broke project-wide, forcing `ContractGen.lean` to hand-build raw `Syntax.node` trees
instead of plain quasiquotes for every generated declaration — a maintenance and readability
cost with no corresponding benefit once the alternative (attach `deriving` directly to
already-elaborated `structure`/`inductive` declarations) was found to work cleanly.

## Consequences

`Lang/Syntax.lean` (the current file) and `Lang/Contract.lean`/`ContractGen.lean` (deleted) are
unrelated files that happen to share directory/naming conventions with their deleted
predecessors — the current `Lang/Syntax.lean` is a different, later, second file (see
[`0001`](0001-txm-superseded-by-syntax.md)), not a restoration of the deleted one.
