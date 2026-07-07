# 0007: `tx` bodies are buffered, not elaborated immediately

## Context

An earlier prototype of the `tx { .. }` command elaborated a `tx` body immediately. Doing so
needed `σ.field`'s storage `Ty` (via `Lsc.Deriving.currContractStorageName`) to already be
registered, which forced `derive_contract_dsl` to run before every `tx` and `derive_contract_def`
to run after every `tx`, permanently straddling any single merged macro call.

## Decision

`tx` now just buffers its raw `lscStmt*` syntax under the current namespace
(`Lsc.Deriving.contractTxSyntaxExt`); `Lsc.Deriving.flushContractTxs` (run by
`derive_contract_def`/`derive_contract`) elaborates and emits the real `def name : Stmt := ...`
declarations later, all at once.

## Consequences

A contract's `structure`/`inductive` declarations, its `tx { .. }` bodies, and the closing
`derive_contract_def`/`derive_contract` command can appear in any order relative to each other in
the source file (within the same namespace), since nothing about a `tx`'s own elaboration depends
on storage/error/event types being registered yet.
