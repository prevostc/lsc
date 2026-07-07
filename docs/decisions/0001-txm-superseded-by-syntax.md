# 0001: `tx { .. }` custom grammar replaced the `TxM` do-notation builder

## Context

Contract bodies need a surface syntax for reading/writing storage, requiring conditions,
emitting events, and reverting with typed errors. The first attempt (`Lsc/Lang/TxM.lean`) built
`Stmt` values via ordinary Lean `do`-notation over a small writer monad (`TxM α := WriterT Stmt
Id α`), reusing Lean's stdlib `term`/`doElem` categories instead of declaring new ones.

## Decision

Contract bodies are now written in a purpose-built grammar (`Lsc/Lang/Syntax.lean`):
`declare_syntax_cat lscExpr`/`lscStmt` introduce two new syntax categories that are inert
everywhere except inside the `tx <name> { ... }` command-level delimiter. `TxM.lean` remains in
the codebase as the underlying builder/combinator layer `tx { ... }` desugars into (still
directly exercised by `Lang/TxMTest.lean`), but it is no longer the contract-author surface.

## Rejected alternatives

The `do`-notation-over-`TxM` approach worked, but every piece of "assignment-shaped" or
"keyword-shaped" sugar it wanted ran into real, empirically-verified parser conflicts with
*existing* Lean productions:

- A generic `σ.field := e` write notation (tried as both a `doElem`-level macro and a lower-level
  raw-`Syntax`-indexed macro) collided with Lean's builtin mutable-local-reassignment `doElem`
  (`doReassign`) — either failing to declare at all, or producing an ambiguous `choice` node the
  `do`-block elaborator refused to resolve.
- `σ.field = e` (a term-level `infix:50`, not a `doElem`) was tried next, on the theory that
  term-level ambiguity might resolve via type-checking. It didn't: the parser deterministically
  shadowed `Eq` for *every* `ident = term` occurrence project-wide, breaking ordinary equality
  checks and proof hypotheses throughout the codebase. Reverted immediately.
- A generic type-tagged read family (`wei σ.field`, `bool σ.field`, `addr σ.field`, `u256
  σ.field`) plus a `set σ.field e` write family stood in as the workaround, along with a `var x
  := e` binder dispatching via a `LetBindable` typeclass to force evaluate-once semantics.
- Even `emit`'s naming had a parser-conflict history: sharing the `emit` spelling between the
  real-constructor sugar and its underlying raw primitive caused declaration-site ambiguity,
  resolved by renaming the primitive (`emitEvent`) rather than the sugar.

## Consequences

With a fresh, purpose-built grammar, none of the above workarounds are needed: `tx { ... }` has
its own `σ.field = e;` assignment production, its own `let x = e;` binder, and its own
`require`/`revert`/`emit` forms, none of which compete with any Lean builtin, since `lscStmt`/
`lscExpr` are categories Lean's core parser never enters except through the `tx { ... }`
delimiter.
