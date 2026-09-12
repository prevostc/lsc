# Agent instructions

Treat context as scarce. Use subagents for contained work (coding, proofs,
exploration, build fixes, research, isolated design). Keep the main context on
goals, architectural decisions, evidence, unresolved questions, and current
work. Prefer module APIs and exported guarantees over internals.

Canonical product goal: `docs/PROJECT_GOAL.md`. Keep it concise; not a diary.

## Model routing

When model selection is available:

- **Cursor Grok 4.6 xhigh** (default): coding, refactoring, exploration, build
  fixes, proof implementation, proof-strategy drafts, design drafts, docs,
  reports.
- **Fable 5.1**: only the few most critical architecture decisions (semantics,
  proof boundaries, trusted assumptions) and when Grok conflicts or fails twice.
  At most one at a time, read-only, tight brief, ≤250-line deliverable. Never
  implementation, docs, or first-draft designs.

Fable budget is the binding constraint. Before spawning Fable: could Grok draft
and Fable only review? If yes, do that. Main (Fable) context: delegate, decide,
record; do not read implementation files or long reports.

Do not let execution agents make major architectural decisions implicitly
through code. See **Preview before large work**.

## Lean execution

**Never run more than one Lean build/checking process at once.** One global lock
across all agents: `lake build`, `lake env lean`, project-wide checks, and
equivalents.

Always `scripts/lean …` (e.g. `scripts/lean lake build Lsc.Security.Wealth`);
never raw `lake`/`lean`. It blocks until the other process finishes. Build only
the targets you need (`lake build <Module>`), not the whole library, so another
agent's in-progress file cannot fail your build. Parallel reasoning is fine;
parallel Lean builds are not.

## Preview before large work

Large: new language feature, interface/security/compiler architecture, example
rewrite, numeric/type-system change, or anything that touches more than one
example or a public theorem family.

1. Show the owner the user-facing code: storage struct, one representative
   function, 1–2 theorem statements as a Solidity developer would read them.
2. Wait for an explicit go. Do not spawn implementation/proof subagents until
   the owner confirms the preview (or a revised one).
3. Do not deep-dive (read large internals, start proofs, rewrite trees) to
   figure out the design. Draft the surface, ask, then implement.

Exempt: build/lint, renames, docs, theorem-docstring quality, one-file bugfixes
that do not change a public API or theorem statement.

Subagent briefs must say `preview already approved`, or stop and return a
preview instead of editing.

```lean
structure Storage where
  reserve0 : Amount token0
  reserve1 : Amount token1

def swap0for1 (amountIn : Amount token0) (minOut : Amount token1) : M (Amount token1) := do
  -- …

Tx.run (swap0for1 dx minOut) ctx w = .ok (out, w') →
  w'.self.reserve0.raw * w'.self.reserve1.raw ≥
    w.self.reserve0.raw * w.self.reserve1.raw
```

## Implementation + proof

Plan implementation and proof jointly. Do not design code first and discover
later that it is hostile to proof.

## Simplification

Treat deletion and refactoring as normal progress. After substantial work ask:

> **If we rebuilt this subsystem today using what we now know, would it still look like this?**

Remove, collapse, or refactor unnecessary complexity before building more on
top. Temporary scaffolding must be removed or explicitly promoted to
architecture.

## Architecture contracts

Do not silently change major architectural contracts. Changes affecting
semantics, compilation, trusted assumptions, or proof boundaries must make
their effect on the documented end-to-end proof chain explicit.

## Theorem statements

Safety theorems take *success* as the hypothesis — `Tx.run f ctx w = .ok (r, w')`,
or at trace level "the call was accepted" — and conclude about `w'`. Anything
the program checks itself (`require`, overflow, balance, authorisation) is
implied by success and must not appear as a hypothesis.

No edge-case exclusions (self-transfer, zero amount, sender = owner, …) unless
the property is genuinely false there; then the docstring states the limitation
explicitly.

Every hypothesis must be necessary: if removing it does not make the theorem
false, remove it. Unused hypotheses (`_h…`) are a bug.

Liveness ("under which conditions does the call succeed") is a separate theorem
(`foo_succeeds_of …`), written only when a user needs it; never fused into a
safety theorem.

Prefer statements over all `ctx`/`w`; avoid hypotheses that merely restate an
invariant already carried by the trace framework (`Inv`) unless the theorem is
stated outside that framework.

State theorems on the state delta (fields of `w'` versus `w`); return values
appear only as corollaries or for view functions.

Before (`Examples/Token/ProofsTheorems.lean`):

```
theorem transfer_conserves (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender + w'.self.balances to =
        w.self.balances ctx.sender + w.self.balances to
```

After:

```
Tx.run (transfer to amount) ctx w = .ok ((), w') →
  w'.self.balances ctx.sender + w'.self.balances to =
    w.self.balances ctx.sender + w.self.balances to
```

`hne` is unnecessary: sender = receiver makes the sum trivially unchanged.

Guarantee-module file split: `Lsc/AGENTS.md`. Example layout: `Examples/AGENTS.md`.
`Checks.lean` imports `*Theorems` only.
