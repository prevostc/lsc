# Math in LSC — The `@math` Annotation

> This document covers how LSC handles arithmetic-heavy functions: the `@math`
> annotation, the automatic ℝ spec generation, the `WayRayMath` dependency,
> and the suggested proof patterns. Read DESIGN.md first.

---

## The Problem

DeFi developers implement mathematical formulas. The formula exists in their head
as a real-number expression — `amountIn * reserveOut / (reserveIn + amountIn)`.
The on-chain implementation is a chain of `wadMul`/`wadDiv` calls over `Nat`.
The gap between the two is where bugs hide:

- Which way does rounding go? Does it favor the user or the protocol?
- What input sizes cause overflow in the intermediate `wadMul`?
- After three nested `rayMul` calls, how much precision has been lost?
- Two equivalent algebraic paths give different results — which is closer to the spec?

LSC's answer: **write the implementation once, get the ℝ spec for free, prove
the gap is acceptable**.

---

## The `@math` Annotation

Mark any pure arithmetic function with `@math`:

```lean
contract AMM where

  @math
  def computeOutput (amountIn r0 r1 : Wad) : Wad :=
    amountIn.wadMul r1 |>.wadDiv (r0.wadAdd amountIn)
```

This does exactly two things:

**1. Generates a `ℝ` twin automatically.**

The compiler walks the expression AST and lifts every operation to its `ℝ`
counterpart. The result is registered as `AMM.computeOutput.spec`:

```lean
-- compiler output — not user code, never written manually
def AMM.computeOutput.spec (amountIn r0 r1 : ℝ) : ℝ :=
  amountIn * r1 / (r0 + amountIn)
```

Available in proof files without any import beyond the contract itself.

**2. Allows the function to be called from `Tx` bodies without manual lifting.**

`@math` functions are pure and total by construction (enforced by the
elaborator). The compiler handles the lift into `ContractM` automatically.

That is all `@math` does. No theorem statements are generated. No proof
obligations are created. The user decides what to prove.

---

## Constraints on `@math` Functions

The elaborator enforces a strict subset of the language. This is what makes the
ℝ lifting pass total — every node has a unique `ℝ` counterpart.

**Allowed:**

- `Wad` and `Ray` arithmetic: `wadMul`, `wadDiv`, `wadAdd`, `wadSub`, `rayMul`,
  `rayDiv`, `rayAdd`, `raySub`
- `UInt256` arithmetic: `addChecked`, `subChecked`, `mulDiv`
- Local `let` bindings
- `if / else` on `Bool` (for `min`, `max`, clamp patterns)
- Calls to other `@math` functions
- Numeric literals

**Not allowed** (compile error with source position):

- Storage reads or writes
- `emit`
- `require` / `revert` (use `.orRevert` at the call site in the `Tx` body instead)
- External calls
- Calls to non-`@math` functions

The `orRevert` pattern keeps error handling out of the math function and in the
`Tx` body where it belongs:

```lean
@math
def computeOutput (amountIn r0 r1 : Wad) : Except ArithError Wad :=
  amountIn.wadMul r1 |>.andThen (·.wadDiv (r0.wadAdd amountIn))

def swap (amountIn : Wad) : Tx := do
  let out ← computeOutput amountIn storage.reserve0 storage.reserve1
              |>.orRevert .Overflow   -- error handling lives here
  -- ...
```

This separation means `computeOutput` proofs never touch `ContractM`. They are
purely about numbers.

---

## The ℝ Lifting Rules

The compiler applies these rules mechanically. Knowing them helps you predict
what `yourFn.spec` will look like.

| LSC operation | ℝ spec counterpart |
|---|---|
| `a.wadMul b` | `a * b` |
| `a.wadDiv b` | `a / b` |
| `a.wadAdd b` | `a + b` |
| `a.wadSub b` | `a - b` |
| `a.rayMul b` | `a * b` |
| `a.rayDiv b` | `a / b` |
| `a.rayAdd b` | `a + b` |
| `a.raySub b` | `a - b` |
| `UInt256.mulDiv a b c` | `a * b / c` |
| `if h then a else b` | `if h then a else b` (preserved) |
| `let x := e` | `let x := e.spec` |
| call to `@math g` | call to `g.spec` |
| `Wad` literal `n` | `(n : ℝ) / WAD` |
| `Ray` literal `n` | `(n : ℝ) / RAY` |

Rounding direction (halfUp vs floor) disappears in the spec — all operations
become exact. This is intentional: the spec captures intent, not precision.

---

## The `WayRayMath` Dependency

LSC depends on `WayRayMath` for the error bound lemmas that connect `ℕ`
operations to their `ℝ` counterparts. These are the building blocks for
faithfulness proofs.

The key primitives you will use in proofs:

```lean
-- Single-operation error bounds
theorem WayRayMath.wadMul_error (a b : ℕ) :
    |decode (wadMulHalfUp a b) - decode a * decode b| ≤ WAD_ERROR

theorem WayRayMath.wadDiv_error (a b : ℕ) (hb : 0 < b) :
    |decode (wadDivHalfUp a b) - decode a / decode b| ≤ WAD_ERROR / decode b

-- Composition error bounds
theorem WayRayMath.wadMul_compose_error (a b c : ℕ) :
    |decode (wadMulHalfUp a (wadMulHalfUp b c)) -
     decode a * decode b * decode c| ≤ (1 + decode a) * WAD_ERROR

-- The decode bridge
def WayRayMath.decode (n : ℕ) : ℝ := (n : ℝ) / WAD
theorem WayRayMath.decode_nonneg (n : ℕ) : 0 ≤ decode n

-- Error constants (concrete values, usable in norm_num)
def WayRayMath.WAD_ERROR : ℝ := (1 : ℝ) / WAD        -- = 10⁻¹⁸
def WayRayMath.RAY_ERROR : ℝ := (1 : ℝ) / RAY        -- = 10⁻²⁷
def WayRayMath.rayMulHalfUpMaxError : ℝ := 1 / (2 * RAY)
```

You do not need to understand the internals of `WayRayMath`. You use its lemmas
the same way you use `Nat.add_comm` — as established facts about operations.

---

## The Proof Workflow

### Step 1 — Write the `@math` function

```lean
@math
def computeOutput (amountIn r0 r1 : Wad) : Except ArithError Wad :=
  amountIn.wadMul r1 |>.andThen (·.wadDiv (r0.wadAdd amountIn))
```

The compiler immediately makes `AMM.computeOutput.spec` available:

```lean
-- auto-generated:
def AMM.computeOutput.spec (amountIn r0 r1 : ℝ) : ℝ :=
  amountIn * r1 / (r0 + amountIn)
```

### Step 2 — Check the spec looks right

```lean
-- Quick sanity check in the proof file:
#check @AMM.computeOutput.spec
-- AMM.computeOutput.spec : ℝ → ℝ → ℝ → ℝ

-- Verify it algebraically:
example (a r0 r1 : ℝ) (h : r0 + a ≠ 0) :
    AMM.computeOutput.spec a r0 r1 ≤ r1 := by
  simp [AMM.computeOutput.spec]
  positivity  -- or field_simp; nlinarith
```

If the spec doesn't match your intent, your implementation is wrong — fix it
before proving anything.

### Step 3 — Choose which theorems to prove

See the suggested theorems section below. Not all are required. Pick the ones
that address your security concerns.

### Step 4 — Let the LLM write proof bodies

Provide the LLM with:
- The `@math` function definition
- The auto-generated `.spec` definition
- The relevant `WayRayMath` lemmas
- The theorem statement you want proved

The LLM handles the proof body. You review whether the theorem statement
captures what you intended.

---

## Suggested Theorems

These are not generated automatically. They are patterns documented here.
Copy, adapt, and prove the ones relevant to your function. Not every `@math`
function needs all four — a simple `min` function needs none.

### Pattern 1 — Spec Correctness

Prove the ℝ spec does what you intend. Pure algebra. `ring` and `field_simp`
close almost all goals here. No `WayRayMath` needed.

```lean
/-- The output formula preserves k exactly in the real-number model. -/
theorem AMM.computeOutput.spec_preserves_k
    (amountIn r0 r1 : ℝ)
    (h0 : 0 < r0) (h1 : 0 < r1) (ha : 0 < amountIn) :
    (r0 + amountIn) * (r1 - AMM.computeOutput.spec amountIn r0 r1) = r0 * r1 := by
  simp [AMM.computeOutput.spec]
  field_simp
  ring
```

This is the theorem that answers: *"does my formula do what I think it does?"*
It lives entirely in ℝ and requires no knowledge of Wad encoding.

### Pattern 2 — Faithfulness

Prove the implementation is within ε of the spec. This uses `WayRayMath` lemmas.
The `ε` should be a concrete value derivable by `norm_num`.

```lean
/-- The on-chain output is within ε of the real-number spec. -/
theorem AMM.computeOutput.faithful
    (amountIn r0 r1 : ℕ)
    (h0 : 0 < r0) (h1 : 0 < r1) (ha : 0 < amountIn)
    -- input bound: needed to bound ε concretely
    (hmax : amountIn ≤ MAX_AMOUNT) :
    -- impl output, decoded
    let out_impl := (wadMulHalfUp amountIn r1).wadDivHalfUp (r0 + amountIn)
    -- spec output
    let out_spec := AMM.computeOutput.spec (decode amountIn) (decode r0) (decode r1)
    -- they agree within ε
    |decode out_impl - out_spec| ≤ AMM.OUTPUT_ε := by
  simp only [AMM.computeOutput.spec]
  -- apply WayRayMath composition lemmas
  calc |decode (wadMulHalfUp amountIn r1).wadDivHalfUp (r0 + amountIn)
          - decode amountIn * decode r1 / (decode r0 + decode amountIn)|
      ≤ _ := WayRayMath.wadDiv_compose_error _ _ _ h0
    _ ≤ AMM.OUTPUT_ε := by norm_num [AMM.OUTPUT_ε, WayRayMath.WAD_ERROR]
```

This answers: *"how much precision does Wad encoding lose?"* and *"what is the
concrete error budget?"*

### Pattern 3 — Rounding Bias

Prove the rounding is one-sided. Critical when rounding direction determines
who benefits — protocol or user. Use `≤` not `|·|`.

```lean
/-- The implementation always rounds output down (favors the protocol). -/
theorem AMM.computeOutput.rounds_down
    (amountIn r0 r1 : ℕ)
    (h0 : 0 < r0) (h1 : 0 < r1) :
    decode (wadMulHalfUp amountIn r1).wadDivFloor (r0 + amountIn) ≤
    AMM.computeOutput.spec (decode amountIn) (decode r0) (decode r1) := by
  simp [AMM.computeOutput.spec]
  exact WayRayMath.wadDiv_floor_le _ _ h0
```

This answers: *"does rounding ever give the user more than they should get?"*
For AMMs and lending protocols this is often a security property, not just
a precision property. A protocol that rounds output up leaks value.

Note: choose `wadDivFloor` vs `wadDivHalfUp` deliberately. `halfUp` is closer
to the spec (smaller `|·|` error) but not monotonically below it. `floor` is
always below the spec (one-sided) but slightly less accurate. Pick based on
which guarantee you need.

### Pattern 4 — Safe Domain

State exactly what inputs are safe (no overflow, no division by zero).
This directly answers: *"when does this break?"*

```lean
/-- Characterize exactly when computeOutput succeeds. -/
theorem AMM.computeOutput.safe_iff
    (amountIn r0 r1 : Wad) :
    (computeOutput amountIn r0 r1).isOk ↔
    -- no overflow in numerator
    amountIn.raw * r1.raw < 2^256 * WAD ∧
    -- denominator nonzero
    r0.raw + amountIn.raw ≠ 0 ∧
    -- no overflow in final division
    (amountIn.raw * r1.raw / WAD) * WAD < 2^256 * (r0.raw + amountIn.raw) := by
  simp [computeOutput, Wad.wadMul, Wad.wadDiv, Wad.wadAdd,
        UInt256.mulDiv, UInt256.addChecked]
  omega
```

This answers: *"what input bounds are safe?"* The right-hand side of the `↔`
is the `SafeInputs` predicate for this function. Users can use it as a
precondition in higher-level theorems:

```lean
-- In the Tx-level theorem:
theorem AMM.swap_succeeds_when_safe
    (s : ContractState AMMStorage) (amountIn : Wad)
    (h : AMM.computeOutput.safe_iff.mp ⟨..., ...⟩) :
    (runS (swap amountIn) s).isOk := by ...
```

---

## The Three Worlds and How They Relate

Every `@math` function lives in three worlds simultaneously. Understanding which
world you are in determines which tools to use.

```
ℝ  world    -- AMM.computeOutput.spec
             -- tools: ring, field_simp, nlinarith, norm_num
             -- facts: exact arithmetic, no overflow possible

ℕ  world    -- computeOutput (the @math function body, over Nat)
             -- tools: WayRayMath lemmas, omega
             -- facts: rounding exists, no overflow (Nat is unbounded)

EVM world   -- the compiled Wad/UInt256 operations
             -- tools: simp + omega, overflow conditions
             -- facts: operations may error, BitVec wrapping
```

The compiler gives you the ℝ/ℕ bridge (`computeOutput.spec` and the implicit
`decode` mapping). You write proofs that connect them. The EVM world is handled
by the framework's arithmetic lemmas — `wadMul_ok_value`, `wadDiv_ok_iff` etc.
You rarely need to think about EVM directly.

The key bridge lemma pattern, used in almost every faithfulness proof:

```lean
-- framework-provided, once per operation:
theorem Wad.wadMul_ok_value (a b r : Wad)
    (h : a.wadMul b = .ok r) :
    r.raw = a.raw * b.raw / WAD := by
  simp [Wad.wadMul, UInt256.mulDiv] at h; omega

-- connects EVM result to ℕ computation
-- then WayRayMath connects ℕ computation to ℝ spec
```

---

## Worked Example — CapNetwork Interest Calculation

This is a full example following the exact pattern from `CapNetwork.Defs` and
`CapNetwork.Theorems`. It shows all four proof patterns on a realistic formula.

### The contract

```lean
contract CapNetwork where

  storage:
    scaledDebt  : Ray
    supplyIndex : Ray
    uwIndex     : Ray

  errors:
    | Overflow

  @math
  def debtAt (scaledDebt supplyIndex uwIndex : Ray) : Ray :=
    scaledDebt.rayMul (supplyIndex.rayMul uwIndex)

  @math
  def supplyInterest (scaledDebt uwIndex0 supplyIndex0 supplyIndex1 : Ray) : Ray :=
    scaledDebt.rayMul (uwIndex0.rayMul (supplyIndex1.raySub supplyIndex0))

  @math
  def premiumInterest (scaledDebt supplyIndex1 uwIndex0 uwIndex1 : Ray) : Ray :=
    scaledDebt.rayMul (supplyIndex1.rayMul (uwIndex1.raySub uwIndex0))
```

### Auto-generated specs (compiler output)

```lean
def CapNetwork.debtAt.spec (d si ui : ℝ) : ℝ :=
  d * (si * ui)

def CapNetwork.supplyInterest.spec (d ui0 si0 si1 : ℝ) : ℝ :=
  d * (ui0 * (si1 - si0))

def CapNetwork.premiumInterest.spec (d si1 ui0 ui1 : ℝ) : ℝ :=
  d * (si1 * (ui1 - ui0))
```

### Pattern 1 — Spec correctness: two paths are equal in ℝ

```lean
/-- In ℝ, computing debt change as (debt_t1 - debt_t0) equals
    (supplyInterest + premiumInterest). No rounding means exact equality. -/
theorem CapNetwork.spec_paths_equal
    (d si0 ui0 si1 ui1 : ℝ)
    (hs : si0 ≤ si1) (hu : ui0 ≤ ui1) :
    -- path 1: direct difference
    let path1 := debtAt.spec d si1 ui1 - debtAt.spec d si0 ui0
    -- path 2: interest components
    let path2 := supplyInterest.spec d ui0 si0 si1 +
                 premiumInterest.spec d si1 ui0 ui1
    path1 = path2 := by
  simp [debtAt.spec, supplyInterest.spec, premiumInterest.spec]
  ring
```

### Pattern 2 — Faithfulness: two impl paths agree within ε

```lean
/-- On-chain, the two debt-change paths agree within implPathsMaxRoundingError. -/
theorem CapNetwork.impl_paths_approx_equal
    (d si0 ui0 si1 ui1 : ℕ)
    (hs : si0 ≤ si1) (hu : ui0 ≤ ui1)
    (hd : decode d ≤ MAX_DEBT) :
    let path1 := decode (debtAt d si1 ui1) - decode (debtAt d si0 ui0)
    let path2 := decode (supplyInterest d ui0 si0 si1) +
                 decode (premiumInterest d si1 ui0 ui1)
    |path1 - path2| ≤ implPathsMaxRoundingError := by
  -- each rayMulHalfUp composed twice contributes at most
  -- (1 + decode d) * RAY_ERROR per term
  -- four terms total → 2 * (1 + decode d) * RAY_ERROR
  have h1 := WayRayMath.double_rayMulHalfUp_decode_error d si1 ui1
  have h2 := WayRayMath.double_rayMulHalfUp_decode_error d si0 ui0
  have h3 := WayRayMath.double_rayMulHalfUp_decode_error d ui0 (si1 - si0)
  have h4 := WayRayMath.double_rayMulHalfUp_decode_error d si1 (ui1 - ui0)
  simp [implPathsMaxRoundingError, MAX_DEBT] at *
  linarith
```

### Pattern 3 — Rounding bias: `rayMulHalfUp` is symmetric around the true value

```lean
/-- debtAt implementation is within one RAY_ERROR of spec in both directions.
    (halfUp rounds to nearest, so bias is symmetric, not one-sided.) -/
theorem CapNetwork.debtAt_symmetric_rounding
    (d si ui : ℕ) :
    |decode (debtAt d si ui) - debtAt.spec (decode d) (decode si) (decode ui)|
    ≤ WayRayMath.rayMulHalfUpMaxError * (1 + decode d) := by
  simp [debtAt, debtAt.spec]
  exact WayRayMath.double_rayMulHalfUp_decode_error d si ui
```

### Pattern 4 — Safe domain

```lean
/-- debtAt succeeds for all inputs below MAX_DEBT and MAX_INDEX. -/
theorem CapNetwork.debtAt_safe
    (d si ui : Wad)
    (hd : d.raw ≤ MAX_DEBT_RAW)
    (hs : si.raw ≤ MAX_INDEX_RAW)
    (hu : ui.raw ≤ MAX_INDEX_RAW) :
    (debtAt d si ui).isOk := by
  simp [debtAt, Ray.rayMul, UInt256.mulDiv]
  -- show that si.raw * ui.raw / RAY < 2^256
  -- and d.raw * (si.raw * ui.raw / RAY) / RAY < 2^256
  -- follows from the given bounds and RAY = 10^27
  omega
```

---

## Deriving ε Concretely

The hardest part of Pattern 2 is arriving at a concrete `ε`. The approach:

**Step 1**: Count how many `rayMul`/`wadMul` operations the formula performs.
Each one contributes at most `RAY_ERROR` or `WAD_ERROR` of absolute error,
scaled by the magnitude of the other operand.

**Step 2**: Use `WayRayMath`'s composition lemmas to get a formula for the
total error in terms of `decode` of the inputs.

**Step 3**: Apply your protocol's input bounds (max debt, max index value,
max reserve size) to convert the formula into a concrete number.

**Step 4**: State `ε` as a `def` in a `noncomputable section` (since it
involves `ℝ` arithmetic), and prove `ε < 10^(-k)` for some `k` using
`norm_num`. This makes the error budget human-readable.

```lean
noncomputable section

/-- ε for computeOutput: one wadMul + one wadDiv = two error terms. -/
def AMM.OUTPUT_ε : ℝ :=
  (1 + MAX_RESERVE) * WAD_ERROR +   -- from wadMul
  WAD_ERROR / MIN_DENOMINATOR        -- from wadDiv

/-- The output error is always below 10⁻¹⁵ given the protocol bounds. -/
theorem AMM.OUTPUT_ε_lt :
    AMM.OUTPUT_ε < (10 : ℝ)^(-15 : ℤ) := by
  simp [AMM.OUTPUT_ε, MAX_RESERVE, MIN_DENOMINATOR, WAD_ERROR]
  norm_num

end
```

The `OUTPUT_ε_lt` theorem is the human-readable summary of your precision
guarantee. An auditor reads it as: *"swap output is accurate to 15 decimal
places"*.

---

## File Conventions

Every contract with `@math` functions gets two additional files:

```
YourContract.lean          -- contract definition with @math functions
YourContract.Spec.lean     -- Pattern 1 theorems (pure ℝ algebra)
YourContract.Math.lean     -- Patterns 2, 3, 4 (ℕ faithfulness, rounding, domain)
```

`Spec.lean` has no `WayRayMath` imports — it only uses `Mathlib` (ring, field_simp).
`Math.lean` imports both `WayRayMath` and the contract.

This separation means:
- `Spec.lean` can be read by anyone who understands the math, regardless of
  Lean expertise
- `Math.lean` is where the precision engineering lives
- The contract file itself stays clean — no proof code mixed with contract code

---

## Quick Reference

| Question | Pattern | Tools |
|---|---|---|
| Does my formula do what I intend? | 1 — Spec correctness | `ring`, `field_simp` |
| How much precision is lost? | 2 — Faithfulness | `WayRayMath` lemmas, `linarith` |
| Does rounding favor the protocol? | 3 — Rounding bias | `WayRayMath` floor lemmas |
| What inputs are safe? | 4 — Safe domain | `simp`, `omega` |
| What does `computeOutput.spec` look like? | `#check YourContract.fn.spec` | compiler output |
| What ε bound should I use? | Count ops × `WAD_ERROR`, apply bounds | `norm_num` |

---

## What `@math` Does NOT Do

To be explicit about the boundaries:

- Does not generate theorem statements. The four patterns above are suggestions.
- Does not run proofs. You write or LLM-generate all proof bodies.
- Does not guarantee your formula is correct. Pattern 1 does that — you must
  write and prove it.
- Does not handle storage, events, or external calls. Those stay in `Tx` bodies.
- Does not affect bytecode. `@math` is a compile-time annotation only.
- Does not add runtime overhead. The `.spec` function exists only in Lean's
  type theory, never in EVM bytecode.