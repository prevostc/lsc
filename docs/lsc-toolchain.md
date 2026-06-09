# LSC Toolchain

**Companion document:** [lsc-spec.md](lsc-spec.md) — normative LSC language definition

This document describes the **current implementation state** and the planned Foundry integration path.

---

## 1. Current State (v0.1)

The v0.1 library (`Lsc.*`) compiles in Lean 4. The proof harness works end-to-end:

```
src/Counter.lean  →  lake build  →  kernel checks types
test/CounterLemma.lean + CounterTheorem.lean  →  lake build  →  kernel checks all proofs
```

No EVM bytecode is emitted yet. The current toolchain is purely a **Lean proof library**.

### 1.1 What works

| Feature | Status |
|---------|--------|
| `Lsc.UInt256`, `Lsc.Address`, `Lsc.World` | ✅ |
| `Lsc.ContractM`, `Lsc.runS` | ✅ |
| `state!` macro (struct + fields + `ContractState` instance + simp lemmas) | ✅ |
| `contract!` macro (monad alias + `view`) | ✅ |
| `error!` macro (inductive + `LscError` instance + `[lsc.error]` attribute) | ✅ |
| `get .field` / `set .field val` | ✅ |
| `+?` checked arithmetic (`addChecked`, `addCheckedNat`) | ✅ |
| `require` / `failWhen` guards | ✅ |
| `@[lsc.external]` / `@[lsc.public]` attributes | ✅ (registered; codegen planned) |
| Counter example + proofs (state-shaped + world-shaped) | ✅ |
| EVM bytecode output | ❌ (v1) |
| Foundry integration | ❌ (v1) |
| `Mapping K V` | ❌ (v1) |
| External calls | ❌ (v2b) |

### 1.2 Name bindings (v0.1 vs planned v1)

| Planned LSC (v1) | Current implementation (v0.1) |
|---|---|
| `World E α` (free monad) | `ContractM E S α` (`StateT World (Except E)`) |
| `load .field` | `get .field` |
| `store [ .field := val ]` | `set .field val` |
| `f.run s` | `runS f s` |
| `state! where` (implicit module) | `state! ModName where` (explicit) |
| ERC-7201 namespaced slots | Sequential flat slots (0, 1, 2, …) |

---

## 2. Project Layout

```
lsc/
├── Lsc/
│   ├── Prelude.lean          # re-exports all Lsc.* modules
│   ├── UInt256.lean          # UInt256 subtype + simp lemmas
│   ├── Word.lean             # FromWord / ToWord typeclasses
│   ├── World.lean            # Address, World, getStorage/setStorage
│   ├── Error.lean            # ArithError, ContractError, LscError
│   ├── ContractState.lean    # Field, ContractState class
│   ├── ContractM.lean        # ContractM, get, set, require, failWhen
│   ├── CheckedArith.lean     # +? operators
│   ├── Run.lean              # runS
│   ├── StateMacro.lean       # state! and contract! macros
│   ├── ErrorMacro.lean       # error! macro
│   └── Attribute.lean        # @[lsc.external], @[lsc.public], @[lsc.error]
└── examples/
    └── counter/
        ├── lakefile.lean
        └── src/Counter.lean
        └── test/
            ├── CounterLemma.lean
            └── CounterTheorem.lean
```

### 2.1 `lakefile.lean` (minimal)

```lean4
import Lake
open Lake DSL

package «lsc» where
  name := "lsc"

@[default_target]
lean_lib Lsc where
  roots := #[`Lsc]
```

The Counter example has its own `lakefile.lean` that requires the parent `lsc` package.

---

## 3. Planned Foundry Integration (v1)

The v1 compiler pipeline will follow the same architecture as Foundry's Vyper support:

```
src/Counter.lean
      │
      ▼  lake build + Lean 4 elaboration
  Lean IR
      │
      ▼  LSC validator
  Validated IR
      │
      ▼  Yul emitter
  out/Counter.lean/Counter.yul
      │
      ▼  solc (strict assembly)
  out/Counter.lean/Counter.json   (Foundry-compatible artifact)
```

### 3.1 Storage layout (planned v1)

In v1, `state!` fields will map to **ERC-7201 namespaced storage**:

- Namespace root: `erc7201(id) = keccak256(keccak256(bytes(id)) − 1) & ~bytes32(0xff)`
- Default namespace id: module name (e.g., `"Counter"` for `src/Counter.lean`)
- Field offsets: sequential within namespace (0, 1, 2, …)

Currently (v0.1) the proof harness uses flat sequential slots at `defaultSelf = Address.zero` — no namespace root computation.

### 3.2 `foundry.toml` (planned v1)

```toml
[profile.default]
src = "src"
out = "out"
libs = ["lib"]
skip = ["test/**/*Lemma.lean", "test/**/*Theorem.lean"]

[profile.default.lean]
toolchain_file = "lean-toolchain"
emit_yul = true
```

### 3.3 Artifact format (planned v1)

```json
{
  "abi": [ ... ],
  "bytecode": { "object": "0x..." },
  "metadata": {
    "storageLayout": {
      "layout": "erc7201",
      "namespaces": [
        {
          "id": "Counter",
          "root": "0x…",
          "fields": [
            { "name": "number", "offset": 0, "type": "uint256" },
            { "name": "paused", "offset": 1, "type": "bool" }
          ]
        }
      ]
    }
  }
}
```

---

## 4. Error Messages

Current errors are Lean elaboration errors. Planned `lsc:` prefix diagnostics for v1:

| Condition | Message |
|-----------|---------|
| `error!` missing `arith` constructor | `error!: 'E' must include '| arith : ArithError → E'` |
| `state!` field with unsupported type | Lean type error at elaboration |
| `sorry` in proof file | Lean kernel rejects |
| Plain `+` on `UInt256` | Lean type error (no `Add UInt256` instance) |
| `store .field v` (wrong syntax) | Lean parse error (planned: `lsc: use set .field v`) |

---

## 5. Verification and Trust Boundaries

```
Theorem files
    ↓ (Lean kernel — proven)
@[lsc.external] contract functions
    ↓ (trusted — tested)
Lean IR → Yul emitter
    ↓ (trusted — solc)
EVM bytecode
    ↓ (tested — Foundry fuzz via deployCode)
On-chain behavior
```

| Layer | v0.1 status |
|-------|-------------|
| Theorem files → contract functions | **Proven** (Lean kernel) |
| Lean IR → Yul emitter | **Not yet implemented** |
| Yul → bytecode | **Not yet implemented** |
| Bytecode on chain | **Not yet implemented** |

---

## 6. Implementation Checklist

### Phase v0.1 (current — Lean library only)

- [x] `Lsc.UInt256` — subtype, comparisons, `addNat`
- [x] `Lsc.Word` — `FromWord`/`ToWord` for `UInt256` and `Bool`
- [x] `Lsc.World` — `Address`, `World`, `getStorage`/`setStorage`, simp lemmas
- [x] `Lsc.Error` — `ArithError`, `ContractError`, `LscError`
- [x] `Lsc.ContractState` — `Field`, `ContractState` class
- [x] `Lsc.ContractM` — `ContractM`, `get`, `set`, `require`, `failWhen`, `revert`
- [x] `Lsc.CheckedArith` — `+?` (addChecked, addCheckedNat)
- [x] `Lsc.Run` — `runS`, `ContractM.pure_apply`, `ContractM.bind_apply`
- [x] `Lsc.StateMacro` — `state!` (struct + fields + instance + simp theorems) + `contract!`
- [x] `Lsc.ErrorMacro` — `error!`
- [x] `Lsc.Attribute` — `@[lsc.external]`, `@[lsc.public]`, `@[lsc.error]`
- [x] Counter example (`src/Counter.lean` + `test/CounterLemma.lean` + `test/CounterTheorem.lean`)

### Phase v1 (planned — Foundry integration)

- [ ] ERC-7201 namespace root computation
- [ ] `load`/`store [ .field := val ]` syntax
- [ ] `Mapping K V` type
- [ ] `MsgContext` (caller, value, timestamp, number)
- [ ] LSC validator (post-elaboration pass, `lsc:` prefix errors)
- [ ] Yul emitter — `@[lsc.external]` → ABI dispatcher + reentrancy lock + inline `SLOAD`/`SSTORE`
- [ ] ABI JSON generation
- [ ] `forge build` / `LeanCompiler` in `foundry-compilers`
- [ ] `forge test` Lean proof runner
- [ ] `forge init --lean` scaffold
- [ ] ERC-20 example

### Phase v2b (planned — external calls)

- [ ] `call`/`staticcall` in `ContractM`
- [ ] Interface definitions (`@[lsc.interface]`)
- [ ] `CALL`/`STATICCALL` lowering
- [ ] Proof erasure for extern call sites
