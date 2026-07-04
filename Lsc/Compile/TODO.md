# Compile pipeline backlog

Deferred work for the LSC v2 compiler. Items are removed or checked off as they land.

## Bytecode follow-ups

- [x] ABI dispatcher (selector routing on calldata)
- [x] `contractToBytecode` for full `counterDef` (increment + pause + unpause)
- [x] Global unique jump labels per function (fixes cross-function `JUMPI`/`JUMP` collisions)
- [x] Encode-time duplicate `JUMPDEST` label detection
- [x] EvmYul execution smoke test (`BytecodeExecSmoke`: increment / pause / unpause storage)
- [ ] Creation bytecode (deploy wrapper returning runtime code)
- [ ] Real keccak256 ABI selectors (replace `String.hash` stub in `Selectors.lean`)
- [ ] Real keccak256 event topic0 for `Paused` / `Unpaused` (currently `name.hash` stub)
- [ ] ABI encode/decode for revert data and return values
- [ ] EvmYul execution with real 256-bit LOG topics (keccak topic0 currently trips gas accounting in EvmYul)
- [ ] Gas-aware codegen / stack peephole optimization
- [ ] Memory-spilled locals (`MSTORE`/`MLOAD` scratch slots) to simplify stack codegen for decompilers

## Proof obligations

Smoke tests and `native_decide` shape checks exist; the items below are the theorems still to prove. Target module: extend [`Correctness.lean`](Correctness.lean) (IR reference semantics) and add bytecode-specific lemmas as needed.

### Lower (`Stmt` → `IR`)

- [ ] `Lower.stmt` preserves a formal `Stmt` big-step semantics (or refines `Lang/Eval` once wired)
- [ ] `Wei.lowerLetBind` / `lowerAddCheckedNatStorage`: checked add matches `Wei` overflow semantics (extend existing shape lemma)
- [ ] `require` lowers to `ifRevert (isZero cond)` with correct revert condition
- [ ] `storageSet` / `emit` resolve slots and topic0 from `Config` correctly

### Codegen (`IR` → `Instr`)

- [ ] Reference semantics for `IR.Expr` / `IR.Stmt` (`evalExpr` / `evalStmt` in `Correctness.lean`) is sound and complete for the fragment we lower
- [ ] `Codegen.stmt`: compiling then executing instrs (via EvmYul `Ξ`) refines `evalStmt` on reachable states
- [ ] `ifRevert`: revert path taken iff condition is non-zero in the reference semantics
- [ ] `log1`: LOG1 topic and 32-byte data word match `evalStmt` log trace (modulo memory layout)
- [ ] Global label threading: prefixed labels do not change codegen semantics, only jump targets
- [ ] Stack cleanup (`log1` local pops): does not alter observable storage / logs / revert outcome

### Encode (`Instr` → `ByteArray`)

- [ ] `fixpointLabels` converges and is stable for all emitted instr lists
- [ ] `layoutLabels` assigns each `jumpDest` the PC of its opcode in the final byte stream
- [ ] Every `pushLabel` / `jump` / `jumpi` resolves to the PC of the matching `jumpDest` (no silent `getD 0`)
- [ ] `encode` is injective on label names: duplicate detection implies layout correctness
- [ ] `serializeInstr` + push width agree with EvmYul `decode` / `parseInstr` (round-trip on emitted bytes)

### Contract (`Config` + `ContractDef` → full instr list)

- [ ] Dispatcher: calldata `< 4` bytes reverts; selector `calldataload(0) >> 224` matches `computeSelector`
- [ ] Dispatcher: unknown selector reverts; known selector jumps to the correct function entry `jumpDest`
- [ ] Function bodies preserve per-function semantics when entered with empty stack (fresh `Ctx.forFunction`)
- [ ] `contractToBytecode` = `encode ∘ contract` succeeds iff label set is duplicate-free

### Counter end-to-end (`counterDef`)

Prove (or reduce to the lemmas above) for `increment` / `pause` / `unpause`:

- [ ] **Increment**: slot 0 increases by 1 when not paused; reverts when paused; overflow check matches `Wei` add-checked
- [ ] **Pause**: slot 1 set when `msg.sender == owner` and not already paused; reverts on `NotOwner` / `Paused`
- [ ] **Unpause**: slot 1 cleared when owner and paused; reverts otherwise
- [ ] **Events**: `Incremented` / `Paused` / `Unpaused` emit expected topic0 and data (once keccak topics land)
- [ ] **Dispatcher + bodies**: full `contractToBytecode counterDef` behavior matches composing the three function proofs

### EvmYul bridge

- [ ] Define a map from `IRState` (or account storage + logs) to EvmYul post-`Ξ` state
- [ ] `BytecodeExecSmoke` properties (slot 0/1 after call) as formal theorems, not only `IO` smoke
- [ ] Execution with real 256-bit LOG topics refines the same spec (blocked on EvmYul gas accounting fix)

### What is already checked (not proofs)

| Check | Where |
|---|---|
| IR increment let shape / local binding | `Correctness.lean` (`native_decide`) |
| Lowering succeeds on counter slices | `Correctness.lean`, `BytecodeTest.lean` |
| Opcode / selector presence in hex | `BytecodeTest.lean` |
| Jump label uniqueness | `BytecodeTest.lean` (`counter_jumpdest_labels_unique`) |
| Storage mutation via EvmYul | `BytecodeExecTest.lean` + `BytecodeExecSmoke` exe |

## Other compile paths (not pursued now)

- [ ] Yul text emission via `Yul.lean` — kept in tree, not on critical path
- [ ] `solc` / strict-assembly pipeline
- [ ] forge-lean Foundry fork
- [ ] Removing or refactoring existing Yul modules
