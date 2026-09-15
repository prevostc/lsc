import Lsc.Compiler.YulDefs
import Lsc.Compiler.YulTheorems

/-!
# Core → Yul

`toYulFn` compiles one `FnDef` to a powdr `YulSemantics` block. `Op.call` /
`Stmt.call` / `Op.view` / `Stmt.view` are emitted as a scoped Yul block: ABI
pack at `0x80` (`mstore(0x80, shl(224, sel))`, args at `0x84+`), then
`call(extCallGas, target, 0, …)` or `staticcall(extCallGas, target, …)`,
`if iszero(ok) { revert(0,0) }`, then `AbiRet` decode. Temporaries `_ok_*`
live inside the block so `restore` drops them; the Core result variable is
declared outside and assigned inside. `toYulFn` does **not** return `none` on
calls.

Every runtime entry checks `tload(0)` and reverts if set. Locking functions
(`¬reentrant ∧ hasExtCall ∧ ¬ isPureRead`) `tstore(0,1)` on entry and
`tstore(0,0)` on committing exits. `[Reentrant]` skips acquire/release.
Not emitted: `for`, `delegatecall`, `selfdestruct`, `create`.
`ite` is `switch` (Yul `if` has no else). Dispatcher is
`switch shr(224, calldataload(0))`. Sub-expressions are nested Yul builtins
(no flatten / `t_i` temps); `{ … }` wraps `if` bodies, `switch` cases, and
external-call temps. `toYulFn` requires `coreWF` and `Nodup` `identV` names
(`{f.name}_{i}`, unique across the dispatcher `switch`); `runtimeBlock`
requires unique selectors.

Definitions are in `YulDefs`; well-formedness and `noExt*` lemmas in
`YulTheorems`.
-/
