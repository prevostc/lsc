import Lsc.Compiler.CorrectnessDefs
import Lsc.Compiler.CorrectnessTheorems

/-!
# `toYulFn_correct` / `runtimeBlock_correct`

Stated against powdr `RunCommitted` (S1, closed `evm`). A Yul `revert` rolls
back storage/logs, matching `Tx`'s `Except.error`. S1 (call-free) is
`toYulFn_correct_callFree` in `Proof/Core.lean`. S2 (`ToYulFnCorrectExt`,
`RuntimeBlockCorrectExt`) lives in `CoreExtSimDefs` / `DispatchExtDefs`.

Layout relations and start-state constructors are in `CorrectnessDefs`;
`mkEvmStateExt` projections in `CorrectnessTheorems`.
-/
