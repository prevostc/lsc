import Lake
open Lake DSL

package lsc where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

require evmyul from git
  "https://github.com/prevostc/EVMYulLean.git" @ "65124bfc495bd253dc8a615bb55d9cc7e432efa9"

require KeccakEngine from git
  "https://github.com/prevostc/lean-keccak-unrolled" @ "main"

lean_lib Lsc where
  globs := #[Glob.submodules `Lsc]

/-- LSC v3 (shallow Lean surface + certified reification), built alongside v2 during the rewrite. -/
lean_lib Lsc3 where
  globs := #[Glob.andSubmodules `Lsc3]

lean_exe «BytecodeExecSmoke» where
  root := `Lsc.Compile.BytecodeExecTestMain
  supportInterpreter := true
