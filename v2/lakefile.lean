import Lake
open Lake DSL

package lscV2 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

require evmyul from git
  "https://github.com/prevostc/EVMYulLean.git" @ "65124bfc495bd253dc8a615bb55d9cc7e432efa9"

require KeccakEngine from git
  "https://github.com/prevostc/lean-keccak-unrolled" @ "main"

lean_lib LscV2 where
  globs := #[Glob.submodules `LscV2]

lean_exe «BytecodeExecSmoke» where
  root := `LscV2.Compile.BytecodeExecTestMain
  supportInterpreter := true
