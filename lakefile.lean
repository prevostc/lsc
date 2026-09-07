import Lake
open Lake DSL

package lsc where
  version := v!"0.2.0"

-- Toolchain and Mathlib pin follow powdr's yul-compiler (see docs/internals/LANGUAGE_ARCHITECTURE.md).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

-- Yul source semantics: the big-step judgment `toYul_correct` is proved against.
require «yul-semantics» from git
  "https://github.com/powdr-labs/yul-semantics" @ "c9914c13df47efe026376723acd632bc33bc16e3"

-- EVM ground truth (conformance-tested) and the verified Yul → EVM compiler.
require evm_semantics from git
  "https://github.com/powdr-labs/evm-semantics" @ "2f8714d6ba960a3de67720019b54513f5bc1a2e3"

require «yul-evm-compiler» from git
  "https://github.com/prevostc/yul-compiler" @ "30230e1c08d990cf454b62b7c566259de71a1397"

-- Concrete keccak for ABI selectors and executable tests.
require KeccakEngine from git
  "https://github.com/prevostc/lean-keccak-unrolled" @ "main"

lean_lib Lsc where
  -- `Glob.submodules` (not `andSubmodules`) because there is no `Lsc/Lang.lean` etc.
  globs := #[
    Glob.submodules `Lsc.Lang,
    Glob.submodules `Lsc.Security,
    Glob.submodules `Lsc.Compiler,
    Glob.submodules `Lsc.Compiler.Proof,
    Glob.submodules `Lsc.Compiler.Transport,
    Glob.submodules `Lsc.Tools,
    Glob.submodules `Lsc.Util,
    Glob.one `Lsc
  ]

lean_lib Stdlib where
  globs := #[
    Glob.one `Stdlib,
    Glob.submodules `Stdlib
  ]

lean_lib Examples where
  globs := #[
    Glob.submodules `Examples.Counter,
    Glob.submodules `Examples.Token,
    Glob.submodules `Examples.Vault,
    Glob.submodules `Examples.Amm,
    Glob.submodules `Examples.Misc
  ]

/-- Pinned axiom footprint of the certificates and end-to-end theorems (built by `lake build`). -/
lean_lib Checks where
  globs := #[Glob.one `Checks]
