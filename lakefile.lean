import Lake
open Lake DSL

package lsc where
  version := v!"0.2.0"

-- Toolchain and Mathlib pin follow powdr's yul-compiler (see docs/architecture/LANGUAGE_ARCHITECTURE.md).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

-- Yul source semantics: the big-step judgment `toYul_correct` is proved against.
require «yul-semantics» from git
  "https://github.com/powdr-labs/yul-semantics" @ "c9914c13df47efe026376723acd632bc33bc16e3"

-- EVM ground truth (conformance-tested) and the verified Yul → EVM compiler.
require evm_semantics from git
  "https://github.com/powdr-labs/evm-semantics" @ "2f8714d6ba960a3de67720019b54513f5bc1a2e3"

require «yul-evm-compiler» from git
  "https://github.com/powdr-labs/yul-compiler" @ "330923e0be35fc02c6cdb325e737003bb79230a8"

-- Concrete keccak for ABI selectors and executable tests.
require KeccakEngine from git
  "https://github.com/prevostc/lean-keccak-unrolled" @ "main"

lean_lib Lsc where
  -- `Glob.submodules` (not `andSubmodules`) because there is no `Lsc/Lang.lean` etc.
  globs := #[
    Glob.submodules `Lsc.Lang,
    Glob.submodules `Lsc.Stdlib,
    Glob.submodules `Lsc.Security,
    Glob.submodules `Lsc.Compiler,
    Glob.submodules `Lsc.Compiler.Proof,
    Glob.submodules `Lsc.Tools,
    Glob.one `Lsc.Examples.Counter,
    Glob.one `Lsc.Examples.AmountDemo,
    Glob.one `Lsc.Examples.Token,
    Glob.one `Lsc.Examples.TokenProofs,
    Glob.one `Lsc.Examples.TokenSecurity,
    Glob.one `Lsc.Examples.Vault,
    Glob.one `Lsc.Examples.VaultProofs,
    Glob.one `Lsc.Examples.VaultSecurity,
    Glob.one `Lsc
  ]

/-- Pinned axiom footprint of the certificates and end-to-end theorems (built by `lake build`). -/
lean_lib Checks where
  globs := #[Glob.one `Checks]
